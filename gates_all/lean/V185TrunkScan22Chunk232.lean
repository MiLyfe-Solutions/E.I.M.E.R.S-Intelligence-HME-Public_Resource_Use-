import V185TrunkScan22Chunk231

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2068747 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_2068747 : Nat := 118140960795 + 2068747 * 2 ^ 59
def prefixEnd_2068747 : Nat := 4983230072969 + 3 ^ 40 * 2068747 * 2
def baseEnd_2068747 : Nat := 708174375697948501032341

theorem tailTrace_2068747 : CollatzResearch.WordTrace tailWord_2068747 prefixEnd_2068747 708174375697948501032341 := by
  unfold tailWord_2068747
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453401836290407703956495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50302267890860271802637663 75453401836290407703956495)
  ·
    refine ⟨113180102754435611555934743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75453401836290407703956495 113180102754435611555934743)
    ·
      refine ⟨169770154131653417333902115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113180102754435611555934743 169770154131653417333902115)
      ·
        refine ⟨254655231197480126000853173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169770154131653417333902115 254655231197480126000853173)
        ·
          refine ⟨23873927924763761812579985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254655231197480126000853173 23873927924763761812579985)
          ·
            refine ⟨17905445943572821359434989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23873927924763761812579985 17905445943572821359434989)
            ·
              refine ⟨6714542228839808009788121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17905445943572821359434989 6714542228839808009788121)
              ·
                refine ⟨5035906671629856007341091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6714542228839808009788121 5035906671629856007341091)
                ·
                  refine ⟨7553860007444784011011637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035906671629856007341091 7553860007444784011011637)
                  ·
                    refine ⟨708174375697948501032341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7553860007444784011011637 708174375697948501032341)
                    ·
                      rfl

theorem cell22_2068747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_2068747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068747 prefixEnd_2068747 := by exact prefixLift 2068747
  have htrace : WordTrace (prefixWord ++ tailWord_2068747) baseStart_2068747 baseEnd_2068747 := by
    simpa [prefixWord, tailWord_2068747, baseEnd_2068747] using wordTrace_append hprefix tailTrace_2068747
  have hstable : (prefixWord ++ tailWord_2068747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068747).length < 2 ^ (prefixWord ++ tailWord_2068747).sum := by decide
  have hdescent : baseEnd_2068747 < baseStart_2068747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068794 : List Nat := [3, 1, 1, 1, 4, 3, 3, 6]
def baseStart_2068794 : Nat := 118140960795 + 2068794 * 2 ^ 59
def prefixEnd_2068794 : Nat := 4983230072969 + 3 ^ 40 * 2068794 * 2
def baseEnd_2068794 : Nat := 78687829417606227234133

theorem tailTrace_2068794 : CollatzResearch.WordTrace tailWord_2068794 prefixEnd_2068794 78687829417606227234133 := by
  unfold tailWord_2068794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863779016780033682729359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50303410711413423153944957 18863779016780033682729359)
  ·
    refine ⟨28295668525170050524094039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863779016780033682729359 28295668525170050524094039)
    ·
      refine ⟨42443502787755075786141059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295668525170050524094039 42443502787755075786141059)
      ·
        refine ⟨63665254181632613679211589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42443502787755075786141059 63665254181632613679211589)
        ·
          refine ⟨11937235159056115064852173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63665254181632613679211589 11937235159056115064852173)
          ·
            refine ⟨4476463184646043149319565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11937235159056115064852173 4476463184646043149319565)
            ·
              refine ⟨1678673694242266180994837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4476463184646043149319565 1678673694242266180994837)
              ·
                refine ⟨78687829417606227234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1678673694242266180994837 78687829417606227234133)
                ·
                  rfl

theorem cell22_2068794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_2068794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068794 prefixEnd_2068794 := by exact prefixLift 2068794
  have htrace : WordTrace (prefixWord ++ tailWord_2068794) baseStart_2068794 baseEnd_2068794 := by
    simpa [prefixWord, tailWord_2068794, baseEnd_2068794] using wordTrace_append hprefix tailTrace_2068794
  have hstable : (prefixWord ++ tailWord_2068794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068794).length < 2 ^ (prefixWord ++ tailWord_2068794).sum := by decide
  have hdescent : baseEnd_2068794 < baseStart_2068794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068903 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2068903 : Nat := 118140960795 + 2068903 * 2 ^ 59
def prefixEnd_2068903 : Nat := 4983230072969 + 3 ^ 40 * 2068903 * 2
def baseEnd_2068903 : Nat := 708227777686016094131863

theorem tailTrace_2068903 : CollatzResearch.WordTrace tailWord_2068903 prefixEnd_2068903 708227777686016094131863 := by
  unfold tailWord_2068903
  simp only [CollatzResearch.WordTrace]
  refine ⟨75459091623725246346635363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50306061082483497564423575 75459091623725246346635363)
  ·
    refine ⟨113188637435587869519953045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75459091623725246346635363 113188637435587869519953045)
    ·
      refine ⟨5305717379793181383747799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113188637435587869519953045 5305717379793181383747799)
      ·
        refine ⟨7958576069689772075621699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305717379793181383747799 7958576069689772075621699)
        ·
          refine ⟨11937864104534658113432549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958576069689772075621699 11937864104534658113432549)
          ·
            refine ⟨2238349519600248396268603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11937864104534658113432549 2238349519600248396268603)
            ·
              refine ⟨3357524279400372594402905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238349519600248396268603 3357524279400372594402905)
              ·
                refine ⟨2518143209550279445802179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357524279400372594402905 2518143209550279445802179)
                ·
                  refine ⟨3777214814325419168703269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518143209550279445802179 3777214814325419168703269)
                  ·
                    refine ⟨708227777686016094131863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777214814325419168703269 708227777686016094131863)
                    ·
                      rfl

theorem cell22_2068903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2068903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068903 prefixEnd_2068903 := by exact prefixLift 2068903
  have htrace : WordTrace (prefixWord ++ tailWord_2068903) baseStart_2068903 baseEnd_2068903 := by
    simpa [prefixWord, tailWord_2068903, baseEnd_2068903] using wordTrace_append hprefix tailTrace_2068903
  have hstable : (prefixWord ++ tailWord_2068903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068903).length < 2 ^ (prefixWord ++ tailWord_2068903).sum := by decide
  have hdescent : baseEnd_2068903 < baseStart_2068903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068961 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_2068961 : Nat := 118140960795 + 2068961 * 2 ^ 59
def prefixEnd_2068961 : Nat := 4983230072969 + 3 ^ 40 * 2068961 * 2
def baseEnd_2068961 : Nat := 708247632271323276181685

theorem tailTrace_2068961 : CollatzResearch.WordTrace tailWord_2068961 prefixEnd_2068961 708247632271323276181685 := by
  unfold tailWord_2068961
  simp only [CollatzResearch.WordTrace]
  refine ⟨75461207057515122252246737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50307471371676748168164491 75461207057515122252246737)
  ·
    refine ⟨56595905293136341689185053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75461207057515122252246737 56595905293136341689185053)
    ·
      refine ⟨21223464484926128133444395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56595905293136341689185053 21223464484926128133444395)
      ·
        refine ⟨31835196727389192200166593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223464484926128133444395 31835196727389192200166593)
        ·
          refine ⟨23876397545541894150124945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31835196727389192200166593 23876397545541894150124945)
          ·
            refine ⟨17907298159156420612593709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23876397545541894150124945 17907298159156420612593709)
            ·
              refine ⟨6715236809683657729722641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17907298159156420612593709 6715236809683657729722641)
              ·
                refine ⟨5036427607262743297291981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715236809683657729722641 5036427607262743297291981)
                ·
                  refine ⟨1888660352723528736484493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5036427607262743297291981 1888660352723528736484493)
                  ·
                    refine ⟨708247632271323276181685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888660352723528736484493 708247632271323276181685)
                    ·
                      rfl

theorem cell22_2068961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_2068961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068961 prefixEnd_2068961 := by exact prefixLift 2068961
  have htrace : WordTrace (prefixWord ++ tailWord_2068961) baseStart_2068961 baseEnd_2068961 := by
    simpa [prefixWord, tailWord_2068961, baseEnd_2068961] using wordTrace_append hprefix tailTrace_2068961
  have hstable : (prefixWord ++ tailWord_2068961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068961).length < 2 ^ (prefixWord ++ tailWord_2068961).sum := by decide
  have hdescent : baseEnd_2068961 < baseStart_2068961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068965 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_2068965 : Nat := 118140960795 + 2068965 * 2 ^ 59
def prefixEnd_2068965 : Nat := 4983230072969 + 3 ^ 40 * 2068965 * 2
def baseEnd_2068965 : Nat := 708249001553068599081673

theorem tailTrace_2068965 : CollatzResearch.WordTrace tailWord_2068965 prefixEnd_2068965 708249001553068599081673 := by
  unfold tailWord_2068965
  simp only [CollatzResearch.WordTrace]
  refine ⟨75461352949500630935392349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50307568633000420623594899 75461352949500630935392349)
  ·
    refine ⟨28298007356062736600772131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75461352949500630935392349 28298007356062736600772131)
    ·
      refine ⟨42447011034094104901158197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28298007356062736600772131 42447011034094104901158197)
      ·
        refine ⟨3979407284446322334483581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42447011034094104901158197 3979407284446322334483581)
        ·
          refine ⟨1492277731667370875431343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3979407284446322334483581 1492277731667370875431343)
          ·
            refine ⟨2238416597501056313147015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492277731667370875431343 2238416597501056313147015)
            ·
              refine ⟨3357624896251584469720523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238416597501056313147015 3357624896251584469720523)
              ·
                refine ⟨5036437344377376704580785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357624896251584469720523 5036437344377376704580785)
                ·
                  refine ⟨3777328008283032528435589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036437344377376704580785 3777328008283032528435589)
                  ·
                    refine ⟨708249001553068599081673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777328008283032528435589 708249001553068599081673)
                    ·
                      rfl

theorem cell22_2068965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_2068965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068965 prefixEnd_2068965 := by exact prefixLift 2068965
  have htrace : WordTrace (prefixWord ++ tailWord_2068965) baseStart_2068965 baseEnd_2068965 := by
    simpa [prefixWord, tailWord_2068965, baseEnd_2068965] using wordTrace_append hprefix tailTrace_2068965
  have hstable : (prefixWord ++ tailWord_2068965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068965).length < 2 ^ (prefixWord ++ tailWord_2068965).sum := by decide
  have hdescent : baseEnd_2068965 < baseStart_2068965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068989 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2068989 : Nat := 118140960795 + 2068989 * 2 ^ 59
def prefixEnd_2068989 : Nat := 4983230072969 + 3 ^ 40 * 2068989 * 2
def baseEnd_2068989 : Nat := 708257217243540536481599

theorem tailTrace_2068989 : CollatzResearch.WordTrace tailWord_2068989 prefixEnd_2068989 708257217243540536481599 := by
  unfold tailWord_2068989
  simp only [CollatzResearch.WordTrace]
  refine ⟨75462228301413683034266021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50308152200942455356177347 75462228301413683034266021)
  ·
    refine ⟨14149167806515065568924879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75462228301413683034266021 14149167806515065568924879)
    ·
      refine ⟨21223751709772598353387319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149167806515065568924879 21223751709772598353387319)
      ·
        refine ⟨31835627564658897530080979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223751709772598353387319 31835627564658897530080979)
        ·
          refine ⟨47753441346988346295121469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31835627564658897530080979 47753441346988346295121469)
          ·
            refine ⟨17907540505120629860670551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47753441346988346295121469 17907540505120629860670551)
            ·
              refine ⟨26861310757680944791005827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907540505120629860670551 26861310757680944791005827)
              ·
                refine ⟨40291966136521417186508741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861310757680944791005827 40291966136521417186508741)
                ·
                  refine ⟨7554743650597765722470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40291966136521417186508741 7554743650597765722470389)
                  ·
                    refine ⟨708257217243540536481599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7554743650597765722470389 708257217243540536481599)
                    ·
                      rfl

theorem cell22_2068989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2068989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068989 prefixEnd_2068989 := by exact prefixLift 2068989
  have htrace : WordTrace (prefixWord ++ tailWord_2068989) baseStart_2068989 baseEnd_2068989 := by
    simpa [prefixWord, tailWord_2068989, baseEnd_2068989] using wordTrace_append hprefix tailTrace_2068989
  have hstable : (prefixWord ++ tailWord_2068989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068989).length < 2 ^ (prefixWord ++ tailWord_2068989).sum := by decide
  have hdescent : baseEnd_2068989 < baseStart_2068989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069006 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2069006 : Nat := 118140960795 + 2069006 * 2 ^ 59
def prefixEnd_2069006 : Nat := 4983230072969 + 3 ^ 40 * 2069006 * 2
def baseEnd_2069006 : Nat := 708263036690958158806547

theorem tailTrace_2069006 : CollatzResearch.WordTrace tailWord_2069006 prefixEnd_2069006 708263036690958158806547 := by
  unfold tailWord_2069006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432856042794011867204359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50308565561568063291756581 9432856042794011867204359)
  ·
    refine ⟨14149284064191017800806539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432856042794011867204359 14149284064191017800806539)
    ·
      refine ⟨21223926096286526701209809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149284064191017800806539 21223926096286526701209809)
      ·
        refine ⟨15917944572214895025907357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21223926096286526701209809 15917944572214895025907357)
        ·
          refine ⟨5969229214580585634715259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15917944572214895025907357 5969229214580585634715259)
          ·
            refine ⟨8953843821870878452072889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969229214580585634715259 8953843821870878452072889)
            ·
              refine ⟨6715382866403158839054667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953843821870878452072889 6715382866403158839054667)
              ·
                refine ⟨10073074299604738258582001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715382866403158839054667 10073074299604738258582001)
                ·
                  refine ⟨7554805724703553693936501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073074299604738258582001 7554805724703553693936501)
                  ·
                    refine ⟨708263036690958158806547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7554805724703553693936501 708263036690958158806547)
                    ·
                      rfl

theorem cell22_2069006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2069006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069006 prefixEnd_2069006 := by exact prefixLift 2069006
  have htrace : WordTrace (prefixWord ++ tailWord_2069006) baseStart_2069006 baseEnd_2069006 := by
    simpa [prefixWord, tailWord_2069006, baseEnd_2069006] using wordTrace_append hprefix tailTrace_2069006
  have hstable : (prefixWord ++ tailWord_2069006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069006).length < 2 ^ (prefixWord ++ tailWord_2069006).sum := by decide
  have hdescent : baseEnd_2069006 < baseStart_2069006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069053 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 6]
def baseStart_2069053 : Nat := 118140960795 + 2069053 * 2 ^ 59
def prefixEnd_2069053 : Nat := 4983230072969 + 3 ^ 40 * 2069053 * 2
def baseEnd_2069053 : Nat := 236093041917155234293801

theorem tailTrace_2069053 : CollatzResearch.WordTrace tailWord_2069053 prefixEnd_2069053 236093041917155234293801 := by
  unfold tailWord_2069053
  simp only [CollatzResearch.WordTrace]
  refine ⟨75464562573181821964595813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50309708382121214643063875 75464562573181821964595813)
  ·
    refine ⟨14149605482471591618361715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75464562573181821964595813 14149605482471591618361715)
    ·
      refine ⟨21224408223707387427542573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149605482471591618361715 21224408223707387427542573)
      ·
        refine ⟨7959153083890270285328465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21224408223707387427542573 7959153083890270285328465)
        ·
          refine ⟨5969364812917702713996349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7959153083890270285328465 5969364812917702713996349)
          ·
            refine ⟨2238511804844138517748631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5969364812917702713996349 2238511804844138517748631)
            ·
              refine ⟨3357767707266207776622947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238511804844138517748631 3357767707266207776622947)
              ·
                refine ⟨5036651560899311664934421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357767707266207776622947 5036651560899311664934421)
                ·
                  refine ⟨236093041917155234293801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036651560899311664934421 236093041917155234293801)
                  ·
                    rfl

theorem cell22_2069053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_2069053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069053 prefixEnd_2069053 := by exact prefixLift 2069053
  have htrace : WordTrace (prefixWord ++ tailWord_2069053) baseStart_2069053 baseEnd_2069053 := by
    simpa [prefixWord, tailWord_2069053, baseEnd_2069053] using wordTrace_append hprefix tailTrace_2069053
  have hstable : (prefixWord ++ tailWord_2069053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069053).length < 2 ^ (prefixWord ++ tailWord_2069053).sum := by decide
  have hdescent : baseEnd_2069053 < baseStart_2069053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069068 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_2069068 : Nat := 118140960795 + 2069068 * 2 ^ 59
def prefixEnd_2069068 : Nat := 4983230072969 + 3 ^ 40 * 2069068 * 2
def baseEnd_2069068 : Nat := 708284260558010663756357

theorem tailTrace_2069068 : CollatzResearch.WordTrace tailWord_2069068 prefixEnd_2069068 708284260558010663756357 := by
  unfold tailWord_2069068
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732554834063739763195929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50310073112084986350927905 37732554834063739763195929)
  ·
    refine ⟨28299416125547804822396947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37732554834063739763195929 28299416125547804822396947)
    ·
      refine ⟨42449124188321707233595421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28299416125547804822396947 42449124188321707233595421)
      ·
        refine ⟨15918421570620640212598283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42449124188321707233595421 15918421570620640212598283)
        ·
          refine ⟨23877632355930960318897425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918421570620640212598283 23877632355930960318897425)
          ·
            refine ⟨17908224266948220239173069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877632355930960318897425 17908224266948220239173069)
            ·
              refine ⟨6715584100105582589689901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17908224266948220239173069 6715584100105582589689901)
              ·
                refine ⟨2518344037539593471133713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6715584100105582589689901 2518344037539593471133713)
                ·
                  refine ⟨1888758028154695103350285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518344037539593471133713 1888758028154695103350285)
                  ·
                    refine ⟨708284260558010663756357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888758028154695103350285 708284260558010663756357)
                    ·
                      rfl

theorem cell22_2069068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_2069068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069068 prefixEnd_2069068 := by exact prefixLift 2069068
  have htrace : WordTrace (prefixWord ++ tailWord_2069068) baseStart_2069068 baseEnd_2069068 := by
    simpa [prefixWord, tailWord_2069068, baseEnd_2069068] using wordTrace_append hprefix tailTrace_2069068
  have hstable : (prefixWord ++ tailWord_2069068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069068).length < 2 ^ (prefixWord ++ tailWord_2069068).sum := by decide
  have hdescent : baseEnd_2069068 < baseStart_2069068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069130 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_2069130 : Nat := 118140960795 + 2069130 * 2 ^ 59
def prefixEnd_2069130 : Nat := 4983230072969 + 3 ^ 40 * 2069130 * 2
def baseEnd_2069130 : Nat := 708305484425063168706167

theorem tailTrace_2069130 : CollatzResearch.WordTrace tailWord_2069130 prefixEnd_2069130 708305484425063168706167 := by
  unfold tailWord_2069130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18866842748475716028787211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50311580662601909410099229 18866842748475716028787211)
  ·
    refine ⟨28300264122713574043180817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18866842748475716028787211 28300264122713574043180817)
    ·
      refine ⟨21225198092035180532385613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28300264122713574043180817 21225198092035180532385613)
      ·
        refine ⟨7959449284513192699644605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21225198092035180532385613 7959449284513192699644605)
        ·
          refine ⟨2984793481692447262366727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7959449284513192699644605 2984793481692447262366727)
          ·
            refine ⟨4477190222538670893550091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984793481692447262366727 4477190222538670893550091)
            ·
              refine ⟨6715785333808006340325137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477190222538670893550091 6715785333808006340325137)
              ·
                refine ⟨5036839000356004755243853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715785333808006340325137 5036839000356004755243853)
                ·
                  refine ⟨1888814625133501783216445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5036839000356004755243853 1888814625133501783216445)
                  ·
                    refine ⟨708305484425063168706167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888814625133501783216445 708305484425063168706167)
                    ·
                      rfl

theorem cell22_2069130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_2069130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069130 prefixEnd_2069130 := by exact prefixLift 2069130
  have htrace : WordTrace (prefixWord ++ tailWord_2069130) baseStart_2069130 baseEnd_2069130 := by
    simpa [prefixWord, tailWord_2069130, baseEnd_2069130] using wordTrace_append hprefix tailTrace_2069130
  have hstable : (prefixWord ++ tailWord_2069130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069130).length < 2 ^ (prefixWord ++ tailWord_2069130).sum := by decide
  have hdescent : baseEnd_2069130 < baseStart_2069130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069171 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 6]
def baseStart_2069171 : Nat := 118140960795 + 2069171 * 2 ^ 59
def prefixEnd_2069171 : Nat := 4983230072969 + 3 ^ 40 * 2069171 * 2
def baseEnd_2069171 : Nat := 236106506520984242810347

theorem tailTrace_2069171 : CollatzResearch.WordTrace tailWord_2069171 prefixEnd_2069171 236106506520984242810347 := by
  unfold tailWord_2069171
  simp only [CollatzResearch.WordTrace]
  refine ⟨75468866386754328117391367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50312577591169552078260911 75468866386754328117391367)
  ·
    refine ⟨113203299580131492176087051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75468866386754328117391367 113203299580131492176087051)
    ·
      refine ⟨169804949370197238264130577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113203299580131492176087051 169804949370197238264130577)
      ·
        refine ⟨127353712027647928698097933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169804949370197238264130577 127353712027647928698097933)
        ·
          refine ⟨47757642010367973261786725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127353712027647928698097933 47757642010367973261786725)
          ·
            refine ⟨8954557876943994986585011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47757642010367973261786725 8954557876943994986585011)
            ·
              refine ⟨13431836815415992479877517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954557876943994986585011 13431836815415992479877517)
              ·
                refine ⟨5036938805780997179954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13431836815415992479877517 5036938805780997179954069)
                ·
                  refine ⟨236106506520984242810347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036938805780997179954069 236106506520984242810347)
                  ·
                    rfl

theorem cell22_2069171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_2069171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069171 prefixEnd_2069171 := by exact prefixLift 2069171
  have htrace : WordTrace (prefixWord ++ tailWord_2069171) baseStart_2069171 baseEnd_2069171 := by
    simpa [prefixWord, tailWord_2069171, baseEnd_2069171] using wordTrace_append hprefix tailTrace_2069171
  have hstable : (prefixWord ++ tailWord_2069171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069171).length < 2 ^ (prefixWord ++ tailWord_2069171).sum := by decide
  have hdescent : baseEnd_2069171 < baseStart_2069171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069188 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_2069188 : Nat := 118140960795 + 2069188 * 2 ^ 59
def prefixEnd_2069188 : Nat := 4983230072969 + 3 ^ 40 * 2069188 * 2
def baseEnd_2069188 : Nat := 236108446336790116918663

theorem tailTrace_2069188 : CollatzResearch.WordTrace tailWord_2069188 prefixEnd_2069188 236108446336790116918663 := by
  unfold tailWord_2069188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37734743213846370010380109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50312990951795160013840145 37734743213846370010380109)
  ·
    refine ⟨14150528705192388753892541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37734743213846370010380109 14150528705192388753892541)
    ·
      refine ⟨5306448264447145782709703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14150528705192388753892541 5306448264447145782709703)
      ·
        refine ⟨7959672396670718674064555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306448264447145782709703 7959672396670718674064555)
        ·
          refine ⟨11939508595006078011096833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959672396670718674064555 11939508595006078011096833)
          ·
            refine ⟨8954631446254558508322625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11939508595006078011096833 8954631446254558508322625)
            ·
              refine ⟨6715973584690918881241969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8954631446254558508322625 6715973584690918881241969)
              ·
                refine ⟨5036980188518189160931477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715973584690918881241969 5036980188518189160931477)
                ·
                  refine ⟨236108446336790116918663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036980188518189160931477 236108446336790116918663)
                  ·
                    rfl

theorem cell22_2069188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_2069188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069188 prefixEnd_2069188 := by exact prefixLift 2069188
  have htrace : WordTrace (prefixWord ++ tailWord_2069188) baseStart_2069188 baseEnd_2069188 := by
    simpa [prefixWord, tailWord_2069188, baseEnd_2069188] using wordTrace_append hprefix tailTrace_2069188
  have hstable : (prefixWord ++ tailWord_2069188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069188).length < 2 ^ (prefixWord ++ tailWord_2069188).sum := by decide
  have hdescent : baseEnd_2069188 < baseStart_2069188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069201 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2069201 : Nat := 118140960795 + 2069201 * 2 ^ 59
def prefixEnd_2069201 : Nat := 4983230072969 + 3 ^ 40 * 2069201 * 2
def baseEnd_2069201 : Nat := 708329789176042650180949

theorem tailTrace_2069201 : CollatzResearch.WordTrace tailWord_2069201 prefixEnd_2069201 708329789176042650180949 := by
  unfold tailWord_2069201
  simp only [CollatzResearch.WordTrace]
  refine ⟨75469960576645643240983457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50313307051097095493988971 75469960576645643240983457)
  ·
    refine ⟨56602470432484232430737593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75469960576645643240983457 56602470432484232430737593)
    ·
      refine ⟨42451852824363174323053195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56602470432484232430737593 42451852824363174323053195)
      ·
        refine ⟨63677779236544761484579793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42451852824363174323053195 63677779236544761484579793)
        ·
          refine ⟨47758334427408571113434845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63677779236544761484579793 47758334427408571113434845)
          ·
            refine ⟨17909375410278214167538067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47758334427408571113434845 17909375410278214167538067)
            ·
              refine ⟨26864063115417321251307101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17909375410278214167538067 26864063115417321251307101)
              ·
                refine ⟨10074023668281495469240163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26864063115417321251307101 10074023668281495469240163)
                ·
                  refine ⟨15111035502422243203860245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10074023668281495469240163 15111035502422243203860245)
                  ·
                    refine ⟨708329789176042650180949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15111035502422243203860245 708329789176042650180949)
                    ·
                      rfl

theorem cell22_2069201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2069201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069201 prefixEnd_2069201 := by exact prefixLift 2069201
  have htrace : WordTrace (prefixWord ++ tailWord_2069201) baseStart_2069201 baseEnd_2069201 := by
    simpa [prefixWord, tailWord_2069201, baseEnd_2069201] using wordTrace_append hprefix tailTrace_2069201
  have hstable : (prefixWord ++ tailWord_2069201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069201).length < 2 ^ (prefixWord ++ tailWord_2069201).sum := by decide
  have hdescent : baseEnd_2069201 < baseStart_2069201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_2069291 : Nat := 118140960795 + 2069291 * 2 ^ 59
def prefixEnd_2069291 : Nat := 4983230072969 + 3 ^ 40 * 2069291 * 2
def baseEnd_2069291 : Nat := 708360598015312415430673

theorem tailTrace_2069291 : CollatzResearch.WordTrace tailWord_2069291 prefixEnd_2069291 708360598015312415430673 := by
  unfold tailWord_2069291
  simp only [CollatzResearch.WordTrace]
  refine ⟨75473243146319588611759727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50315495430879725741173151 75473243146319588611759727)
  ·
    refine ⟨113209864719479382917639591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75473243146319588611759727 113209864719479382917639591)
    ·
      refine ⟨169814797079219074376459387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113209864719479382917639591 169814797079219074376459387)
      ·
        refine ⟨254722195618828611564689081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169814797079219074376459387 254722195618828611564689081)
        ·
          refine ⟨191041646714121458673516811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254722195618828611564689081 191041646714121458673516811)
          ·
            refine ⟨286562470071182188010275217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191041646714121458673516811 286562470071182188010275217)
            ·
              refine ⟨214921852553386641007706413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286562470071182188010275217 214921852553386641007706413)
              ·
                refine ⟨80595694707519990377889905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214921852553386641007706413 80595694707519990377889905)
                ·
                  refine ⟨60446771030639992783417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80595694707519990377889905 60446771030639992783417429)
                  ·
                    refine ⟨708360598015312415430673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60446771030639992783417429 708360598015312415430673)
                    ·
                      rfl

theorem cell22_2069291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_2069291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069291 prefixEnd_2069291 := by exact prefixLift 2069291
  have htrace : WordTrace (prefixWord ++ tailWord_2069291) baseStart_2069291 baseEnd_2069291 := by
    simpa [prefixWord, tailWord_2069291, baseEnd_2069291] using wordTrace_append hprefix tailTrace_2069291
  have hstable : (prefixWord ++ tailWord_2069291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069291).length < 2 ^ (prefixWord ++ tailWord_2069291).sum := by decide
  have hdescent : baseEnd_2069291 < baseStart_2069291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069340 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_2069340 : Nat := 118140960795 + 2069340 * 2 ^ 59
def prefixEnd_2069340 : Nat := 4983230072969 + 3 ^ 40 * 2069340 * 2
def baseEnd_2069340 : Nat := 236125790572230873651841

theorem tailTrace_2069340 : CollatzResearch.WordTrace tailWord_2069340 prefixEnd_2069340 236125790572230873651841 := by
  unfold tailWord_2069340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737515161571034990146737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50316686882094713320195649 37737515161571034990146737)
  ·
    refine ⟨28303136371178276242610053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37737515161571034990146737 28303136371178276242610053)
    ·
      refine ⟨5306838069595926795489385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28303136371178276242610053 5306838069595926795489385)
      ·
        refine ⟨3980128552196945096617039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5306838069595926795489385 3980128552196945096617039)
        ·
          refine ⟨5970192828295417644925559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980128552196945096617039 5970192828295417644925559)
          ·
            refine ⟨8955289242443126467388339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970192828295417644925559 8955289242443126467388339)
            ·
              refine ⟨13432933863664689701082509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955289242443126467388339 13432933863664689701082509)
              ·
                refine ⟨5037350198874258637905941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432933863664689701082509 5037350198874258637905941)
                ·
                  refine ⟨236125790572230873651841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5037350198874258637905941 236125790572230873651841)
                  ·
                    rfl

theorem cell22_2069340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_2069340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069340 prefixEnd_2069340 := by exact prefixLift 2069340
  have htrace : WordTrace (prefixWord ++ tailWord_2069340) baseStart_2069340 baseEnd_2069340 := by
    simpa [prefixWord, tailWord_2069340, baseEnd_2069340] using wordTrace_append hprefix tailTrace_2069340
  have hstable : (prefixWord ++ tailWord_2069340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069340).length < 2 ^ (prefixWord ++ tailWord_2069340).sum := by decide
  have hdescent : baseEnd_2069340 < baseStart_2069340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069355 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 2, 3]
def baseStart_2069355 : Nat := 118140960795 + 2069355 * 2 ^ 59
def prefixEnd_2069355 : Nat := 4983230072969 + 3 ^ 40 * 2069355 * 2
def baseEnd_2069355 : Nat := 708382506523237581830477

theorem tailTrace_2069355 : CollatzResearch.WordTrace tailWord_2069355 prefixEnd_2069355 708382506523237581830477 := by
  unfold tailWord_2069355
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475577418087727542089519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50317051612058485028059679 75475577418087727542089519)
  ·
    refine ⟨113213366127131591313134279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75475577418087727542089519 113213366127131591313134279)
    ·
      refine ⟨169820049190697386969701419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113213366127131591313134279 169820049190697386969701419)
      ·
        refine ⟨254730073786046080454552129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169820049190697386969701419 254730073786046080454552129)
        ·
          refine ⟨191047555339534560340914097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254730073786046080454552129 191047555339534560340914097)
          ·
            refine ⟨143285666504650920255685573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191047555339534560340914097 143285666504650920255685573)
            ·
              refine ⟨26866062469622047547941045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143285666504650920255685573 26866062469622047547941045)
              ·
                refine ⟨2518693356527066957619473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26866062469622047547941045 2518693356527066957619473)
                ·
                  refine ⟨1889020017395300218214605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518693356527066957619473 1889020017395300218214605)
                  ·
                    refine ⟨708382506523237581830477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889020017395300218214605 708382506523237581830477)
                    ·
                      rfl

theorem cell22_2069355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].length) (baseStart_2069355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069355 prefixEnd_2069355 := by exact prefixLift 2069355
  have htrace : WordTrace (prefixWord ++ tailWord_2069355) baseStart_2069355 baseEnd_2069355 := by
    simpa [prefixWord, tailWord_2069355, baseEnd_2069355] using wordTrace_append hprefix tailTrace_2069355
  have hstable : (prefixWord ++ tailWord_2069355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069355).length < 2 ^ (prefixWord ++ tailWord_2069355).sum := by decide
  have hdescent : baseEnd_2069355 < baseStart_2069355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069451 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 1, 3]
def baseStart_2069451 : Nat := 118140960795 + 2069451 * 2 ^ 59
def prefixEnd_2069451 : Nat := 4983230072969 + 3 ^ 40 * 2069451 * 2
def baseEnd_2069451 : Nat := 708415369285125331430183

theorem tailTrace_2069451 : CollatzResearch.WordTrace tailWord_2069451 prefixEnd_2069451 708415369285125331430183 := by
  unfold tailWord_2069451
  simp only [CollatzResearch.WordTrace]
  refine ⟨75479078825739935937584207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50319385883826623958389471 75479078825739935937584207)
  ·
    refine ⟨113218618238609903906376311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75479078825739935937584207 113218618238609903906376311)
    ·
      refine ⟨169827927357914855859564467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113218618238609903906376311 169827927357914855859564467)
      ·
        refine ⟨254741891036872283789346701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169827927357914855859564467 254741891036872283789346701)
        ·
          refine ⟨95528209138827106421005013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254741891036872283789346701 95528209138827106421005013)
          ·
            refine ⟨2238942401691260306742305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95528209138827106421005013 2238942401691260306742305)
            ·
              refine ⟨1679206801268445230056729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238942401691260306742305 1679206801268445230056729)
              ·
                refine ⟨1259405100951333922542547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679206801268445230056729 1259405100951333922542547)
                ·
                  refine ⟨1889107651427000883813821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259405100951333922542547 1889107651427000883813821)
                  ·
                    refine ⟨708415369285125331430183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889107651427000883813821 708415369285125331430183)
                    ·
                      rfl

theorem cell22_2069451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 3].length) (baseStart_2069451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069451 prefixEnd_2069451 := by exact prefixLift 2069451
  have htrace : WordTrace (prefixWord ++ tailWord_2069451) baseStart_2069451 baseEnd_2069451 := by
    simpa [prefixWord, tailWord_2069451, baseEnd_2069451] using wordTrace_append hprefix tailTrace_2069451
  have hstable : (prefixWord ++ tailWord_2069451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069451).length < 2 ^ (prefixWord ++ tailWord_2069451).sum := by decide
  have hdescent : baseEnd_2069451 < baseStart_2069451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069453 : List Nat := [1, 6, 3, 1, 2, 1, 1, 7]
def baseStart_2069453 : Nat := 118140960795 + 2069453 * 2 ^ 59
def prefixEnd_2069453 : Nat := 4983230072969 + 3 ^ 40 * 2069453 * 2
def baseEnd_2069453 : Nat := 78712894880666443653353

theorem tailTrace_2069453 : CollatzResearch.WordTrace tailWord_2069453 prefixEnd_2069453 78712894880666443653353 := by
  unfold tailWord_2069453
  simp only [CollatzResearch.WordTrace]
  refine ⟨75479151771732690279157013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50319434514488460186104675 75479151771732690279157013)
  ·
    refine ⟨3538085239299969856835485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75479151771732690279157013 3538085239299969856835485)
    ·
      refine ⟨1326781964737488696313307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3538085239299969856835485 1326781964737488696313307)
      ·
        refine ⟨1990172947106233044469961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326781964737488696313307 1990172947106233044469961)
        ·
          refine ⟨1492629710329674783352471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990172947106233044469961 1492629710329674783352471)
          ·
            refine ⟨2238944565494512175028707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492629710329674783352471 2238944565494512175028707)
            ·
              refine ⟨3358416848241768262543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238944565494512175028707 3358416848241768262543061)
              ·
                refine ⟨78712894880666443653353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3358416848241768262543061 78712894880666443653353)
                ·
                  rfl

theorem cell22_2069453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 7].length) (baseStart_2069453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069453 prefixEnd_2069453 := by exact prefixLift 2069453
  have htrace : WordTrace (prefixWord ++ tailWord_2069453) baseStart_2069453 baseEnd_2069453 := by
    simpa [prefixWord, tailWord_2069453, baseEnd_2069453] using wordTrace_append hprefix tailTrace_2069453
  have hstable : (prefixWord ++ tailWord_2069453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069453).length < 2 ^ (prefixWord ++ tailWord_2069453).sum := by decide
  have hdescent : baseEnd_2069453 < baseStart_2069453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069462 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2069462 : Nat := 118140960795 + 2069462 * 2 ^ 59
def prefixEnd_2069462 : Nat := 4983230072969 + 3 ^ 40 * 2069462 * 2
def baseEnd_2069462 : Nat := 708419134809924969405149

theorem tailTrace_2069462 : CollatzResearch.WordTrace tailWord_2069462 prefixEnd_2069462 708419134809924969405149 := by
  unfold tailWord_2069462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717467501793755301014665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50319653352466723210823093 4717467501793755301014665)
  ·
    refine ⟨3538100626345316475760999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4717467501793755301014665 3538100626345316475760999)
    ·
      refine ⟨5307150939517974713641499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538100626345316475760999 5307150939517974713641499)
      ·
        refine ⟨7960726409276962070462249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307150939517974713641499 7960726409276962070462249)
        ·
          refine ⟨5970544806957721552846687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7960726409276962070462249 5970544806957721552846687)
          ·
            refine ⟨8955817210436582329270031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970544806957721552846687 8955817210436582329270031)
            ·
              refine ⟨13433725815654873493905047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955817210436582329270031 13433725815654873493905047)
              ·
                refine ⟨20150588723482310240857571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433725815654873493905047 20150588723482310240857571)
                ·
                  refine ⟨30225883085223465361286357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20150588723482310240857571 30225883085223465361286357)
                  ·
                    refine ⟨708419134809924969405149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30225883085223465361286357 708419134809924969405149)
                    ·
                      rfl

theorem cell22_2069462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2069462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069462 prefixEnd_2069462 := by exact prefixLift 2069462
  have htrace : WordTrace (prefixWord ++ tailWord_2069462) baseStart_2069462 baseEnd_2069462 := by
    simpa [prefixWord, tailWord_2069462, baseEnd_2069462] using wordTrace_append hprefix tailTrace_2069462
  have hstable : (prefixWord ++ tailWord_2069462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069462).length < 2 ^ (prefixWord ++ tailWord_2069462).sum := by decide
  have hdescent : baseEnd_2069462 < baseStart_2069462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069475 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 6]
def baseStart_2069475 : Nat := 118140960795 + 2069475 * 2 ^ 59
def prefixEnd_2069475 : Nat := 4983230072969 + 3 ^ 40 * 2069475 * 2
def baseEnd_2069475 : Nat := 236141194991865756276703

theorem tailTrace_2069475 : CollatzResearch.WordTrace tailWord_2069475 prefixEnd_2069475 236141194991865756276703 := by
  unfold tailWord_2069475
  simp only [CollatzResearch.WordTrace]
  refine ⟨75479954177652988036457879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50319969451768658690971919 75479954177652988036457879)
  ·
    refine ⟨113219931266479482054686819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75479954177652988036457879 113219931266479482054686819)
    ·
      refine ⟨169829896899719223082030229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113219931266479482054686819 169829896899719223082030229)
      ·
        refine ⟨7960776417174338581970167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169829896899719223082030229 7960776417174338581970167)
        ·
          refine ⟨11941164625761507872955251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960776417174338581970167 11941164625761507872955251)
          ·
            refine ⟨17911746938642261809432877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941164625761507872955251 17911746938642261809432877)
            ·
              refine ⟨6716905101990848178537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17911746938642261809432877 6716905101990848178537329)
              ·
                refine ⟨5037678826493136133902997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716905101990848178537329 5037678826493136133902997)
                ·
                  refine ⟨236141194991865756276703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5037678826493136133902997 236141194991865756276703)
                  ·
                    rfl

theorem cell22_2069475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_2069475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069475 prefixEnd_2069475 := by exact prefixLift 2069475
  have htrace : WordTrace (prefixWord ++ tailWord_2069475) baseStart_2069475 baseEnd_2069475 := by
    simpa [prefixWord, tailWord_2069475, baseEnd_2069475] using wordTrace_append hprefix tailTrace_2069475
  have hstable : (prefixWord ++ tailWord_2069475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069475).length < 2 ^ (prefixWord ++ tailWord_2069475).sum := by decide
  have hdescent : baseEnd_2069475 < baseStart_2069475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069494 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2069494 : Nat := 118140960795 + 2069494 * 2 ^ 59
def prefixEnd_2069494 : Nat := 4983230072969 + 3 ^ 40 * 2069494 * 2
def baseEnd_2069494 : Nat := 708430089063887552605051

theorem tailTrace_2069494 : CollatzResearch.WordTrace tailWord_2069494 prefixEnd_2069494 708430089063887552605051 := by
  unfold tailWord_2069494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717540447786509642587471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50320431443056102854266357 4717540447786509642587471)
  ·
    refine ⟨7076310671679764463881207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717540447786509642587471 7076310671679764463881207)
    ·
      refine ⟨10614466007519646695821811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076310671679764463881207 10614466007519646695821811)
      ·
        refine ⟨15921699011279470043732717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614466007519646695821811 15921699011279470043732717)
        ·
          refine ⟨5970637129229801266399769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15921699011279470043732717 5970637129229801266399769)
          ·
            refine ⟨4477977846922350949799827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5970637129229801266399769 4477977846922350949799827)
            ·
              refine ⟨6716966770383526424699741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477977846922350949799827 6716966770383526424699741)
              ·
                refine ⟨2518862538893822409262403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6716966770383526424699741 2518862538893822409262403)
                ·
                  refine ⟨3778293808340733613893605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518862538893822409262403 3778293808340733613893605)
                  ·
                    refine ⟨708430089063887552605051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778293808340733613893605 708430089063887552605051)
                    ·
                      rfl

theorem cell22_2069494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2069494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069494 prefixEnd_2069494 := by exact prefixLift 2069494
  have htrace : WordTrace (prefixWord ++ tailWord_2069494) baseStart_2069494 baseEnd_2069494 := by
    simpa [prefixWord, tailWord_2069494, baseEnd_2069494] using wordTrace_append hprefix tailTrace_2069494
  have hstable : (prefixWord ++ tailWord_2069494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069494).length < 2 ^ (prefixWord ++ tailWord_2069494).sum := by decide
  have hdescent : baseEnd_2069494 < baseStart_2069494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069537 : List Nat := [1, 2, 3, 2, 3, 1, 4, 6]
def baseStart_2069537 : Nat := 118140960795 + 2069537 * 2 ^ 59
def prefixEnd_2069537 : Nat := 4983230072969 + 3 ^ 40 * 2069537 * 2
def baseEnd_2069537 : Nat := 78716089871405530419991

theorem tailTrace_2069537 : CollatzResearch.WordTrace tailWord_2069537 prefixEnd_2069537 78716089871405530419991 := by
  unfold tailWord_2069537
  simp only [CollatzResearch.WordTrace]
  refine ⟨75482215503428372625214865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50321477002285581750143243 75482215503428372625214865)
  ·
    refine ⟨56611661627571279468911149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75482215503428372625214865 56611661627571279468911149)
    ·
      refine ⟨21229373110339229800841681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56611661627571279468911149 21229373110339229800841681)
      ·
        refine ⟨15922029832754422350631261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21229373110339229800841681 15922029832754422350631261)
        ·
          refine ⟨5970761187282908381486723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15922029832754422350631261 5970761187282908381486723)
          ·
            refine ⟨8956141780924362572230085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970761187282908381486723 8956141780924362572230085)
            ·
              refine ⟨1679276583923317982293141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8956141780924362572230085 1679276583923317982293141)
              ·
                refine ⟨78716089871405530419991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1679276583923317982293141 78716089871405530419991)
                ·
                  rfl

theorem cell22_2069537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 6].length) (baseStart_2069537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069537 prefixEnd_2069537 := by exact prefixLift 2069537
  have htrace : WordTrace (prefixWord ++ tailWord_2069537) baseStart_2069537 baseEnd_2069537 := by
    simpa [prefixWord, tailWord_2069537, baseEnd_2069537] using wordTrace_append hprefix tailTrace_2069537
  have hstable : (prefixWord ++ tailWord_2069537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069537).length < 2 ^ (prefixWord ++ tailWord_2069537).sum := by decide
  have hdescent : baseEnd_2069537 < baseStart_2069537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069580 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_2069580 : Nat := 118140960795 + 2069580 * 2 ^ 59
def prefixEnd_2069580 : Nat := 4983230072969 + 3 ^ 40 * 2069580 * 2
def baseEnd_2069580 : Nat := 708459528621411994954787

theorem tailTrace_2069580 : CollatzResearch.WordTrace tailWord_2069580 prefixEnd_2069580 708459528621411994954787 := by
  unfold tailWord_2069580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37741891921136295484515097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50322522561515060646020129 37741891921136295484515097)
  ·
    refine ⟨28306418940852221613386323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37741891921136295484515097 28306418940852221613386323)
    ·
      refine ⟨42459628411278332420079485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306418940852221613386323 42459628411278332420079485)
      ·
        refine ⟨15922360654229374657529807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42459628411278332420079485 15922360654229374657529807)
        ·
          refine ⟨23883540981344061986294711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922360654229374657529807 23883540981344061986294711)
          ·
            refine ⟨35825311472016092979442067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23883540981344061986294711 35825311472016092979442067)
            ·
              refine ⟨53737967208024139469163101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35825311472016092979442067 53737967208024139469163101)
              ·
                refine ⟨20151737703009052300936163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53737967208024139469163101 20151737703009052300936163)
                ·
                  refine ⟨30227606554513578451404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20151737703009052300936163 30227606554513578451404245)
                  ·
                    refine ⟨708459528621411994954787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30227606554513578451404245 708459528621411994954787)
                    ·
                      rfl

theorem cell22_2069580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_2069580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069580 prefixEnd_2069580 := by exact prefixLift 2069580
  have htrace : WordTrace (prefixWord ++ tailWord_2069580) baseStart_2069580 baseEnd_2069580 := by
    simpa [prefixWord, tailWord_2069580, baseEnd_2069580] using wordTrace_append hprefix tailTrace_2069580
  have hstable : (prefixWord ++ tailWord_2069580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069580).length < 2 ^ (prefixWord ++ tailWord_2069580).sum := by decide
  have hdescent : baseEnd_2069580 < baseStart_2069580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069582 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_2069582 : Nat := 118140960795 + 2069582 * 2 ^ 59
def prefixEnd_2069582 : Nat := 4983230072969 + 3 ^ 40 * 2069582 * 2
def baseEnd_2069582 : Nat := 236153404420761552134927

theorem tailTrace_2069582 : CollatzResearch.WordTrace tailWord_2069582 prefixEnd_2069582 236153404420761552134927 := by
  unfold tailWord_2069582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435482098533168163825375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50322571192176896873735333 9435482098533168163825375)
  ·
    refine ⟨14153223147799752245738063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9435482098533168163825375 14153223147799752245738063)
    ·
      refine ⟨21229834721699628368607095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153223147799752245738063 21229834721699628368607095)
      ·
        refine ⟨31844752082549442552910643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21229834721699628368607095 31844752082549442552910643)
        ·
          refine ⟨47767128123824163829365965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31844752082549442552910643 47767128123824163829365965)
          ·
            refine ⟨17912673046434061436012237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47767128123824163829365965 17912673046434061436012237)
            ·
              refine ⟨6717252392412773038504589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17912673046434061436012237 6717252392412773038504589)
              ·
                refine ⟨2518969647154789889439221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6717252392412773038504589 2518969647154789889439221)
                ·
                  refine ⟨236153404420761552134927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2518969647154789889439221 236153404420761552134927)
                  ·
                    rfl

theorem cell22_2069582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_2069582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069582 prefixEnd_2069582 := by exact prefixLift 2069582
  have htrace : WordTrace (prefixWord ++ tailWord_2069582) baseStart_2069582 baseEnd_2069582 := by
    simpa [prefixWord, tailWord_2069582, baseEnd_2069582] using wordTrace_append hprefix tailTrace_2069582
  have hstable : (prefixWord ++ tailWord_2069582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069582).length < 2 ^ (prefixWord ++ tailWord_2069582).sum := by decide
  have hdescent : baseEnd_2069582 < baseStart_2069582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069663 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 1, 4]
def baseStart_2069663 : Nat := 118140960795 + 2069663 * 2 ^ 59
def prefixEnd_2069663 : Nat := 4983230072969 + 3 ^ 40 * 2069663 * 2
def baseEnd_2069663 : Nat := 708487941217627445129533

theorem tailTrace_2069663 : CollatzResearch.WordTrace tailWord_2069663 prefixEnd_2069663 708487941217627445129533 := by
  unfold tailWord_2069663
  simp only [CollatzResearch.WordTrace]
  refine ⟨75486811100971896144301643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50324540733981264096201095 75486811100971896144301643)
  ·
    refine ⟨113230216651457844216452465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75486811100971896144301643 113230216651457844216452465)
    ·
      refine ⟨84922662488593383162339349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113230216651457844216452465 84922662488593383162339349)
      ·
        refine ⟨3980749804152814835734657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84922662488593383162339349 3980749804152814835734657)
        ·
          refine ⟨2985562353114611126800993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980749804152814835734657 2985562353114611126800993)
          ·
            refine ⟨2239171764835958345100745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2985562353114611126800993 2239171764835958345100745)
            ·
              refine ⟨1679378823626968758825559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239171764835958345100745 1679378823626968758825559)
              ·
                refine ⟨2519068235440453138238339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679378823626968758825559 2519068235440453138238339)
                ·
                  refine ⟨3778602353160679707357509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519068235440453138238339 3778602353160679707357509)
                  ·
                    refine ⟨708487941217627445129533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778602353160679707357509 708487941217627445129533)
                    ·
                      rfl

theorem cell22_2069663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_2069663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069663 prefixEnd_2069663 := by exact prefixLift 2069663
  have htrace : WordTrace (prefixWord ++ tailWord_2069663) baseStart_2069663 baseEnd_2069663 := by
    simpa [prefixWord, tailWord_2069663, baseEnd_2069663] using wordTrace_append hprefix tailTrace_2069663
  have hstable : (prefixWord ++ tailWord_2069663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069663).length < 2 ^ (prefixWord ++ tailWord_2069663).sum := by decide
  have hdescent : baseEnd_2069663 < baseStart_2069663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069704 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_2069704 : Nat := 118140960795 + 2069704 * 2 ^ 59
def prefixEnd_2069704 : Nat := 4983230072969 + 3 ^ 40 * 2069704 * 2
def baseEnd_2069704 : Nat := 708501976355517004854407

theorem tailTrace_2069704 : CollatzResearch.WordTrace tailWord_2069704 prefixEnd_2069704 708501976355517004854407 := by
  unfold tailWord_2069704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37744153246911680073272083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50325537662548906764362777 37744153246911680073272083)
  ·
    refine ⟨56616229870367520109908125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37744153246911680073272083 56616229870367520109908125)
    ·
      refine ⟨21231086201387820041215547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56616229870367520109908125 21231086201387820041215547)
      ·
        refine ⟨31846629302081730061823321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231086201387820041215547 31846629302081730061823321)
        ·
          refine ⟨23884971976561297546367491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31846629302081730061823321 23884971976561297546367491)
          ·
            refine ⟨35827457964841946319551237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23884971976561297546367491 35827457964841946319551237)
            ·
              refine ⟨6717648368407864934915857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35827457964841946319551237 6717648368407864934915857)
              ·
                refine ⟨5038236276305898701186893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717648368407864934915857 5038236276305898701186893)
                ·
                  refine ⟨1889338603614712012945085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5038236276305898701186893 1889338603614712012945085)
                  ·
                    refine ⟨708501976355517004854407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889338603614712012945085 708501976355517004854407)
                    ·
                      rfl

theorem cell22_2069704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_2069704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069704 prefixEnd_2069704 := by exact prefixLift 2069704
  have htrace : WordTrace (prefixWord ++ tailWord_2069704) baseStart_2069704 baseEnd_2069704 := by
    simpa [prefixWord, tailWord_2069704, baseEnd_2069704] using wordTrace_append hprefix tailTrace_2069704
  have hstable : (prefixWord ++ tailWord_2069704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069704).length < 2 ^ (prefixWord ++ tailWord_2069704).sum := by decide
  have hdescent : baseEnd_2069704 < baseStart_2069704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069732 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2069732 : Nat := 118140960795 + 2069732 * 2 ^ 59
def prefixEnd_2069732 : Nat := 4983230072969 + 3 ^ 40 * 2069732 * 2
def baseEnd_2069732 : Nat := 708511561327734265154321

theorem tailTrace_2069732 : CollatzResearch.WordTrace tailWord_2069732 prefixEnd_2069732 708511561327734265154321 := by
  unfold tailWord_2069732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37744663868860960464281725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50326218491814613952375633 37744663868860960464281725)
  ·
    refine ⟨14154248950822860174105647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37744663868860960464281725 14154248950822860174105647)
    ·
      refine ⟨21231373426234290261158471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154248950822860174105647 21231373426234290261158471)
      ·
        refine ⟨31847060139351435391737707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231373426234290261158471 31847060139351435391737707)
        ·
          refine ⟨47770590209027153087606561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847060139351435391737707 47770590209027153087606561)
          ·
            refine ⟨35827942656770364815704921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47770590209027153087606561 35827942656770364815704921)
            ·
              refine ⟨26870956992577773611778691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35827942656770364815704921 26870956992577773611778691)
              ·
                refine ⟨40306435488866660417668037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26870956992577773611778691 40306435488866660417668037)
                ·
                  refine ⟨7557456654162498828312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40306435488866660417668037 7557456654162498828312757)
                  ·
                    refine ⟨708511561327734265154321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7557456654162498828312757 708511561327734265154321)
                    ·
                      rfl

theorem cell22_2069732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2069732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069732 prefixEnd_2069732 := by exact prefixLift 2069732
  have htrace : WordTrace (prefixWord ++ tailWord_2069732) baseStart_2069732 baseEnd_2069732 := by
    simpa [prefixWord, tailWord_2069732, baseEnd_2069732] using wordTrace_append hprefix tailTrace_2069732
  have hstable : (prefixWord ++ tailWord_2069732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069732).length < 2 ^ (prefixWord ++ tailWord_2069732).sum := by decide
  have hdescent : baseEnd_2069732 < baseStart_2069732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069796 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2069796 : Nat := 118140960795 + 2069796 * 2 ^ 59
def prefixEnd_2069796 : Nat := 4983230072969 + 3 ^ 40 * 2069796 * 2
def baseEnd_2069796 : Nat := 236177823278553143851375

theorem tailTrace_2069796 : CollatzResearch.WordTrace tailWord_2069796 prefixEnd_2069796 236177823278553143851375 := by
  unfold tailWord_2069796
  simp only [CollatzResearch.WordTrace]
  refine ⟨37745831004745029929446621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50327774672993373239262161 37745831004745029929446621)
  ·
    refine ⟨14154686626779386223542483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37745831004745029929446621 14154686626779386223542483)
    ·
      refine ⟨21232029940169079335313725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154686626779386223542483 21232029940169079335313725)
      ·
        refine ⟨7962011227563404750742647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21232029940169079335313725 7962011227563404750742647)
        ·
          refine ⟨11943016841345107126113971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962011227563404750742647 11943016841345107126113971)
          ·
            refine ⟨17914525262017660689170957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943016841345107126113971 17914525262017660689170957)
            ·
              refine ⟨6717946973256622758439109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17914525262017660689170957 6717946973256622758439109)
              ·
                refine ⟨1259615057485616767207333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6717946973256622758439109 1259615057485616767207333)
                ·
                  refine ⟨236177823278553143851375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259615057485616767207333 236177823278553143851375)
                  ·
                    rfl

theorem cell22_2069796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2069796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069796 prefixEnd_2069796 := by exact prefixLift 2069796
  have htrace : WordTrace (prefixWord ++ tailWord_2069796) baseStart_2069796 baseEnd_2069796 := by
    simpa [prefixWord, tailWord_2069796, baseEnd_2069796] using wordTrace_append hprefix tailTrace_2069796
  have hstable : (prefixWord ++ tailWord_2069796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069796).length < 2 ^ (prefixWord ++ tailWord_2069796).sum := by decide
  have hdescent : baseEnd_2069796 < baseStart_2069796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069811 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 2, 3]
def baseStart_2069811 : Nat := 118140960795 + 2069811 * 2 ^ 59
def prefixEnd_2069811 : Nat := 4983230072969 + 3 ^ 40 * 2069811 * 2
def baseEnd_2069811 : Nat := 708538604642204392429079

theorem tailTrace_2069811 : CollatzResearch.WordTrace tailWord_2069811 prefixEnd_2069811 708538604642204392429079 := by
  unfold tailWord_2069811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75492209104435717420689287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50328139402957144947126191 75492209104435717420689287)
  ·
    refine ⟨113238313656653576131033931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75492209104435717420689287 113238313656653576131033931)
    ·
      refine ⟨169857470484980364196550897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113238313656653576131033931 169857470484980364196550897)
      ·
        refine ⟨127393102863735273147413173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169857470484980364196550897 127393102863735273147413173)
        ·
          refine ⟨11943103393475181857569985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127393102863735273147413173 11943103393475181857569985)
          ·
            refine ⟨8957327545106386393177489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11943103393475181857569985 8957327545106386393177489)
            ·
              refine ⟨6717995658829789794883117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957327545106386393177489 6717995658829789794883117)
              ·
                refine ⟨2519248372061171173081169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6717995658829789794883117 2519248372061171173081169)
                ·
                  refine ⟨1889436279045878379810877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519248372061171173081169 1889436279045878379810877)
                  ·
                    refine ⟨708538604642204392429079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889436279045878379810877 708538604642204392429079)
                    ·
                      rfl

theorem cell22_2069811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].length) (baseStart_2069811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069811 prefixEnd_2069811 := by exact prefixLift 2069811
  have htrace : WordTrace (prefixWord ++ tailWord_2069811) baseStart_2069811 baseEnd_2069811 := by
    simpa [prefixWord, tailWord_2069811, baseEnd_2069811] using wordTrace_append hprefix tailTrace_2069811
  have hstable : (prefixWord ++ tailWord_2069811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069811).length < 2 ^ (prefixWord ++ tailWord_2069811).sum := by decide
  have hdescent : baseEnd_2069811 < baseStart_2069811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069824 : List Nat := [2, 1, 1, 2, 2, 1, 7, 6]
def baseStart_2069824 : Nat := 118140960795 + 2069824 * 2 ^ 59
def prefixEnd_2069824 : Nat := 4983230072969 + 3 ^ 40 * 2069824 * 2
def baseEnd_2069824 : Nat := 78727006089764076872671

theorem tailTrace_2069824 : CollatzResearch.WordTrace tailWord_2069824 prefixEnd_2069824 78727006089764076872671 := by
  unfold tailWord_2069824
  simp only [CollatzResearch.WordTrace]
  refine ⟨37746341626694310320456263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50328455502259080427275017 37746341626694310320456263)
  ·
    refine ⟨56619512440041465480684395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37746341626694310320456263 56619512440041465480684395)
    ·
      refine ⟨84929268660062198221026593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56619512440041465480684395 84929268660062198221026593)
      ·
        refine ⟨63696951495046648665769945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84929268660062198221026593 63696951495046648665769945)
        ·
          refine ⟨47772713621284986499327459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63696951495046648665769945 47772713621284986499327459)
          ·
            refine ⟨71659070431927479748991189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47772713621284986499327459 71659070431927479748991189)
            ·
              refine ⟨1679509463248300306616981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71659070431927479748991189 1679509463248300306616981)
              ·
                refine ⟨78727006089764076872671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1679509463248300306616981 78727006089764076872671)
                ·
                  rfl

theorem cell22_2069824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_2069824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069824 prefixEnd_2069824 := by exact prefixLift 2069824
  have htrace : WordTrace (prefixWord ++ tailWord_2069824) baseStart_2069824 baseEnd_2069824 := by
    simpa [prefixWord, tailWord_2069824, baseEnd_2069824] using wordTrace_append hprefix tailTrace_2069824
  have hstable : (prefixWord ++ tailWord_2069824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069824).length < 2 ^ (prefixWord ++ tailWord_2069824).sum := by decide
  have hdescent : baseEnd_2069824 < baseStart_2069824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069856 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_2069856 : Nat := 118140960795 + 2069856 * 2 ^ 59
def prefixEnd_2069856 : Nat := 4983230072969 + 3 ^ 40 * 2069856 * 2
def baseEnd_2069856 : Nat := 708554009061839275053941

theorem tailTrace_2069856 : CollatzResearch.WordTrace tailWord_2069856 prefixEnd_2069856 708554009061839275053941 := by
  unfold tailWord_2069856
  simp only [CollatzResearch.WordTrace]
  refine ⟨37746925194636345053038711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50329233592848460070718281 37746925194636345053038711)
  ·
    refine ⟨56620387791954517579558067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37746925194636345053038711 56620387791954517579558067)
    ·
      refine ⟨84930581687931776369337101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56620387791954517579558067 84930581687931776369337101)
      ·
        refine ⟨31848968132974416138501413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84930581687931776369337101 31848968132974416138501413)
        ·
          refine ⟨5971681524932703025969015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31848968132974416138501413 5971681524932703025969015)
          ·
            refine ⟨8957522287399054538953523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971681524932703025969015 8957522287399054538953523)
            ·
              refine ⟨13436283431098581808430285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957522287399054538953523 13436283431098581808430285)
              ·
                refine ⟨5038606286661968178161357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13436283431098581808430285 5038606286661968178161357)
                ·
                  refine ⟨1889477357498238066810509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5038606286661968178161357 1889477357498238066810509)
                  ·
                    refine ⟨708554009061839275053941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889477357498238066810509 708554009061839275053941)
                    ·
                      rfl

theorem cell22_2069856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_2069856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069856 prefixEnd_2069856 := by exact prefixLift 2069856
  have htrace : WordTrace (prefixWord ++ tailWord_2069856) baseStart_2069856 baseEnd_2069856 := by
    simpa [prefixWord, tailWord_2069856, baseEnd_2069856] using wordTrace_append hprefix tailTrace_2069856
  have hstable : (prefixWord ++ tailWord_2069856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069856).length < 2 ^ (prefixWord ++ tailWord_2069856).sum := by decide
  have hdescent : baseEnd_2069856 < baseStart_2069856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069933 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2069933 : Nat := 118140960795 + 2069933 * 2 ^ 59
def prefixEnd_2069933 : Nat := 4983230072969 + 3 ^ 40 * 2069933 * 2
def baseEnd_2069933 : Nat := 708580367735436740878705

theorem tailTrace_2069933 : CollatzResearch.WordTrace tailWord_2069933 prefixEnd_2069933 708580367735436740878705 := by
  unfold tailWord_2069933
  simp only [CollatzResearch.WordTrace]
  refine ⟨75496658809993732256630453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50331105873329154837753635 75496658809993732256630453)
  ·
    refine ⟨7077811763436912399059105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75496658809993732256630453 7077811763436912399059105)
    ·
      refine ⟨5308358822577684299294329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077811763436912399059105 5308358822577684299294329)
      ·
        refine ⟨3981269116933263224470747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308358822577684299294329 3981269116933263224470747)
        ·
          refine ⟨5971903675399894836706121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981269116933263224470747 5971903675399894836706121)
          ·
            refine ⟨4478927756549921127529591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971903675399894836706121 4478927756549921127529591)
            ·
              refine ⟨6718391634824881691294387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478927756549921127529591 6718391634824881691294387)
              ·
                refine ⟨10077587452237322536941581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718391634824881691294387 10077587452237322536941581)
                ·
                  refine ⟨3779095294588995951353093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077587452237322536941581 3779095294588995951353093)
                  ·
                    refine ⟨708580367735436740878705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779095294588995951353093 708580367735436740878705)
                    ·
                      rfl

theorem cell22_2069933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2069933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069933 prefixEnd_2069933 := by exact prefixLift 2069933
  have htrace : WordTrace (prefixWord ++ tailWord_2069933) baseStart_2069933 baseEnd_2069933 := by
    simpa [prefixWord, tailWord_2069933, baseEnd_2069933] using wordTrace_append hprefix tailTrace_2069933
  have hstable : (prefixWord ++ tailWord_2069933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069933).length < 2 ^ (prefixWord ++ tailWord_2069933).sum := by decide
  have hdescent : baseEnd_2069933 < baseStart_2069933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069944 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_2069944 : Nat := 118140960795 + 2069944 * 2 ^ 59
def prefixEnd_2069944 : Nat := 4983230072969 + 3 ^ 40 * 2069944 * 2
def baseEnd_2069944 : Nat := 708584133260236378853671

theorem tailTrace_2069944 : CollatzResearch.WordTrace tailWord_2069944 prefixEnd_2069944 708584133260236378853671 := by
  unfold tailWord_2069944
  simp only [CollatzResearch.WordTrace]
  refine ⟨37748530006476940567640443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50331373341969254090187257 37748530006476940567640443)
  ·
    refine ⟨56622795009715410851460665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37748530006476940567640443 56622795009715410851460665)
    ·
      refine ⟨42467096257286558138595499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56622795009715410851460665 42467096257286558138595499)
      ·
        refine ⟨63700644385929837207893249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42467096257286558138595499 63700644385929837207893249)
        ·
          refine ⟨47775483289447377905919937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63700644385929837207893249 47775483289447377905919937)
          ·
            refine ⟨35831612467085533429439953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47775483289447377905919937 35831612467085533429439953)
            ·
              refine ⟨26873709350314150072079965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35831612467085533429439953 26873709350314150072079965)
              ·
                refine ⟨10077641006367806277029987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26873709350314150072079965 10077641006367806277029987)
                ·
                  refine ⟨15116461509551709415544981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10077641006367806277029987 15116461509551709415544981)
                  ·
                    refine ⟨708584133260236378853671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15116461509551709415544981 708584133260236378853671)
                    ·
                      rfl

theorem cell22_2069944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_2069944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069944 prefixEnd_2069944 := by exact prefixLift 2069944
  have htrace : WordTrace (prefixWord ++ tailWord_2069944) baseStart_2069944 baseEnd_2069944 := by
    simpa [prefixWord, tailWord_2069944, baseEnd_2069944] using wordTrace_append hprefix tailTrace_2069944
  have hstable : (prefixWord ++ tailWord_2069944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069944).length < 2 ^ (prefixWord ++ tailWord_2069944).sum := by decide
  have hdescent : baseEnd_2069944 < baseStart_2069944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069954 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2069954 : Nat := 118140960795 + 2069954 * 2 ^ 59
def prefixEnd_2069954 : Nat := 4983230072969 + 3 ^ 40 * 2069954 * 2
def baseEnd_2069954 : Nat := 236195852154866562034547

theorem tailTrace_2069954 : CollatzResearch.WordTrace tailWord_2069954 prefixEnd_2069954 236195852154866562034547 := by
  unfold tailWord_2069954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874356185729413210786229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50331616495278435228763277 18874356185729413210786229)
  ·
    refine ⟨1769470892412132488511209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18874356185729413210786229 1769470892412132488511209)
    ·
      refine ⟨1327103169309099366383407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1769470892412132488511209 1327103169309099366383407)
      ·
        refine ⟨1990654753963649049575111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327103169309099366383407 1990654753963649049575111)
        ·
          refine ⟨2985982130945473574362667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990654753963649049575111 2985982130945473574362667)
          ·
            refine ⟨4478973196418210361544001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985982130945473574362667 4478973196418210361544001)
            ·
              refine ⟨3359229897313657771158001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478973196418210361544001 3359229897313657771158001)
              ·
                refine ⟨2519422422985243328368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359229897313657771158001 2519422422985243328368501)
                ·
                  refine ⟨236195852154866562034547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519422422985243328368501 236195852154866562034547)
                  ·
                    rfl

theorem cell22_2069954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2069954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2069954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2069954 prefixEnd_2069954 := by exact prefixLift 2069954
  have htrace : WordTrace (prefixWord ++ tailWord_2069954) baseStart_2069954 baseEnd_2069954 := by
    simpa [prefixWord, tailWord_2069954, baseEnd_2069954] using wordTrace_append hprefix tailTrace_2069954
  have hstable : (prefixWord ++ tailWord_2069954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069954).length < 2 ^ (prefixWord ++ tailWord_2069954).sum := by decide
  have hdescent : baseEnd_2069954 < baseStart_2069954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070014 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2070014 : Nat := 118140960795 + 2070014 * 2 ^ 59
def prefixEnd_2070014 : Nat := 4983230072969 + 3 ^ 40 * 2070014 * 2
def baseEnd_2070014 : Nat := 708608095690779529603457

theorem tailTrace_2070014 : CollatzResearch.WordTrace tailWord_2070014 prefixEnd_2070014 708608095690779529603457 := by
  unfold tailWord_2070014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437451640337535386291137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50333075415133522060219397 9437451640337535386291137)
  ·
    refine ⟨7078088730253151539718353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9437451640337535386291137 7078088730253151539718353)
    ·
      refine ⟨5308566547689863654788765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7078088730253151539718353 5308566547689863654788765)
      ·
        refine ⟨1990712455383698870545787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5308566547689863654788765 1990712455383698870545787)
        ·
          refine ⟨2986068683075548305818681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990712455383698870545787 2986068683075548305818681)
          ·
            refine ⟨2239551512306661229364011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986068683075548305818681 2239551512306661229364011)
            ·
              refine ⟨3359327268459991844046017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239551512306661229364011 3359327268459991844046017)
              ·
                refine ⟨2519495451344993883034513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359327268459991844046017 2519495451344993883034513)
                ·
                  refine ⟨1889621588508745412275885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519495451344993883034513 1889621588508745412275885)
                  ·
                    refine ⟨708608095690779529603457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889621588508745412275885 708608095690779529603457)
                    ·
                      rfl

theorem cell22_2070014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2070014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070014 prefixEnd_2070014 := by exact prefixLift 2070014
  have htrace : WordTrace (prefixWord ++ tailWord_2070014) baseStart_2070014 baseEnd_2070014 := by
    simpa [prefixWord, tailWord_2070014, baseEnd_2070014] using wordTrace_append hprefix tailTrace_2070014
  have hstable : (prefixWord ++ tailWord_2070014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070014).length < 2 ^ (prefixWord ++ tailWord_2070014).sum := by decide
  have hdescent : baseEnd_2070014 < baseStart_2070014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070096 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_2070096 : Nat := 118140960795 + 2070096 * 2 ^ 59
def prefixEnd_2070096 : Nat := 4983230072969 + 3 ^ 40 * 2070096 * 2
def baseEnd_2070096 : Nat := 708636165966558649053205

theorem tailTrace_2070096 : CollatzResearch.WordTrace tailWord_2070096 prefixEnd_2070096 708636165966558649053205 := by
  unfold tailWord_2070096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37751301954201605547407071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50335069272268807396542761 37751301954201605547407071)
  ·
    refine ⟨56626952931302408321110607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37751301954201605547407071 56626952931302408321110607)
    ·
      refine ⟨84940429396953612481665911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56626952931302408321110607 84940429396953612481665911)
      ·
        refine ⟨127410644095430418722498867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84940429396953612481665911 127410644095430418722498867)
        ·
          refine ⟨191115966143145628083748301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127410644095430418722498867 191115966143145628083748301)
          ·
            refine ⟨71668487303679610531405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191115966143145628083748301 71668487303679610531405613)
            ·
              refine ⟨26875682738879853949277105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71668487303679610531405613 26875682738879853949277105)
              ·
                refine ⟨20156762054159890461957829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26875682738879853949277105 20156762054159890461957829)
                ·
                  refine ⟨3779392885154979461617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20156762054159890461957829 3779392885154979461617093)
                  ·
                    refine ⟨708636165966558649053205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779392885154979461617093 708636165966558649053205)
                    ·
                      rfl

theorem cell22_2070096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_2070096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070096 prefixEnd_2070096 := by exact prefixLift 2070096
  have htrace : WordTrace (prefixWord ++ tailWord_2070096) baseStart_2070096 baseEnd_2070096 := by
    simpa [prefixWord, tailWord_2070096, baseEnd_2070096] using wordTrace_append hprefix tailTrace_2070096
  have hstable : (prefixWord ++ tailWord_2070096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070096).length < 2 ^ (prefixWord ++ tailWord_2070096).sum := by decide
  have hdescent : baseEnd_2070096 < baseStart_2070096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070113 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2070113 : Nat := 118140960795 + 2070113 * 2 ^ 59
def prefixEnd_2070113 : Nat := 4983230072969 + 3 ^ 40 * 2070113 * 2
def baseEnd_2070113 : Nat := 708641985413976271378153

theorem tailTrace_2070113 : CollatzResearch.WordTrace tailWord_2070113 prefixEnd_2070113 708641985413976271378153 := by
  unfold tailWord_2070113
  simp only [CollatzResearch.WordTrace]
  refine ⟨75503223949341622998182993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50335482632894415332121995 75503223949341622998182993)
  ·
    refine ⟨56627417962006217248637245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75503223949341622998182993 56627417962006217248637245)
    ·
      refine ⟨21235281735752331468238967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56627417962006217248637245 21235281735752331468238967)
      ·
        refine ⟨31852922603628497202358451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21235281735752331468238967 31852922603628497202358451)
        ·
          refine ⟨47779383905442745803537677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31852922603628497202358451 47779383905442745803537677)
          ·
            refine ⟨17917268964541029676326629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47779383905442745803537677 17917268964541029676326629)
            ·
              refine ⟨3359487930851443064311243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17917268964541029676326629 3359487930851443064311243)
              ·
                refine ⟨5039231896277164596466865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359487930851443064311243 5039231896277164596466865)
                ·
                  refine ⟨3779423922207873447350149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039231896277164596466865 3779423922207873447350149)
                  ·
                    refine ⟨708641985413976271378153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779423922207873447350149 708641985413976271378153)
                    ·
                      rfl

theorem cell22_2070113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2070113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070113 prefixEnd_2070113 := by exact prefixLift 2070113
  have htrace : WordTrace (prefixWord ++ tailWord_2070113) baseStart_2070113 baseEnd_2070113 := by
    simpa [prefixWord, tailWord_2070113, baseEnd_2070113] using wordTrace_append hprefix tailTrace_2070113
  have hstable : (prefixWord ++ tailWord_2070113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070113).length < 2 ^ (prefixWord ++ tailWord_2070113).sum := by decide
  have hdescent : baseEnd_2070113 < baseStart_2070113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070134 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_2070134 : Nat := 118140960795 + 2070134 * 2 ^ 59
def prefixEnd_2070134 : Nat := 4983230072969 + 3 ^ 40 * 2070134 * 2
def baseEnd_2070134 : Nat := 236216391381046405534363

theorem tailTrace_2070134 : CollatzResearch.WordTrace tailWord_2070134 prefixEnd_2070134 236216391381046405534363 := by
  unfold tailWord_2070134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718999367641596474043591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50335993254843695723131637 4718999367641596474043591)
  ·
    refine ⟨7078499051462394711065387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718999367641596474043591 7078499051462394711065387)
    ·
      refine ⟨10617748577193592066598081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078499051462394711065387 10617748577193592066598081)
      ·
        refine ⟨7963311432895194049948561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10617748577193592066598081 7963311432895194049948561)
        ·
          refine ⟨5972483574671395537461421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963311432895194049948561 5972483574671395537461421)
          ·
            refine ⟨2239681340501773326548033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5972483574671395537461421 2239681340501773326548033)
            ·
              refine ⟨1679761005376329994911025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239681340501773326548033 1679761005376329994911025)
              ·
                refine ⟨1259820754032247496183269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679761005376329994911025 1259820754032247496183269)
                ·
                  refine ⟨236216391381046405534363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259820754032247496183269 236216391381046405534363)
                  ·
                    rfl

theorem cell22_2070134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_2070134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070134 prefixEnd_2070134 := by exact prefixLift 2070134
  have htrace : WordTrace (prefixWord ++ tailWord_2070134) baseStart_2070134 baseEnd_2070134 := by
    simpa [prefixWord, tailWord_2070134, baseEnd_2070134] using wordTrace_append hprefix tailTrace_2070134
  have hstable : (prefixWord ++ tailWord_2070134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070134).length < 2 ^ (prefixWord ++ tailWord_2070134).sum := by decide
  have hdescent : baseEnd_2070134 < baseStart_2070134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070164 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2070164 : Nat := 118140960795 + 2070164 * 2 ^ 59
def prefixEnd_2070164 : Nat := 4983230072969 + 3 ^ 40 * 2070164 * 2
def baseEnd_2070164 : Nat := 708659443756229138352997

theorem tailTrace_2070164 : CollatzResearch.WordTrace tailWord_2070164 prefixEnd_2070164 708659443756229138352997 := by
  unfold tailWord_2070164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37752542036078429354144773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50336722714771239138859697 37752542036078429354144773)
  ·
    refine ⟨7078601631764705503902145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37752542036078429354144773 7078601631764705503902145)
    ·
      refine ⟨5308951223823529127926609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7078601631764705503902145 5308951223823529127926609)
      ·
        refine ⟨3981713417867646845944957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308951223823529127926609 3981713417867646845944957)
        ·
          refine ⟨1493142531700367567229359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3981713417867646845944957 1493142531700367567229359)
          ·
            refine ⟨2239713797550551350844039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493142531700367567229359 2239713797550551350844039)
            ·
              refine ⟨3359570696325827026266059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239713797550551350844039 3359570696325827026266059)
              ·
                refine ⟨5039356044488740539399089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359570696325827026266059 5039356044488740539399089)
                ·
                  refine ⟨3779517033366555404549317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039356044488740539399089 3779517033366555404549317)
                  ·
                    refine ⟨708659443756229138352997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779517033366555404549317 708659443756229138352997)
                    ·
                      rfl

theorem cell22_2070164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2070164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070164 prefixEnd_2070164 := by exact prefixLift 2070164
  have htrace : WordTrace (prefixWord ++ tailWord_2070164) baseStart_2070164 baseEnd_2070164 := by
    simpa [prefixWord, tailWord_2070164, baseEnd_2070164] using wordTrace_append hprefix tailTrace_2070164
  have hstable : (prefixWord ++ tailWord_2070164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070164).length < 2 ^ (prefixWord ++ tailWord_2070164).sum := by decide
  have hdescent : baseEnd_2070164 < baseStart_2070164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070177 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2070177 : Nat := 118140960795 + 2070177 * 2 ^ 59
def prefixEnd_2070177 : Nat := 4983230072969 + 3 ^ 40 * 2070177 * 2
def baseEnd_2070177 : Nat := 708663893921901437777957

theorem tailTrace_2070177 : CollatzResearch.WordTrace tailWord_2070177 prefixEnd_2070177 708663893921901437777957 := by
  unfold tailWord_2070177
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505558221109761928512785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50337038814073174619008523 75505558221109761928512785)
  ·
    refine ⟨56629168665832321446384589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75505558221109761928512785 56629168665832321446384589)
    ·
      refine ⟨21235938249687120542394221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56629168665832321446384589 21235938249687120542394221)
      ·
        refine ⟨7963476843632670203397833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21235938249687120542394221 7963476843632670203397833)
        ·
          refine ⟨5972607632724502652548375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963476843632670203397833 5972607632724502652548375)
          ·
            refine ⟨8958911449086753978822563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972607632724502652548375 8958911449086753978822563)
            ·
              refine ⟨13438367173630130968233845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958911449086753978822563 13438367173630130968233845)
              ·
                refine ⟨1259846922527824778271923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13438367173630130968233845 1259846922527824778271923)
                ·
                  refine ⟨1889770383791737167407885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259846922527824778271923 1889770383791737167407885)
                  ·
                    refine ⟨708663893921901437777957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889770383791737167407885 708663893921901437777957)
                    ·
                      rfl

theorem cell22_2070177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2070177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070177 prefixEnd_2070177 := by exact prefixLift 2070177
  have htrace : WordTrace (prefixWord ++ tailWord_2070177) baseStart_2070177 baseEnd_2070177 := by
    simpa [prefixWord, tailWord_2070177, baseEnd_2070177] using wordTrace_append hprefix tailTrace_2070177
  have hstable : (prefixWord ++ tailWord_2070177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070177).length < 2 ^ (prefixWord ++ tailWord_2070177).sum := by decide
  have hdescent : baseEnd_2070177 < baseStart_2070177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070250 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_2070250 : Nat := 118140960795 + 2070250 * 2 ^ 59
def prefixEnd_2070250 : Nat := 4983230072969 + 3 ^ 40 * 2070250 * 2
def baseEnd_2070250 : Nat := 708688883313753580702733

theorem tailTrace_2070250 : CollatzResearch.WordTrace tailWord_2070250 prefixEnd_2070250 708688883313753580702733 := by
  unfold tailWord_2070250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877055187461323848980051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50338813833230196930613469 18877055187461323848980051)
  ·
    refine ⟨28315582781191985773470077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18877055187461323848980051 28315582781191985773470077)
    ·
      refine ⟨10618343542946994665051279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28315582781191985773470077 10618343542946994665051279)
      ·
        refine ⟨15927515314420491997576919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10618343542946994665051279 15927515314420491997576919)
        ·
          refine ⟨23891272971630737996365379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927515314420491997576919 23891272971630737996365379)
          ·
            refine ⟨35836909457446106994548069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23891272971630737996365379 35836909457446106994548069)
            ·
              refine ⟨6719420523271145061477763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35836909457446106994548069 6719420523271145061477763)
              ·
                refine ⟨10079130784906717592216645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719420523271145061477763 10079130784906717592216645)
                ·
                  refine ⟨1889837022170009548540621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10079130784906717592216645 1889837022170009548540621)
                  ·
                    refine ⟨708688883313753580702733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889837022170009548540621 708688883313753580702733)
                    ·
                      rfl

theorem cell22_2070250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_2070250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070250 prefixEnd_2070250 := by exact prefixLift 2070250
  have htrace : WordTrace (prefixWord ++ tailWord_2070250) baseStart_2070250 baseEnd_2070250 := by
    simpa [prefixWord, tailWord_2070250, baseEnd_2070250] using wordTrace_append hprefix tailTrace_2070250
  have hstable : (prefixWord ++ tailWord_2070250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070250).length < 2 ^ (prefixWord ++ tailWord_2070250).sum := by decide
  have hdescent : baseEnd_2070250 < baseStart_2070250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070329 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_2070329 : Nat := 118140960795 + 2070329 * 2 ^ 59
def prefixEnd_2070329 : Nat := 4983230072969 + 3 ^ 40 * 2070329 * 2
def baseEnd_2070329 : Nat := 708715926628223707977491

theorem tailTrace_2070329 : CollatzResearch.WordTrace tailWord_2070329 prefixEnd_2070329 708715926628223707977491 := by
  unfold tailWord_2070329
  simp only [CollatzResearch.WordTrace]
  refine ⟨75511102116559091888046041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50340734744372727925364027 75511102116559091888046041)
  ·
    refine ⟨56633326587419318916034531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75511102116559091888046041 56633326587419318916034531)
    ·
      refine ⟨84949989881128978374051797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56633326587419318916034531 84949989881128978374051797)
      ·
        refine ⟨1991015387838960430641839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84949989881128978374051797 1991015387838960430641839)
        ·
          refine ⟨2986523081758440645962759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991015387838960430641839 2986523081758440645962759)
          ·
            refine ⟨4479784622637660968944139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986523081758440645962759 4479784622637660968944139)
            ·
              refine ⟨6719676933956491453416209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479784622637660968944139 6719676933956491453416209)
              ·
                refine ⟨5039757700467368590062157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719676933956491453416209 5039757700467368590062157)
                ·
                  refine ⟨1889909137675263221273309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5039757700467368590062157 1889909137675263221273309)
                  ·
                    refine ⟨708715926628223707977491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1889909137675263221273309 708715926628223707977491)
                    ·
                      rfl

theorem cell22_2070329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_2070329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070329 prefixEnd_2070329 := by exact prefixLift 2070329
  have htrace : WordTrace (prefixWord ++ tailWord_2070329) baseStart_2070329 baseEnd_2070329 := by
    simpa [prefixWord, tailWord_2070329, baseEnd_2070329] using wordTrace_append hprefix tailTrace_2070329
  have hstable : (prefixWord ++ tailWord_2070329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070329).length < 2 ^ (prefixWord ++ tailWord_2070329).sum := by decide
  have hdescent : baseEnd_2070329 < baseStart_2070329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070359 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 5]
def baseStart_2070359 : Nat := 118140960795 + 2070359 * 2 ^ 59
def prefixEnd_2070359 : Nat := 4983230072969 + 3 ^ 40 * 2070359 * 2
def baseEnd_2070359 : Nat := 236242065413771209909133

theorem tailTrace_2070359 : CollatzResearch.WordTrace tailWord_2070359 prefixEnd_2070359 236242065413771209909133 := by
  unfold tailWord_2070359
  simp only [CollatzResearch.WordTrace]
  refine ⟨75512196306450407011638131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50341464204300271341092087 75512196306450407011638131)
  ·
    refine ⟨113268294459675610517457197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75512196306450407011638131 113268294459675610517457197)
    ·
      refine ⟨42475610422378353944046449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113268294459675610517457197 42475610422378353944046449)
      ·
        refine ⟨31856707816783765458034837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42475610422378353944046449 31856707816783765458034837)
        ·
          refine ⟨1493283178911739005845383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31856707816783765458034837 1493283178911739005845383)
          ·
            refine ⟨2239924768367608508768075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493283178911739005845383 2239924768367608508768075)
            ·
              refine ⟨3359887152551412763152113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239924768367608508768075 3359887152551412763152113)
              ·
                refine ⟨2519915364413559572364085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359887152551412763152113 2519915364413559572364085)
                ·
                  refine ⟨236242065413771209909133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519915364413559572364085 236242065413771209909133)
                  ·
                    rfl

theorem cell22_2070359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 5].length) (baseStart_2070359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070359 prefixEnd_2070359 := by exact prefixLift 2070359
  have htrace : WordTrace (prefixWord ++ tailWord_2070359) baseStart_2070359 baseEnd_2070359 := by
    simpa [prefixWord, tailWord_2070359, baseEnd_2070359] using wordTrace_append hprefix tailTrace_2070359
  have hstable : (prefixWord ++ tailWord_2070359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070359).length < 2 ^ (prefixWord ++ tailWord_2070359).sum := by decide
  have hdescent : baseEnd_2070359 < baseStart_2070359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070400 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_2070400 : Nat := 118140960795 + 2070400 * 2 ^ 59
def prefixEnd_2070400 : Nat := 4983230072969 + 3 ^ 40 * 2070400 * 2
def baseEnd_2070400 : Nat := 708740231379203189452273

theorem tailTrace_2070400 : CollatzResearch.WordTrace tailWord_2070400 prefixEnd_2070400 708740231379203189452273 := by
  unfold tailWord_2070400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37756845849650935506940327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50342461132867914009253769 37756845849650935506940327)
  ·
    refine ⟨56635268774476403260410491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37756845849650935506940327 56635268774476403260410491)
    ·
      refine ⟨84952903161714604890615737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56635268774476403260410491 84952903161714604890615737)
      ·
        refine ⟨63714677371285953667961803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84952903161714604890615737 63714677371285953667961803)
        ·
          refine ⟨95572016056928930501942705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63714677371285953667961803 95572016056928930501942705)
          ·
            refine ⟨71679012042696697876457029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95572016056928930501942705 71679012042696697876457029)
            ·
              refine ⟨13439814758005630851835693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71679012042696697876457029 13439814758005630851835693)
              ·
                refine ⟨5039930534252111569438385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13439814758005630851835693 5039930534252111569438385)
                ·
                  refine ⟨3779947900689083677078789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039930534252111569438385 3779947900689083677078789)
                  ·
                    refine ⟨708740231379203189452273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779947900689083677078789 708740231379203189452273)
                    ·
                      rfl

theorem cell22_2070400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_2070400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070400 prefixEnd_2070400 := by exact prefixLift 2070400
  have htrace : WordTrace (prefixWord ++ tailWord_2070400) baseStart_2070400 baseEnd_2070400 := by
    simpa [prefixWord, tailWord_2070400, baseEnd_2070400] using wordTrace_append hprefix tailTrace_2070400
  have hstable : (prefixWord ++ tailWord_2070400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070400).length < 2 ^ (prefixWord ++ tailWord_2070400).sum := by decide
  have hdescent : baseEnd_2070400 < baseStart_2070400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070436 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_2070436 : Nat := 118140960795 + 2070436 * 2 ^ 59
def prefixEnd_2070436 : Nat := 4983230072969 + 3 ^ 40 * 2070436 * 2
def baseEnd_2070436 : Nat := 708752554914911095552163

theorem tailTrace_2070436 : CollatzResearch.WordTrace tailWord_2070436 prefixEnd_2070436 708752554914911095552163 := by
  unfold tailWord_2070436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757502363585724581095581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50343336484780966108127441 37757502363585724581095581)
  ·
    refine ⟨14159063386344646717910843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37757502363585724581095581 14159063386344646717910843)
    ·
      refine ⟨21238595079516970076866265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159063386344646717910843 21238595079516970076866265)
      ·
        refine ⟨15928946309637727557649699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21238595079516970076866265 15928946309637727557649699)
        ·
          refine ⟨23893419464456591336474549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928946309637727557649699 23893419464456591336474549)
          ·
            refine ⟨2240008074792805437794489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23893419464456591336474549 2240008074792805437794489)
            ·
              refine ⟨1680006056094604078345867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240008074792805437794489 1680006056094604078345867)
              ·
                refine ⟨2520009084141906117518801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680006056094604078345867 2520009084141906117518801)
                ·
                  refine ⟨1890006813106429588139101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2520009084141906117518801 1890006813106429588139101)
                  ·
                    refine ⟨708752554914911095552163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1890006813106429588139101 708752554914911095552163)
                    ·
                      rfl

theorem cell22_2070436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_2070436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070436 prefixEnd_2070436 := by exact prefixLift 2070436
  have htrace : WordTrace (prefixWord ++ tailWord_2070436) baseStart_2070436 baseEnd_2070436 := by
    simpa [prefixWord, tailWord_2070436, baseEnd_2070436] using wordTrace_append hprefix tailTrace_2070436
  have hstable : (prefixWord ++ tailWord_2070436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070436).length < 2 ^ (prefixWord ++ tailWord_2070436).sum := by decide
  have hdescent : baseEnd_2070436 < baseStart_2070436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070464 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_2070464 : Nat := 118140960795 + 2070464 * 2 ^ 59
def prefixEnd_2070464 : Nat := 4983230072969 + 3 ^ 40 * 2070464 * 2
def baseEnd_2070464 : Nat := 708762139887128355852077

theorem tailTrace_2070464 : CollatzResearch.WordTrace tailWord_2070464 prefixEnd_2070464 708762139887128355852077 := by
  unfold tailWord_2070464
  simp only [CollatzResearch.WordTrace]
  refine ⟨37758012985535004972105223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50344017314046673296140297 37758012985535004972105223)
  ·
    refine ⟨56637019478302507458157835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37758012985535004972105223 56637019478302507458157835)
    ·
      refine ⟨84955529217453761187236753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56637019478302507458157835 84955529217453761187236753)
      ·
        refine ⟨63716646913090320890427565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84955529217453761187236753 63716646913090320890427565)
        ·
          refine ⟨23893742592408870333910337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63716646913090320890427565 23893742592408870333910337)
          ·
            refine ⟨17920306944306652750432753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23893742592408870333910337 17920306944306652750432753)
            ·
              refine ⟨13440230208229989562824565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17920306944306652750432753 13440230208229989562824565)
              ·
                refine ⟨1260021582021561521514803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13440230208229989562824565 1260021582021561521514803)
                ·
                  refine ⟨1890032373032342282272205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260021582021561521514803 1890032373032342282272205)
                  ·
                    refine ⟨708762139887128355852077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1890032373032342282272205 708762139887128355852077)
                    ·
                      rfl

theorem cell22_2070464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_2070464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070464 prefixEnd_2070464 := by exact prefixLift 2070464
  have htrace : WordTrace (prefixWord ++ tailWord_2070464) baseStart_2070464 baseEnd_2070464 := by
    simpa [prefixWord, tailWord_2070464, baseEnd_2070464] using wordTrace_append hprefix tailTrace_2070464
  have hstable : (prefixWord ++ tailWord_2070464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070464).length < 2 ^ (prefixWord ++ tailWord_2070464).sum := by decide
  have hdescent : baseEnd_2070464 < baseStart_2070464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070475 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_2070475 : Nat := 118140960795 + 2070475 * 2 ^ 59
def prefixEnd_2070475 : Nat := 4983230072969 + 3 ^ 40 * 2070475 * 2
def baseEnd_2070475 : Nat := 708765905411927993827043

theorem tailTrace_2070475 : CollatzResearch.WordTrace tailWord_2070475 prefixEnd_2070475 708765905411927993827043 := by
  unfold tailWord_2070475
  simp only [CollatzResearch.WordTrace]
  refine ⟨75516427174030158822860879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50344284782686772548573919 75516427174030158822860879)
  ·
    refine ⟨113274640761045238234291319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75516427174030158822860879 113274640761045238234291319)
    ·
      refine ⟨169911961141567857351436979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113274640761045238234291319 169911961141567857351436979)
      ·
        refine ⟨254867941712351786027155469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169911961141567857351436979 254867941712351786027155469)
        ·
          refine ⟨95575478142131919760183301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254867941712351786027155469 95575478142131919760183301)
          ·
            refine ⟨17920402151649734955034369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95575478142131919760183301 17920402151649734955034369)
            ·
              refine ⟨13440301613737301216275777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17920402151649734955034369 13440301613737301216275777)
              ·
                refine ⟨10080226210302975912206833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13440301613737301216275777 10080226210302975912206833)
                ·
                  refine ⟨7560169657727231934155125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080226210302975912206833 7560169657727231934155125)
                  ·
                    refine ⟨708765905411927993827043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7560169657727231934155125 708765905411927993827043)
                    ·
                      rfl

theorem cell22_2070475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_2070475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070475 prefixEnd_2070475 := by exact prefixLift 2070475
  have htrace : WordTrace (prefixWord ++ tailWord_2070475) baseStart_2070475 baseEnd_2070475 := by
    simpa [prefixWord, tailWord_2070475, baseEnd_2070475] using wordTrace_append hprefix tailTrace_2070475
  have hstable : (prefixWord ++ tailWord_2070475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070475).length < 2 ^ (prefixWord ++ tailWord_2070475).sum := by decide
  have hdescent : baseEnd_2070475 < baseStart_2070475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070554 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_2070554 : Nat := 118140960795 + 2070554 * 2 ^ 59
def prefixEnd_2070554 : Nat := 4983230072969 + 3 ^ 40 * 2070554 * 2
def baseEnd_2070554 : Nat := 708792948726398121101801

theorem tailTrace_2070554 : CollatzResearch.WordTrace tailWord_2070554 prefixEnd_2070554 708792948726398121101801 := by
  unfold tailWord_2070554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879827135185988828746679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50346205693829303543324477 18879827135185988828746679)
  ·
    refine ⟨28319740702778983243120019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18879827135185988828746679 28319740702778983243120019)
    ·
      refine ⟨42479611054168474864680029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28319740702778983243120019 42479611054168474864680029)
      ·
        refine ⟨15929854145313178074255011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42479611054168474864680029 15929854145313178074255011)
        ·
          refine ⟨23894781217969767111382517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15929854145313178074255011 23894781217969767111382517)
          ·
            refine ⟨2240135739184665666692111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23894781217969767111382517 2240135739184665666692111)
            ·
              refine ⟨3360203608776998500038167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240135739184665666692111 3360203608776998500038167)
              ·
                refine ⟨5040305413165497750057251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360203608776998500038167 5040305413165497750057251)
                ·
                  refine ⟨7560458119748246625085877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040305413165497750057251 7560458119748246625085877)
                  ·
                    refine ⟨708792948726398121101801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7560458119748246625085877 708792948726398121101801)
                    ·
                      rfl

theorem cell22_2070554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_2070554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070554 prefixEnd_2070554 := by exact prefixLift 2070554
  have htrace : WordTrace (prefixWord ++ tailWord_2070554) baseStart_2070554 baseEnd_2070554 := by
    simpa [prefixWord, tailWord_2070554, baseEnd_2070554] using wordTrace_append hprefix tailTrace_2070554
  have hstable : (prefixWord ++ tailWord_2070554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070554).length < 2 ^ (prefixWord ++ tailWord_2070554).sum := by decide
  have hdescent : baseEnd_2070554 < baseStart_2070554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070584 : List Nat := [2, 1, 2, 1, 7, 1, 8]
def baseStart_2070584 : Nat := 118140960795 + 2070584 * 2 ^ 59
def prefixEnd_2070584 : Nat := 4983230072969 + 3 ^ 40 * 2070584 * 2
def baseEnd_2070584 : Nat := 26251971049610668253767

theorem tailTrace_2070584 : CollatzResearch.WordTrace tailWord_2070584 prefixEnd_2070584 26251971049610668253767 := by
  unfold tailWord_2070584
  simp only [CollatzResearch.WordTrace]
  refine ⟨37760201365317635219289403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50346935153756846959052537 37760201365317635219289403)
  ·
    refine ⟨56640302047976452828934105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37760201365317635219289403 56640302047976452828934105)
    ·
      refine ⟨42480226535982339621700579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56640302047976452828934105 42480226535982339621700579)
      ·
        refine ⟨63720339803973509432550869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42480226535982339621700579 63720339803973509432550869)
        ·
          refine ⟨1493445464155629127325411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63720339803973509432550869 1493445464155629127325411)
          ·
            refine ⟨2240168196233443690988117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493445464155629127325411 2240168196233443690988117)
            ·
              refine ⟨26251971049610668253767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2240168196233443690988117 26251971049610668253767)
              ·
                rfl

theorem cell22_2070584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 8].length) (baseStart_2070584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070584 prefixEnd_2070584 := by exact prefixLift 2070584
  have htrace : WordTrace (prefixWord ++ tailWord_2070584) baseStart_2070584 baseEnd_2070584 := by
    simpa [prefixWord, tailWord_2070584, baseEnd_2070584] using wordTrace_append hprefix tailTrace_2070584
  have hstable : (prefixWord ++ tailWord_2070584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070584).length < 2 ^ (prefixWord ++ tailWord_2070584).sum := by decide
  have hdescent : baseEnd_2070584 < baseStart_2070584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070646 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2070646 : Nat := 118140960795 + 2070646 * 2 ^ 59
def prefixEnd_2070646 : Nat := 4983230072969 + 3 ^ 40 * 2070646 * 2
def baseEnd_2070646 : Nat := 236274814068846849267173

theorem tailTrace_2070646 : CollatzResearch.WordTrace tailWord_2070646 prefixEnd_2070646 236274814068846849267173 := by
  unfold tailWord_2070646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720166503525665939208487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50348442704273770018223861 4720166503525665939208487)
  ·
    refine ⟨7080249755288498908812731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720166503525665939208487 7080249755288498908812731)
    ·
      refine ⟨10620374632932748363219097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7080249755288498908812731 10620374632932748363219097)
      ·
        refine ⟨7965280974699561272414323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10620374632932748363219097 7965280974699561272414323)
        ·
          refine ⟨11947921462049341908621485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965280974699561272414323 11947921462049341908621485)
          ·
            refine ⟨4480470548268503215733057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11947921462049341908621485 4480470548268503215733057)
            ·
              refine ⟨3360352911201377411799793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480470548268503215733057 3360352911201377411799793)
              ·
                refine ⟨2520264683401033058849845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360352911201377411799793 2520264683401033058849845)
                ·
                  refine ⟨236274814068846849267173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2520264683401033058849845 236274814068846849267173)
                  ·
                    rfl

theorem cell22_2070646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2070646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070646 prefixEnd_2070646 := by exact prefixLift 2070646
  have htrace : WordTrace (prefixWord ++ tailWord_2070646) baseStart_2070646 baseEnd_2070646 := by
    simpa [prefixWord, tailWord_2070646, baseEnd_2070646] using wordTrace_append hprefix tailTrace_2070646
  have hstable : (prefixWord ++ tailWord_2070646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070646).length < 2 ^ (prefixWord ++ tailWord_2070646).sum := by decide
  have hdescent : baseEnd_2070646 < baseStart_2070646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070674 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_2070674 : Nat := 118140960795 + 2070674 * 2 ^ 59
def prefixEnd_2070674 : Nat := 4983230072969 + 3 ^ 40 * 2070674 * 2
def baseEnd_2070674 : Nat := 236278009059585936033811

theorem tailTrace_2070674 : CollatzResearch.WordTrace tailWord_2070674 prefixEnd_2070674 236278009059585936033811 := by
  unfold tailWord_2070674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18880921325077303952338769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50349123533539477206236717 18880921325077303952338769)
  ·
    refine ⟨14160690993807977964254077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18880921325077303952338769 14160690993807977964254077)
    ·
      refine ⟨5310259122677991736595279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14160690993807977964254077 5310259122677991736595279)
      ·
        refine ⟨7965388684016987604892919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310259122677991736595279 7965388684016987604892919)
        ·
          refine ⟨11948083026025481407339379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965388684016987604892919 11948083026025481407339379)
          ·
            refine ⟨17922124539038222111009069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11948083026025481407339379 17922124539038222111009069)
            ·
              refine ⟨6720796702139333291628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17922124539038222111009069 6720796702139333291628401)
              ·
                refine ⟨5040597526604499968721301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720796702139333291628401 5040597526604499968721301)
                ·
                  refine ⟨236278009059585936033811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5040597526604499968721301 236278009059585936033811)
                  ·
                    rfl

theorem cell22_2070674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_2070674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070674 prefixEnd_2070674 := by exact prefixLift 2070674
  have htrace : WordTrace (prefixWord ++ tailWord_2070674) baseStart_2070674 baseEnd_2070674 := by
    simpa [prefixWord, tailWord_2070674, baseEnd_2070674] using wordTrace_append hprefix tailTrace_2070674
  have hstable : (prefixWord ++ tailWord_2070674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070674).length < 2 ^ (prefixWord ++ tailWord_2070674).sum := by decide
  have hdescent : baseEnd_2070674 < baseStart_2070674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070689 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2070689 : Nat := 118140960795 + 2070689 * 2 ^ 59
def prefixEnd_2070689 : Nat := 4983230072969 + 3 ^ 40 * 2070689 * 2
def baseEnd_2070689 : Nat := 708839161985302768976387

theorem tailTrace_2070689 : CollatzResearch.WordTrace tailWord_2070689 prefixEnd_2070689 708839161985302768976387 := by
  unfold tailWord_2070689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524232395254873371151121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50349488263503248914100747 75524232395254873371151121)
  ·
    refine ⟨56643174296441155028363341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75524232395254873371151121 56643174296441155028363341)
    ·
      refine ⟨21241190361165433135636253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56643174296441155028363341 21241190361165433135636253)
      ·
        refine ⟨7965446385437037425863595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21241190361165433135636253 7965446385437037425863595)
        ·
          refine ⟨11948169578155556138795393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965446385437037425863595 11948169578155556138795393)
          ·
            refine ⟨8961127183616667104096545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11948169578155556138795393 8961127183616667104096545)
            ·
              refine ⟨6720845387712500328072409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961127183616667104096545 6720845387712500328072409)
              ·
                refine ⟨5040634040784375246054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720845387712500328072409 5040634040784375246054307)
                ·
                  refine ⟨7560951061176562869081461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040634040784375246054307 7560951061176562869081461)
                  ·
                    refine ⟨708839161985302768976387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7560951061176562869081461 708839161985302768976387)
                    ·
                      rfl

theorem cell22_2070689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2070689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070689 prefixEnd_2070689 := by exact prefixLift 2070689
  have htrace : WordTrace (prefixWord ++ tailWord_2070689) baseStart_2070689 baseEnd_2070689 := by
    simpa [prefixWord, tailWord_2070689, baseEnd_2070689] using wordTrace_append hprefix tailTrace_2070689
  have hstable : (prefixWord ++ tailWord_2070689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070689).length < 2 ^ (prefixWord ++ tailWord_2070689).sum := by decide
  have hdescent : baseEnd_2070689 < baseStart_2070689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070747 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 7]
def baseStart_2070747 : Nat := 118140960795 + 2070747 * 2 ^ 59
def prefixEnd_2070747 : Nat := 4983230072969 + 3 ^ 40 * 2070747 * 2
def baseEnd_2070747 : Nat := 236286338856869983675403

theorem tailTrace_2070747 : CollatzResearch.WordTrace tailWord_2070747 prefixEnd_2070747 236286338856869983675403 := by
  unfold tailWord_2070747
  simp only [CollatzResearch.WordTrace]
  refine ⟨75526347829044749276762495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50350898552696499517841663 75526347829044749276762495)
  ·
    refine ⟨113289521743567123915143743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75526347829044749276762495 113289521743567123915143743)
    ·
      refine ⟨169934282615350685872715615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113289521743567123915143743 169934282615350685872715615)
      ·
        refine ⟨254901423923026028809073423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169934282615350685872715615 254901423923026028809073423)
        ·
          refine ⟨382352135884539043213610135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254901423923026028809073423 382352135884539043213610135)
          ·
            refine ⟨573528203826808564820415203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382352135884539043213610135 573528203826808564820415203)
            ·
              refine ⟨860292305740212847230622805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573528203826808564820415203 860292305740212847230622805)
              ·
                refine ⟨10081550457893119303483861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 860292305740212847230622805 10081550457893119303483861)
                ·
                  refine ⟨236286338856869983675403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10081550457893119303483861 236286338856869983675403)
                  ·
                    rfl

theorem cell22_2070747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_2070747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070747 prefixEnd_2070747 := by exact prefixLift 2070747
  have htrace : WordTrace (prefixWord ++ tailWord_2070747) baseStart_2070747 baseEnd_2070747 := by
    simpa [prefixWord, tailWord_2070747, baseEnd_2070747] using wordTrace_append hprefix tailTrace_2070747
  have hstable : (prefixWord ++ tailWord_2070747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070747).length < 2 ^ (prefixWord ++ tailWord_2070747).sum := by decide
  have hdescent : baseEnd_2070747 < baseStart_2070747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070764 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_2070764 : Nat := 118140960795 + 2070764 * 2 ^ 59
def prefixEnd_2070764 : Nat := 4983230072969 + 3 ^ 40 * 2070764 * 2
def baseEnd_2070764 : Nat := 236288278672675857783719

theorem tailTrace_2070764 : CollatzResearch.WordTrace tailWord_2070764 prefixEnd_2070764 236288278672675857783719 := by
  unfold tailWord_2070764
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763483934991580590065673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50351311913322107453420897 37763483934991580590065673)
  ·
    refine ⟨28322612951243685442549255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37763483934991580590065673 28322612951243685442549255)
    ·
      refine ⟨42483919426865528163823883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28322612951243685442549255 42483919426865528163823883)
      ·
        refine ⟨63725879140298292245735825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42483919426865528163823883 63725879140298292245735825)
        ·
          refine ⟨47794409355223719184301869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63725879140298292245735825 47794409355223719184301869)
          ·
            refine ⟨17922903508208894694113201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47794409355223719184301869 17922903508208894694113201)
            ·
              refine ⟨13442177631156671020584901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17922903508208894694113201 13442177631156671020584901)
              ·
                refine ⟨2520408305841875816359669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13442177631156671020584901 2520408305841875816359669)
                ·
                  refine ⟨236288278672675857783719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2520408305841875816359669 236288278672675857783719)
                  ·
                    rfl

theorem cell22_2070764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_2070764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070764 prefixEnd_2070764 := by exact prefixLift 2070764
  have htrace : WordTrace (prefixWord ++ tailWord_2070764) baseStart_2070764 baseEnd_2070764 := by
    simpa [prefixWord, tailWord_2070764, baseEnd_2070764] using wordTrace_append hprefix tailTrace_2070764
  have hstable : (prefixWord ++ tailWord_2070764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070764).length < 2 ^ (prefixWord ++ tailWord_2070764).sum := by decide
  have hdescent : baseEnd_2070764 < baseStart_2070764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070839 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2070839 : Nat := 118140960795 + 2070839 * 2 ^ 59
def prefixEnd_2070839 : Nat := 4983230072969 + 3 ^ 40 * 2070839 * 2
def baseEnd_2070839 : Nat := 708890510050752377725927

theorem tailTrace_2070839 : CollatzResearch.WordTrace tailWord_2070839 prefixEnd_2070839 708890510050752377725927 := by
  unfold tailWord_2070839
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529703344711448989111571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50353135563140965992741047 75529703344711448989111571)
  ·
    refine ⟨113294555017067173483667357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75529703344711448989111571 113294555017067173483667357)
    ·
      refine ⟨42485458131400190056375259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113294555017067173483667357 42485458131400190056375259)
      ·
        refine ⟨63728187197100285084562889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42485458131400190056375259 63728187197100285084562889)
        ·
          refine ⟨47796140397825213813422167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63728187197100285084562889 47796140397825213813422167)
          ·
            refine ⟨71694210596737820720133251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47796140397825213813422167 71694210596737820720133251)
            ·
              refine ⟨107541315895106731080199877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71694210596737820720133251 107541315895106731080199877)
              ·
                refine ⟨20163996730332512077537477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107541315895106731080199877 20163996730332512077537477)
                ·
                  refine ⟨3780749386937346014538277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20163996730332512077537477 3780749386937346014538277)
                  ·
                    refine ⟨708890510050752377725927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780749386937346014538277 708890510050752377725927)
                    ·
                      rfl

theorem cell22_2070839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2070839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070839 prefixEnd_2070839 := by exact prefixLift 2070839
  have htrace : WordTrace (prefixWord ++ tailWord_2070839) baseStart_2070839 baseEnd_2070839 := by
    simpa [prefixWord, tailWord_2070839, baseEnd_2070839] using wordTrace_append hprefix tailTrace_2070839
  have hstable : (prefixWord ++ tailWord_2070839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070839).length < 2 ^ (prefixWord ++ tailWord_2070839).sum := by decide
  have hdescent : baseEnd_2070839 < baseStart_2070839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070841 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_2070841 : Nat := 118140960795 + 2070841 * 2 ^ 59
def prefixEnd_2070841 : Nat := 4983230072969 + 3 ^ 40 * 2070841 * 2
def baseEnd_2070841 : Nat := 708891194691625039175921

theorem tailTrace_2070841 : CollatzResearch.WordTrace tailWord_2070841 prefixEnd_2070841 708891194691625039175921 := by
  unfold tailWord_2070841
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529776290704203330684377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50353184193802802220456251 75529776290704203330684377)
  ·
    refine ⟨56647332218028152498013283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75529776290704203330684377 56647332218028152498013283)
    ·
      refine ⟨84970998327042228747019925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56647332218028152498013283 84970998327042228747019925)
      ·
        refine ⟨3983015546580104472516559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84970998327042228747019925 3983015546580104472516559)
        ·
          refine ⟨5974523319870156708774839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983015546580104472516559 5974523319870156708774839)
          ·
            refine ⟨8961784979805235063162259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974523319870156708774839 8961784979805235063162259)
            ·
              refine ⟨13442677469707852594743389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961784979805235063162259 13442677469707852594743389)
              ·
                refine ⟨5041004051140444723028771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13442677469707852594743389 5041004051140444723028771)
                ·
                  refine ⟨7561506076710667084543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041004051140444723028771 7561506076710667084543157)
                  ·
                    refine ⟨708891194691625039175921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7561506076710667084543157 708891194691625039175921)
                    ·
                      rfl

theorem cell22_2070841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_2070841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070841 prefixEnd_2070841 := by exact prefixLift 2070841
  have htrace : WordTrace (prefixWord ++ tailWord_2070841) baseStart_2070841 baseEnd_2070841 := by
    simpa [prefixWord, tailWord_2070841, baseEnd_2070841] using wordTrace_append hprefix tailTrace_2070841
  have hstable : (prefixWord ++ tailWord_2070841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070841).length < 2 ^ (prefixWord ++ tailWord_2070841).sum := by decide
  have hdescent : baseEnd_2070841 < baseStart_2070841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070856 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_2070856 : Nat := 118140960795 + 2070856 * 2 ^ 59
def prefixEnd_2070856 : Nat := 4983230072969 + 3 ^ 40 * 2070856 * 2
def baseEnd_2070856 : Nat := 708896329498170000050875

theorem tailTrace_2070856 : CollatzResearch.WordTrace tailWord_2070856 prefixEnd_2070856 708896329498170000050875 := by
  unfold tailWord_2070856
  simp only [CollatzResearch.WordTrace]
  refine ⟨37765161692824930446240211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50353548923766573928320281 37765161692824930446240211)
  ·
    refine ⟨56647742539237395669360317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37765161692824930446240211 56647742539237395669360317)
    ·
      refine ⟨21242903452214023376010119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56647742539237395669360317 21242903452214023376010119)
      ·
        refine ⟨31864355178321035064015179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21242903452214023376010119 31864355178321035064015179)
        ·
          refine ⟨47796532767481552596022769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31864355178321035064015179 47796532767481552596022769)
          ·
            refine ⟨35847399575611164447017077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47796532767481552596022769 35847399575611164447017077)
            ·
              refine ⟨3360693710213546666907851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35847399575611164447017077 3360693710213546666907851)
              ·
                refine ⟨5041040565320320000361777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360693710213546666907851 5041040565320320000361777)
                ·
                  refine ⟨3780780423990240000271333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041040565320320000361777 3780780423990240000271333)
                  ·
                    refine ⟨708896329498170000050875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780780423990240000271333 708896329498170000050875)
                    ·
                      rfl

theorem cell22_2070856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_2070856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2070856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2070856 prefixEnd_2070856 := by exact prefixLift 2070856
  have htrace : WordTrace (prefixWord ++ tailWord_2070856) baseStart_2070856 baseEnd_2070856 := by
    simpa [prefixWord, tailWord_2070856, baseEnd_2070856] using wordTrace_append hprefix tailTrace_2070856
  have hstable : (prefixWord ++ tailWord_2070856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070856).length < 2 ^ (prefixWord ++ tailWord_2070856).sum := by decide
  have hdescent : baseEnd_2070856 < baseStart_2070856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071158 : List Nat := [5, 1, 1, 2, 13]
def baseStart_2071158 : Nat := 118140960795 + 2071158 * 2 ^ 59
def prefixEnd_2071158 : Nat := 4983230072969 + 3 ^ 40 * 2071158 * 2
def baseEnd_2071158 : Nat := 2917694280946262876543

theorem tailTrace_2071158 : CollatzResearch.WordTrace tailWord_2071158 prefixEnd_2071158 2917694280946262876543 := by
  unfold tailWord_2071158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721333639409735404373383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50360892153703844313316085 4721333639409735404373383)
  ·
    refine ⟨7082000459114603106560075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721333639409735404373383 7082000459114603106560075)
    ·
      refine ⟨10623000688671904659840113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082000459114603106560075 10623000688671904659840113)
      ·
        refine ⟨7967250516503928494880085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10623000688671904659840113 7967250516503928494880085)
        ·
          refine ⟨2917694280946262876543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7967250516503928494880085 2917694280946262876543)
          ·
            rfl

theorem cell22_2071158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 13].length) (baseStart_2071158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071158 prefixEnd_2071158 := by exact prefixLift 2071158
  have htrace : WordTrace (prefixWord ++ tailWord_2071158) baseStart_2071158 baseEnd_2071158 := by
    simpa [prefixWord, tailWord_2071158, baseEnd_2071158] using wordTrace_append hprefix tailTrace_2071158
  have hstable : (prefixWord ++ tailWord_2071158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071158).length < 2 ^ (prefixWord ++ tailWord_2071158).sum := by decide
  have hdescent : baseEnd_2071158 < baseStart_2071158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071194 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_2071194 : Nat := 118140960795 + 2071194 * 2 ^ 59
def prefixEnd_2071194 : Nat := 4983230072969 + 3 ^ 40 * 2071194 * 2
def baseEnd_2071194 : Nat := 709012033805649785099839

theorem tailTrace_2071194 : CollatzResearch.WordTrace tailWord_2071194 prefixEnd_2071194 709012033805649785099839 := by
  unfold tailWord_2071194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885662814606336154571159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50361767505616896412189757 18885662814606336154571159)
  ·
    refine ⟨28328494221909504231856739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18885662814606336154571159 28328494221909504231856739)
    ·
      refine ⟨42492741332864256347785109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28328494221909504231856739 42492741332864256347785109)
      ·
        refine ⟨1991847249978012016302427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42492741332864256347785109 1991847249978012016302427)
        ·
          refine ⟨2987770874967018024453641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991847249978012016302427 2987770874967018024453641)
          ·
            refine ⟨2240828156225263518340231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987770874967018024453641 2240828156225263518340231)
            ·
              refine ⟨3361242234337895277510347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240828156225263518340231 3361242234337895277510347)
              ·
                refine ⟨5041863351506842916265521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361242234337895277510347 5041863351506842916265521)
                ·
                  refine ⟨3781397513630132187199141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041863351506842916265521 3781397513630132187199141)
                  ·
                    refine ⟨709012033805649785099839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781397513630132187199141 709012033805649785099839)
                    ·
                      rfl

theorem cell22_2071194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_2071194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071194 prefixEnd_2071194 := by exact prefixLift 2071194
  have htrace : WordTrace (prefixWord ++ tailWord_2071194) baseStart_2071194 baseEnd_2071194 := by
    simpa [prefixWord, tailWord_2071194, baseEnd_2071194] using wordTrace_append hprefix tailTrace_2071194
  have hstable : (prefixWord ++ tailWord_2071194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071194).length < 2 ^ (prefixWord ++ tailWord_2071194).sum := by decide
  have hdescent : baseEnd_2071194 < baseStart_2071194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071267 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 1, 4]
def baseStart_2071267 : Nat := 118140960795 + 2071267 * 2 ^ 59
def prefixEnd_2071267 : Nat := 4983230072969 + 3 ^ 40 * 2071267 * 2
def baseEnd_2071267 : Nat := 709037023197501928024615

theorem tailTrace_2071267 : CollatzResearch.WordTrace tailWord_2071267 prefixEnd_2071267 709037023197501928024615 := by
  unfold tailWord_2071267
  simp only [CollatzResearch.WordTrace]
  refine ⟨75545313787160878085692055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50363542524773918723794703 75545313787160878085692055)
  ·
    refine ⟨113317970680741317128538083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75545313787160878085692055 113317970680741317128538083)
    ·
      refine ⟨169976956021111975692807125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113317970680741317128538083 169976956021111975692807125)
      ·
        refine ⟨3983834906744811930300167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 169976956021111975692807125 3983834906744811930300167)
        ·
          refine ⟨5975752360117217895450251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983834906744811930300167 5975752360117217895450251)
          ·
            refine ⟨8963628540175826843175377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975752360117217895450251 8963628540175826843175377)
            ·
              refine ⟨6722721405131870132381533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8963628540175826843175377 6722721405131870132381533)
              ·
                refine ⟨2521020526924451299643075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6722721405131870132381533 2521020526924451299643075)
                ·
                  refine ⟨3781530790386676949464613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521020526924451299643075 3781530790386676949464613)
                  ·
                    refine ⟨709037023197501928024615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781530790386676949464613 709037023197501928024615)
                    ·
                      rfl

theorem cell22_2071267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_2071267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071267 prefixEnd_2071267 := by exact prefixLift 2071267
  have htrace : WordTrace (prefixWord ++ tailWord_2071267) baseStart_2071267 baseEnd_2071267 := by
    simpa [prefixWord, tailWord_2071267, baseEnd_2071267] using wordTrace_append hprefix tailTrace_2071267
  have hstable : (prefixWord ++ tailWord_2071267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071267).length < 2 ^ (prefixWord ++ tailWord_2071267).sum := by decide
  have hdescent : baseEnd_2071267 < baseStart_2071267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071280 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_2071280 : Nat := 118140960795 + 2071280 * 2 ^ 59
def prefixEnd_2071280 : Nat := 4983230072969 + 3 ^ 40 * 2071280 * 2
def baseEnd_2071280 : Nat := 709041473363174227449575

theorem tailTrace_2071280 : CollatzResearch.WordTrace tailWord_2071280 prefixEnd_2071280 709041473363174227449575 := by
  unfold tailWord_2071280
  simp only [CollatzResearch.WordTrace]
  refine ⟨37772893968056890652957647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50363858624075854203943529 37772893968056890652957647)
  ·
    refine ⟨56659340952085335979436471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37772893968056890652957647 56659340952085335979436471)
    ·
      refine ⟨84989011428128003969154707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56659340952085335979436471 84989011428128003969154707)
      ·
        refine ⟨127483517142192005953732061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84989011428128003969154707 127483517142192005953732061)
        ·
          refine ⟨47806318928322002232649523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127483517142192005953732061 47806318928322002232649523)
          ·
            refine ⟨71709478392483003348974285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47806318928322002232649523 71709478392483003348974285)
            ·
              refine ⟨26891054397181126255865357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71709478392483003348974285 26891054397181126255865357)
              ·
                refine ⟨10084145398942922345949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26891054397181126255865357 10084145398942922345949509)
                ·
                  refine ⟨1890777262301797939865533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10084145398942922345949509 1890777262301797939865533)
                  ·
                    refine ⟨709041473363174227449575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1890777262301797939865533 709041473363174227449575)
                    ·
                      rfl

theorem cell22_2071280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_2071280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071280 prefixEnd_2071280 := by exact prefixLift 2071280
  have htrace : WordTrace (prefixWord ++ tailWord_2071280) baseStart_2071280 baseEnd_2071280 := by
    simpa [prefixWord, tailWord_2071280, baseEnd_2071280] using wordTrace_append hprefix tailTrace_2071280
  have hstable : (prefixWord ++ tailWord_2071280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071280).length < 2 ^ (prefixWord ++ tailWord_2071280).sum := by decide
  have hdescent : baseEnd_2071280 < baseStart_2071280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071282 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_2071282 : Nat := 118140960795 + 2071282 * 2 ^ 59
def prefixEnd_2071282 : Nat := 4983230072969 + 3 ^ 40 * 2071282 * 2
def baseEnd_2071282 : Nat := 236347386001348962966523

theorem tailTrace_2071282 : CollatzResearch.WordTrace tailWord_2071282 prefixEnd_2071282 236347386001348962966523 := by
  unfold tailWord_2071282
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886465220526633911872025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50363907254737690431658733 18886465220526633911872025)
  ·
    refine ⟨14164848915394975433904019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18886465220526633911872025 14164848915394975433904019)
    ·
      refine ⟨21247273373092463150856029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14164848915394975433904019 21247273373092463150856029)
      ·
        refine ⟨7967727514909673681571011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21247273373092463150856029 7967727514909673681571011)
        ·
          refine ⟨11951591272364510522356517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967727514909673681571011 11951591272364510522356517)
          ·
            refine ⟨2240923363568345722941847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11951591272364510522356517 2240923363568345722941847)
            ·
              refine ⟨3361385045352518584412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240923363568345722941847 3361385045352518584412771)
              ·
                refine ⟨5042077568028777876619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361385045352518584412771 5042077568028777876619157)
                ·
                  refine ⟨236347386001348962966523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5042077568028777876619157 236347386001348962966523)
                  ·
                    rfl

theorem cell22_2071282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_2071282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071282 prefixEnd_2071282 := by exact prefixLift 2071282
  have htrace : WordTrace (prefixWord ++ tailWord_2071282) baseStart_2071282 baseEnd_2071282 := by
    simpa [prefixWord, tailWord_2071282, baseEnd_2071282] using wordTrace_append hprefix tailTrace_2071282
  have hstable : (prefixWord ++ tailWord_2071282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071282).length < 2 ^ (prefixWord ++ tailWord_2071282).sum := by decide
  have hdescent : baseEnd_2071282 < baseStart_2071282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071314 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2071314 : Nat := 118140960795 + 2071314 * 2 ^ 59
def prefixEnd_2071314 : Nat := 4983230072969 + 3 ^ 40 * 2071314 * 2
def baseEnd_2071314 : Nat := 709053112258009472099471

theorem tailTrace_2071314 : CollatzResearch.WordTrace tailWord_2071314 prefixEnd_2071314 709053112258009472099471 := by
  unfold tailWord_2071314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886757004497651278163249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50364685345327070075101997 18886757004497651278163249)
  ·
    refine ⟨14165067753373238458622437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18886757004497651278163249 14165067753373238458622437)
    ·
      refine ⟨2655950203757482210991707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14165067753373238458622437 2655950203757482210991707)
      ·
        refine ⟨3983925305636223316487561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655950203757482210991707 3983925305636223316487561)
        ·
          refine ⟨2987943979227167487365671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983925305636223316487561 2987943979227167487365671)
          ·
            refine ⟨4481915968840751231048507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987943979227167487365671 4481915968840751231048507)
            ·
              refine ⟨6722873953261126846572761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481915968840751231048507 6722873953261126846572761)
              ·
                refine ⟨5042155464945845134929571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722873953261126846572761 5042155464945845134929571)
                ·
                  refine ⟨7563233197418767702394357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042155464945845134929571 7563233197418767702394357)
                  ·
                    refine ⟨709053112258009472099471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7563233197418767702394357 709053112258009472099471)
                    ·
                      rfl

theorem cell22_2071314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2071314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071314 prefixEnd_2071314 := by exact prefixLift 2071314
  have htrace : WordTrace (prefixWord ++ tailWord_2071314) baseStart_2071314 baseEnd_2071314 := by
    simpa [prefixWord, tailWord_2071314, baseEnd_2071314] using wordTrace_append hprefix tailTrace_2071314
  have hstable : (prefixWord ++ tailWord_2071314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071314).length < 2 ^ (prefixWord ++ tailWord_2071314).sum := by decide
  have hdescent : baseEnd_2071314 < baseStart_2071314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071323 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_2071323 : Nat := 118140960795 + 2071323 * 2 ^ 59
def prefixEnd_2071323 : Nat := 4983230072969 + 3 ^ 40 * 2071323 * 2
def baseEnd_2071323 : Nat := 709056193141936448624443

theorem tailTrace_2071323 : CollatzResearch.WordTrace tailWord_2071323 prefixEnd_2071323 709056193141936448624443 := by
  unfold tailWord_2071323
  simp only [CollatzResearch.WordTrace]
  refine ⟨75547356274957999649730623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50364904183305333099820415 75547356274957999649730623)
  ·
    refine ⟨113321034412436999474595935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75547356274957999649730623 113321034412436999474595935)
    ·
      refine ⟨169981551618655499211893903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113321034412436999474595935 169981551618655499211893903)
      ·
        refine ⟨254972327427983248817840855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169981551618655499211893903 254972327427983248817840855)
        ·
          refine ⟨382458491141974873226761283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254972327427983248817840855 382458491141974873226761283)
          ·
            refine ⟨573687736712962309840141925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382458491141974873226761283 573687736712962309840141925)
            ·
              refine ⟨107566450633680433095026611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573687736712962309840141925 107566450633680433095026611)
              ·
                refine ⟨161349675950520649642539917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107566450633680433095026611 161349675950520649642539917)
                ·
                  refine ⟨60506128481445243615952469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161349675950520649642539917 60506128481445243615952469)
                  ·
                    refine ⟨709056193141936448624443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60506128481445243615952469 709056193141936448624443)
                    ·
                      rfl

theorem cell22_2071323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_2071323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071323 prefixEnd_2071323 := by exact prefixLift 2071323
  have htrace : WordTrace (prefixWord ++ tailWord_2071323) baseStart_2071323 baseEnd_2071323 := by
    simpa [prefixWord, tailWord_2071323, baseEnd_2071323] using wordTrace_append hprefix tailTrace_2071323
  have hstable : (prefixWord ++ tailWord_2071323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071323).length < 2 ^ (prefixWord ++ tailWord_2071323).sum := by decide
  have hdescent : baseEnd_2071323 < baseStart_2071323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071406 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_2071406 : Nat := 118140960795 + 2071406 * 2 ^ 59
def prefixEnd_2071406 : Nat := 4983230072969 + 3 ^ 40 * 2071406 * 2
def baseEnd_2071406 : Nat := 236361535246050632933063

theorem tailTrace_2071406 : CollatzResearch.WordTrace tailWord_2071406 prefixEnd_2071406 236361535246050632933063 := by
  unfold tailWord_2071406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443797941707163103125259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50366922355771536550001381 9443797941707163103125259)
  ·
    refine ⟨14165696912560744654687889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9443797941707163103125259 14165696912560744654687889)
    ·
      refine ⟨10624272684420558491015917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14165696912560744654687889 10624272684420558491015917)
      ·
        refine ⟨3984102256657709434130969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10624272684420558491015917 3984102256657709434130969)
        ·
          refine ⟨2988076692493282075598227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3984102256657709434130969 2988076692493282075598227)
          ·
            refine ⟨4482115038739923113397341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988076692493282075598227 4482115038739923113397341)
            ·
              refine ⟨1680793139527471167524003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4482115038739923113397341 1680793139527471167524003)
              ·
                refine ⟨2521189709291206751286005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680793139527471167524003 2521189709291206751286005)
                ·
                  refine ⟨236361535246050632933063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521189709291206751286005 236361535246050632933063)
                  ·
                    rfl

theorem cell22_2071406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_2071406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071406 prefixEnd_2071406 := by exact prefixLift 2071406
  have htrace : WordTrace (prefixWord ++ tailWord_2071406) baseStart_2071406 baseEnd_2071406 := by
    simpa [prefixWord, tailWord_2071406, baseEnd_2071406] using wordTrace_append hprefix tailTrace_2071406
  have hstable : (prefixWord ++ tailWord_2071406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071406).length < 2 ^ (prefixWord ++ tailWord_2071406).sum := by decide
  have hdescent : baseEnd_2071406 < baseStart_2071406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071445 : List Nat := [1, 3, 2, 1, 1, 4, 10]
def baseStart_2071445 : Nat := 118140960795 + 2071445 * 2 ^ 59
def prefixEnd_2071445 : Nat := 4983230072969 + 3 ^ 40 * 2071445 * 2
def baseEnd_2071445 : Nat := 26262887267969214706447

theorem tailTrace_2071445 : CollatzResearch.WordTrace tailWord_2071445 prefixEnd_2071445 26262887267969214706447 := by
  unfold tailWord_2071445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75551805980516014485671789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50367870653677342990447859 75551805980516014485671789)
  ·
    refine ⟨28331927242693505432126921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75551805980516014485671789 28331927242693505432126921)
    ·
      refine ⟨21248945432020129074095191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28331927242693505432126921 21248945432020129074095191)
      ·
        refine ⟨31873418148030193611142787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21248945432020129074095191 31873418148030193611142787)
        ·
          refine ⟨47810127222045290416714181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31873418148030193611142787 47810127222045290416714181)
          ·
            refine ⟨8964398854133491953133909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47810127222045290416714181 8964398854133491953133909)
            ·
              refine ⟨26262887267969214706447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8964398854133491953133909 26262887267969214706447)
              ·
                rfl

theorem cell22_2071445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 10].length) (baseStart_2071445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071445 prefixEnd_2071445 := by exact prefixLift 2071445
  have htrace : WordTrace (prefixWord ++ tailWord_2071445) baseStart_2071445 baseEnd_2071445 := by
    simpa [prefixWord, tailWord_2071445, baseEnd_2071445] using wordTrace_append hprefix tailTrace_2071445
  have hstable : (prefixWord ++ tailWord_2071445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071445).length < 2 ^ (prefixWord ++ tailWord_2071445).sum := by decide
  have hdescent : baseEnd_2071445 < baseStart_2071445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071447 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2071447 : Nat := 118140960795 + 2071447 * 2 ^ 59
def prefixEnd_2071447 : Nat := 4983230072969 + 3 ^ 40 * 2071447 * 2
def baseEnd_2071447 : Nat := 709098640876041458524063

theorem tailTrace_2071447 : CollatzResearch.WordTrace tailWord_2071447 prefixEnd_2071447 709098640876041458524063 := by
  unfold tailWord_2071447
  simp only [CollatzResearch.WordTrace]
  refine ⟨75551878926508768827244595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50367919284339179218163063 75551878926508768827244595)
  ·
    refine ⟨113327818389763153240866893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75551878926508768827244595 113327818389763153240866893)
    ·
      refine ⟨42497931896161182465325085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113327818389763153240866893 42497931896161182465325085)
      ·
        refine ⟨15936724461060443424496907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42497931896161182465325085 15936724461060443424496907)
        ·
          refine ⟨23905086691590665136745361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936724461060443424496907 23905086691590665136745361)
          ·
            refine ⟨17928815018692998852559021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23905086691590665136745361 17928815018692998852559021)
            ·
              refine ⟨6723305632009874569709633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17928815018692998852559021 6723305632009874569709633)
              ·
                refine ⟨5042479224007405927282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723305632009874569709633 5042479224007405927282225)
                ·
                  refine ⟨3781859418005554445461669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042479224007405927282225 3781859418005554445461669)
                  ·
                    refine ⟨709098640876041458524063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781859418005554445461669 709098640876041458524063)
                    ·
                      rfl

theorem cell22_2071447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2071447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071447 prefixEnd_2071447 := by exact prefixLift 2071447
  have htrace : WordTrace (prefixWord ++ tailWord_2071447) baseStart_2071447 baseEnd_2071447 := by
    simpa [prefixWord, tailWord_2071447, baseEnd_2071447] using wordTrace_append hprefix tailTrace_2071447
  have hstable : (prefixWord ++ tailWord_2071447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071447).length < 2 ^ (prefixWord ++ tailWord_2071447).sum := by decide
  have hdescent : baseEnd_2071447 < baseStart_2071447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071475 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_2071475 : Nat := 118140960795 + 2071475 * 2 ^ 59
def prefixEnd_2071475 : Nat := 4983230072969 + 3 ^ 40 * 2071475 * 2
def baseEnd_2071475 : Nat := 709108225848258718823977

theorem tailTrace_2071475 : CollatzResearch.WordTrace tailWord_2071475 prefixEnd_2071475 709108225848258718823977 := by
  unfold tailWord_2071475
  simp only [CollatzResearch.WordTrace]
  refine ⟨75552900170407329609263879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50368600113604886406175919 75552900170407329609263879)
  ·
    refine ⟨113329350255610994413895819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75552900170407329609263879 113329350255610994413895819)
    ·
      refine ⟨169994025383416491620843729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113329350255610994413895819 169994025383416491620843729)
      ·
        refine ⟨127495519037562368715632797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169994025383416491620843729 127495519037562368715632797)
        ·
          refine ⟨47810819639085888268362299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127495519037562368715632797 47810819639085888268362299)
          ·
            refine ⟨71716229458628832402543449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47810819639085888268362299 71716229458628832402543449)
            ·
              refine ⟨53787172093971624301907587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71716229458628832402543449 53787172093971624301907587)
              ·
                refine ⟨80680758140957436452861381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53787172093971624301907587 80680758140957436452861381)
                ·
                  refine ⟨15127642151429519334911509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80680758140957436452861381 15127642151429519334911509)
                  ·
                    refine ⟨709108225848258718823977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15127642151429519334911509 709108225848258718823977)
                    ·
                      rfl

theorem cell22_2071475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_2071475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071475 prefixEnd_2071475 := by exact prefixLift 2071475
  have htrace : WordTrace (prefixWord ++ tailWord_2071475) baseStart_2071475 baseEnd_2071475 := by
    simpa [prefixWord, tailWord_2071475, baseEnd_2071475] using wordTrace_append hprefix tailTrace_2071475
  have hstable : (prefixWord ++ tailWord_2071475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071475).length < 2 ^ (prefixWord ++ tailWord_2071475).sum := by decide
  have hdescent : baseEnd_2071475 < baseStart_2071475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071614 : List Nat := [4, 2, 1, 3, 1, 1, 10]
def baseStart_2071614 : Nat := 118140960795 + 2071614 * 2 ^ 59
def prefixEnd_2071614 : Nat := 4983230072969 + 3 ^ 40 * 2071614 * 2
def baseEnd_2071614 : Nat := 26265029940329951466613

theorem tailTrace_2071614 : CollatzResearch.WordTrace tailWord_2071614 prefixEnd_2071614 26265029940329951466613 := by
  unfold tailWord_2071614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444746239612969543571737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50371979944602504232382597 9444746239612969543571737)
  ·
    refine ⟨7083559679709727157678803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9444746239612969543571737 7083559679709727157678803)
    ·
      refine ⟨10625339519564590736518205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7083559679709727157678803 10625339519564590736518205)
      ·
        refine ⟨3984502319836721526194327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10625339519564590736518205 3984502319836721526194327)
        ·
          refine ⟨5976753479755082289291491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984502319836721526194327 5976753479755082289291491)
          ·
            refine ⟨8965130219632623433937237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976753479755082289291491 8965130219632623433937237)
            ·
              refine ⟨26265029940329951466613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8965130219632623433937237 26265029940329951466613)
              ·
                rfl

theorem cell22_2071614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 10].length) (baseStart_2071614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071614 prefixEnd_2071614 := by exact prefixLift 2071614
  have htrace : WordTrace (prefixWord ++ tailWord_2071614) baseStart_2071614 baseEnd_2071614 := by
    simpa [prefixWord, tailWord_2071614, baseEnd_2071614] using wordTrace_append hprefix tailTrace_2071614
  have hstable : (prefixWord ++ tailWord_2071614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071614).length < 2 ^ (prefixWord ++ tailWord_2071614).sum := by decide
  have hdescent : baseEnd_2071614 < baseStart_2071614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071642 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_2071642 : Nat := 118140960795 + 2071642 * 2 ^ 59
def prefixEnd_2071642 : Nat := 4983230072969 + 3 ^ 40 * 2071642 * 2
def baseEnd_2071642 : Nat := 236388464453708649966155

theorem tailTrace_2071642 : CollatzResearch.WordTrace tailWord_2071642 prefixEnd_2071642 236388464453708649966155 := by
  unfold tailWord_2071642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889747790200579282648295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50372660773868211420395453 18889747790200579282648295)
  ·
    refine ⟨28334621685300868923972443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889747790200579282648295 28334621685300868923972443)
    ·
      refine ⟨42501932527951303385958665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28334621685300868923972443 42501932527951303385958665)
      ·
        refine ⟨31876449395963477539468999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42501932527951303385958665 31876449395963477539468999)
        ·
          refine ⟨47814674093945216309203499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31876449395963477539468999 47814674093945216309203499)
          ·
            refine ⟨71722011140917824463805249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47814674093945216309203499 71722011140917824463805249)
            ·
              refine ⟨53791508355688368347853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71722011140917824463805249 53791508355688368347853937)
              ·
                refine ⟨40343631266766276260890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53791508355688368347853937 40343631266766276260890453)
                ·
                  refine ⟨236388464453708649966155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40343631266766276260890453 236388464453708649966155)
                  ·
                    rfl

theorem cell22_2071642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_2071642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071642 prefixEnd_2071642 := by exact prefixLift 2071642
  have htrace : WordTrace (prefixWord ++ tailWord_2071642) baseStart_2071642 baseEnd_2071642 := by
    simpa [prefixWord, tailWord_2071642, baseEnd_2071642] using wordTrace_append hprefix tailTrace_2071642
  have hstable : (prefixWord ++ tailWord_2071642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071642).length < 2 ^ (prefixWord ++ tailWord_2071642).sum := by decide
  have hdescent : baseEnd_2071642 < baseStart_2071642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071689 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_2071689 : Nat := 118140960795 + 2071689 * 2 ^ 59
def prefixEnd_2071689 : Nat := 4983230072969 + 3 ^ 40 * 2071689 * 2
def baseEnd_2071689 : Nat := 709181482421633493973321

theorem tailTrace_2071689 : CollatzResearch.WordTrace tailWord_2071689 prefixEnd_2071689 709181482421633493973321 := by
  unfold tailWord_2071689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75560705391632044157554121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50373803594421362771702747 75560705391632044157554121)
  ·
    refine ⟨56670529043724033118165591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75560705391632044157554121 56670529043724033118165591)
    ·
      refine ⟨85005793565586049677248387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56670529043724033118165591 85005793565586049677248387)
      ·
        refine ⟨127508690348379074515872581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85005793565586049677248387 127508690348379074515872581)
        ·
          refine ⟨23907879440321076471726109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127508690348379074515872581 23907879440321076471726109)
          ·
            refine ⟨8965454790120403676897291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23907879440321076471726109 8965454790120403676897291)
            ·
              refine ⟨13448182185180605515345937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965454790120403676897291 13448182185180605515345937)
              ·
                refine ⟨10086136638885454136509453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13448182185180605515345937 10086136638885454136509453)
                ·
                  refine ⟨3782301239582045301191045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086136638885454136509453 3782301239582045301191045)
                  ·
                    refine ⟨709181482421633493973321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782301239582045301191045 709181482421633493973321)
                    ·
                      rfl

theorem cell22_2071689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_2071689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071689 prefixEnd_2071689 := by exact prefixLift 2071689
  have htrace : WordTrace (prefixWord ++ tailWord_2071689) baseStart_2071689 baseEnd_2071689 := by
    simpa [prefixWord, tailWord_2071689, baseEnd_2071689] using wordTrace_append hprefix tailTrace_2071689
  have hstable : (prefixWord ++ tailWord_2071689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071689).length < 2 ^ (prefixWord ++ tailWord_2071689).sum := by decide
  have hdescent : baseEnd_2071689 < baseStart_2071689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071704 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_2071704 : Nat := 118140960795 + 2071704 * 2 ^ 59
def prefixEnd_2071704 : Nat := 4983230072969 + 3 ^ 40 * 2071704 * 2
def baseEnd_2071704 : Nat := 236395539076059484949425

theorem tailTrace_2071704 : CollatzResearch.WordTrace tailWord_2071704 prefixEnd_2071704 236395539076059484949425 := by
  unfold tailWord_2071704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37780626243288850859675083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50374168324385134479566777 37780626243288850859675083)
  ·
    refine ⟨56670939364933276289512625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37780626243288850859675083 56670939364933276289512625)
    ·
      refine ⟨42503204523699957217134469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56670939364933276289512625 42503204523699957217134469)
      ·
        refine ⟨7969350848193741978212713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42503204523699957217134469 7969350848193741978212713)
        ·
          refine ⟨5977013136145306483659535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7969350848193741978212713 5977013136145306483659535)
          ·
            refine ⟨8965519704217959725489303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977013136145306483659535 8965519704217959725489303)
            ·
              refine ⟨13448279556326939588233955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965519704217959725489303 13448279556326939588233955)
              ·
                refine ⟨20172419334490409382350933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448279556326939588233955 20172419334490409382350933)
                ·
                  refine ⟨236395539076059484949425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20172419334490409382350933 236395539076059484949425)
                  ·
                    rfl

theorem cell22_2071704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_2071704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071704 prefixEnd_2071704 := by exact prefixLift 2071704
  have htrace : WordTrace (prefixWord ++ tailWord_2071704) baseStart_2071704 baseEnd_2071704 := by
    simpa [prefixWord, tailWord_2071704, baseEnd_2071704] using wordTrace_append hprefix tailTrace_2071704
  have hstable : (prefixWord ++ tailWord_2071704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071704).length < 2 ^ (prefixWord ++ tailWord_2071704).sum := by decide
  have hdescent : baseEnd_2071704 < baseStart_2071704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071706 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_2071706 : Nat := 118140960795 + 2071706 * 2 ^ 59
def prefixEnd_2071706 : Nat := 4983230072969 + 3 ^ 40 * 2071706 * 2
def baseEnd_2071706 : Nat := 709187301869051116298269

theorem tailTrace_2071706 : CollatzResearch.WordTrace tailWord_2071706 prefixEnd_2071706 709187301869051116298269 := by
  unfold tailWord_2071706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890331358142614015230743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50374216955046970707281981 18890331358142614015230743)
  ·
    refine ⟨28335497037213921022846115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18890331358142614015230743 28335497037213921022846115)
    ·
      refine ⟨42503245555820881534269173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28335497037213921022846115 42503245555820881534269173)
      ·
        refine ⟨3984679270858207643837735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42503245555820881534269173 3984679270858207643837735)
        ·
          refine ⟨5977018906287311465756603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984679270858207643837735 5977018906287311465756603)
          ·
            refine ⟨8965528359430967198634905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977018906287311465756603 8965528359430967198634905)
            ·
              refine ⟨6724146269573225398976179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965528359430967198634905 6724146269573225398976179)
              ·
                refine ⟨10086219404359838098464269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724146269573225398976179 10086219404359838098464269)
                ·
                  refine ⟨3782332276634939286924101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086219404359838098464269 3782332276634939286924101)
                  ·
                    refine ⟨709187301869051116298269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782332276634939286924101 709187301869051116298269)
                    ·
                      rfl

theorem cell22_2071706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_2071706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071706 prefixEnd_2071706 := by exact prefixLift 2071706
  have htrace : WordTrace (prefixWord ++ tailWord_2071706) baseStart_2071706 baseEnd_2071706 := by
    simpa [prefixWord, tailWord_2071706, baseEnd_2071706] using wordTrace_append hprefix tailTrace_2071706
  have hstable : (prefixWord ++ tailWord_2071706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071706).length < 2 ^ (prefixWord ++ tailWord_2071706).sum := by decide
  have hdescent : baseEnd_2071706 < baseStart_2071706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071736 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_2071736 : Nat := 118140960795 + 2071736 * 2 ^ 59
def prefixEnd_2071736 : Nat := 4983230072969 + 3 ^ 40 * 2071736 * 2
def baseEnd_2071736 : Nat := 709197571482141038048177

theorem tailTrace_2071736 : CollatzResearch.WordTrace tailWord_2071736 prefixEnd_2071736 709197571482141038048177 := by
  unfold tailWord_2071736
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781209811230885592257531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50374946414974514123010041 37781209811230885592257531)
  ·
    refine ⟨56671814716846328388386297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37781209811230885592257531 56671814716846328388386297)
    ·
      refine ⟨42503861037634746291289723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56671814716846328388386297 42503861037634746291289723)
      ·
        refine ⟨63755791556452119436934585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42503861037634746291289723 63755791556452119436934585)
        ·
          refine ⟨47816843667339089577700939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63755791556452119436934585 47816843667339089577700939)
          ·
            refine ⟨71725265501008634366551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47816843667339089577700939 71725265501008634366551409)
            ·
              refine ⟨53793949125756475774913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71725265501008634366551409 53793949125756475774913557)
              ·
                refine ⟨2521591365269834801949073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53793949125756475774913557 2521591365269834801949073)
                ·
                  refine ⟨1891193523952376101461805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521591365269834801949073 1891193523952376101461805)
                  ·
                    refine ⟨709197571482141038048177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891193523952376101461805 709197571482141038048177)
                    ·
                      rfl

theorem cell22_2071736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_2071736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071736 prefixEnd_2071736 := by exact prefixLift 2071736
  have htrace : WordTrace (prefixWord ++ tailWord_2071736) baseStart_2071736 baseEnd_2071736 := by
    simpa [prefixWord, tailWord_2071736, baseEnd_2071736] using wordTrace_append hprefix tailTrace_2071736
  have hstable : (prefixWord ++ tailWord_2071736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071736).length < 2 ^ (prefixWord ++ tailWord_2071736).sum := by decide
  have hdescent : baseEnd_2071736 < baseStart_2071736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071757 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2071757 : Nat := 118140960795 + 2071757 * 2 ^ 59
def prefixEnd_2071757 : Nat := 4983230072969 + 3 ^ 40 * 2071757 * 2
def baseEnd_2071757 : Nat := 709204760211303983273113

theorem tailTrace_2071757 : CollatzResearch.WordTrace tailWord_2071757 prefixEnd_2071757 709204760211303983273113 := by
  unfold tailWord_2071757
  simp only [CollatzResearch.WordTrace]
  refine ⟨75563185555385691771029525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50375457036923794514019683 75563185555385691771029525)
  ·
    refine ⟨3542024322908704301767009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75563185555385691771029525 3542024322908704301767009)
    ·
      refine ⟨2656518242181528226325257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3542024322908704301767009 2656518242181528226325257)
      ·
        refine ⟨1992388681636146169743943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2656518242181528226325257 1992388681636146169743943)
        ·
          refine ⟨2988583022454219254615915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992388681636146169743943 2988583022454219254615915)
          ·
            refine ⟨4482874533681328881923873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988583022454219254615915 4482874533681328881923873)
            ·
              refine ⟨3362155900260996661442905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482874533681328881923873 3362155900260996661442905)
              ·
                refine ⟨2521616925195747496082179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362155900260996661442905 2521616925195747496082179)
                ·
                  refine ⟨3782425387793621244123269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521616925195747496082179 3782425387793621244123269)
                  ·
                    refine ⟨709204760211303983273113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782425387793621244123269 709204760211303983273113)
                    ·
                      rfl

theorem cell22_2071757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2071757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071757 prefixEnd_2071757 := by exact prefixLift 2071757
  have htrace : WordTrace (prefixWord ++ tailWord_2071757) baseStart_2071757 baseEnd_2071757 := by
    simpa [prefixWord, tailWord_2071757, baseEnd_2071757] using wordTrace_append hprefix tailTrace_2071757
  have hstable : (prefixWord ++ tailWord_2071757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071757).length < 2 ^ (prefixWord ++ tailWord_2071757).sum := by decide
  have hdescent : baseEnd_2071757 < baseStart_2071757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071783 : List Nat := [1, 1, 5, 3, 3, 1, 8]
def baseStart_2071783 : Nat := 118140960795 + 2071783 * 2 ^ 59
def prefixEnd_2071783 : Nat := 4983230072969 + 3 ^ 40 * 2071783 * 2
def baseEnd_2071783 : Nat := 26267172612690688226779

theorem tailTrace_2071783 : CollatzResearch.WordTrace tailWord_2071783 prefixEnd_2071783 26267172612690688226779 := by
  unfold tailWord_2071783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75564133853291498211476003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50376089235527665474317335 75564133853291498211476003)
  ·
    refine ⟨113346200779937247317214005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75564133853291498211476003 113346200779937247317214005)
    ·
      refine ⟨10626206323119116935988813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113346200779937247317214005 10626206323119116935988813)
      ·
        refine ⟨3984827371169668850995805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10626206323119116935988813 3984827371169668850995805)
        ·
          refine ⟨1494310264188625819123427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3984827371169668850995805 1494310264188625819123427)
          ·
            refine ⟨2241465396282938728685141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494310264188625819123427 2241465396282938728685141)
            ·
              refine ⟨26267172612690688226779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2241465396282938728685141 26267172612690688226779)
              ·
                rfl

theorem cell22_2071783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 8].length) (baseStart_2071783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071783 prefixEnd_2071783 := by exact prefixLift 2071783
  have htrace : WordTrace (prefixWord ++ tailWord_2071783) baseStart_2071783 baseEnd_2071783 := by
    simpa [prefixWord, tailWord_2071783, baseEnd_2071783] using wordTrace_append hprefix tailTrace_2071783
  have hstable : (prefixWord ++ tailWord_2071783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071783).length < 2 ^ (prefixWord ++ tailWord_2071783).sum := by decide
  have hdescent : baseEnd_2071783 < baseStart_2071783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071811 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 5]
def baseStart_2071811 : Nat := 118140960795 + 2071811 * 2 ^ 59
def prefixEnd_2071811 : Nat := 4983230072969 + 3 ^ 40 * 2071811 * 2
def baseEnd_2071811 : Nat := 236407748504955280807649

theorem tailTrace_2071811 : CollatzResearch.WordTrace tailWord_2071811 prefixEnd_2071811 236407748504955280807649 := by
  unfold tailWord_2071811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75565155097190058993495287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50376770064793372662330191 75565155097190058993495287)
  ·
    refine ⟨113347732645785088490242931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75565155097190058993495287 113347732645785088490242931)
    ·
      refine ⟨170021598968677632735364397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113347732645785088490242931 170021598968677632735364397)
      ·
        refine ⟨63758099613254112275761649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170021598968677632735364397 63758099613254112275761649)
        ·
          refine ⟨47818574709940584206821237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63758099613254112275761649 47818574709940584206821237)
          ·
            refine ⟨4482991379056929769389491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47818574709940584206821237 4482991379056929769389491)
            ·
              refine ⟨6724487068585394654084237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482991379056929769389491 6724487068585394654084237)
              ·
                refine ⟨2521682650719522995281589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6724487068585394654084237 2521682650719522995281589)
                ·
                  refine ⟨236407748504955280807649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521682650719522995281589 236407748504955280807649)
                  ·
                    rfl

theorem cell22_2071811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].length) (baseStart_2071811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071811 prefixEnd_2071811 := by exact prefixLift 2071811
  have htrace : WordTrace (prefixWord ++ tailWord_2071811) baseStart_2071811 baseEnd_2071811 := by
    simpa [prefixWord, tailWord_2071811, baseEnd_2071811] using wordTrace_append hprefix tailTrace_2071811
  have hstable : (prefixWord ++ tailWord_2071811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071811).length < 2 ^ (prefixWord ++ tailWord_2071811).sum := by decide
  have hdescent : baseEnd_2071811 < baseStart_2071811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071871 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_2071871 : Nat := 118140960795 + 2071871 * 2 ^ 59
def prefixEnd_2071871 : Nat := 4983230072969 + 3 ^ 40 * 2071871 * 2
def baseEnd_2071871 : Nat := 709243784741045685922763

theorem tailTrace_2071871 : CollatzResearch.WordTrace tailWord_2071871 prefixEnd_2071871 709243784741045685922763 := by
  unfold tailWord_2071871
  simp only [CollatzResearch.WordTrace]
  refine ⟨75567343476972689240679467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50378228984648459493786311 75567343476972689240679467)
  ·
    refine ⟨113351015215459033861019201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75567343476972689240679467 113351015215459033861019201)
    ·
      refine ⟨85013261411594275395764401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113351015215459033861019201 85013261411594275395764401)
      ·
        refine ⟨63759946058695706546823301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85013261411594275395764401 63759946058695706546823301)
        ·
          refine ⟨11954989886005444977529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63759946058695706546823301 11954989886005444977529369)
          ·
            refine ⟨8966242414504083733147027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11954989886005444977529369 8966242414504083733147027)
            ·
              refine ⟨13449363621756125599720541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966242414504083733147027 13449363621756125599720541)
              ·
                refine ⟨5043511358158547099895203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449363621756125599720541 5043511358158547099895203)
                ·
                  refine ⟨7565267037237820649842805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043511358158547099895203 7565267037237820649842805)
                  ·
                    refine ⟨709243784741045685922763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7565267037237820649842805 709243784741045685922763)
                    ·
                      rfl

theorem cell22_2071871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_2071871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071871 prefixEnd_2071871 := by exact prefixLift 2071871
  have htrace : WordTrace (prefixWord ++ tailWord_2071871) baseStart_2071871 baseEnd_2071871 := by
    simpa [prefixWord, tailWord_2071871, baseEnd_2071871] using wordTrace_append hprefix tailTrace_2071871
  have hstable : (prefixWord ++ tailWord_2071871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071871).length < 2 ^ (prefixWord ++ tailWord_2071871).sum := by decide
  have hdescent : baseEnd_2071871 < baseStart_2071871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071873 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 6]
def baseStart_2071873 : Nat := 118140960795 + 2071873 * 2 ^ 59
def prefixEnd_2071873 : Nat := 4983230072969 + 3 ^ 40 * 2071873 * 2
def baseEnd_2071873 : Nat := 236414823127306115790919

theorem tailTrace_2071873 : CollatzResearch.WordTrace tailWord_2071873 prefixEnd_2071873 236414823127306115790919 := by
  unfold tailWord_2071873
  simp only [CollatzResearch.WordTrace]
  refine ⟨75567416422965443582252273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50378277615310295721501515 75567416422965443582252273)
  ·
    refine ⟨56675562317224082686689205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75567416422965443582252273 56675562317224082686689205)
    ·
      refine ⟨5313333967239757751877113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56675562317224082686689205 5313333967239757751877113)
      ·
        refine ⟨3985000475429818313907835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313333967239757751877113 3985000475429818313907835)
        ·
          refine ⟨5977500713144727470861753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985000475429818313907835 5977500713144727470861753)
          ·
            refine ⟨4483125534858545603146315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5977500713144727470861753 4483125534858545603146315)
            ·
              refine ⟨6724688302287818404719473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483125534858545603146315 6724688302287818404719473)
              ·
                refine ⟨5043516226715863803539605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724688302287818404719473 5043516226715863803539605)
                ·
                  refine ⟨236414823127306115790919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5043516226715863803539605 236414823127306115790919)
                  ·
                    rfl

theorem cell22_2071873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_2071873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071873 prefixEnd_2071873 := by exact prefixLift 2071873
  have htrace : WordTrace (prefixWord ++ tailWord_2071873) baseStart_2071873 baseEnd_2071873 := by
    simpa [prefixWord, tailWord_2071873, baseEnd_2071873] using wordTrace_append hprefix tailTrace_2071873
  have hstable : (prefixWord ++ tailWord_2071873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071873).length < 2 ^ (prefixWord ++ tailWord_2071873).sum := by decide
  have hdescent : baseEnd_2071873 < baseStart_2071873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071886 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2071886 : Nat := 118140960795 + 2071886 * 2 ^ 59
def prefixEnd_2071886 : Nat := 4983230072969 + 3 ^ 40 * 2071886 * 2
def baseEnd_2071886 : Nat := 709248919547590646797717

theorem tailTrace_2071886 : CollatzResearch.WordTrace tailWord_2071886 prefixEnd_2071886 709248919547590646797717 := by
  unfold tailWord_2071886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445986321489793350309439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50378593714612231201650341 9445986321489793350309439)
  ·
    refine ⟨14168979482234690025464159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9445986321489793350309439 14168979482234690025464159)
    ·
      refine ⟨21253469223352035038196239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168979482234690025464159 21253469223352035038196239)
      ·
        refine ⟨31880203835028052557294359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253469223352035038196239 31880203835028052557294359)
        ·
          refine ⟨47820305752542078835941539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31880203835028052557294359 47820305752542078835941539)
          ·
            refine ⟨71730458628813118253912309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47820305752542078835941539 71730458628813118253912309)
            ·
              refine ⟨6724730496451229836304279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71730458628813118253912309 6724730496451229836304279)
              ·
                refine ⟨10087095744676844754456419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724730496451229836304279 10087095744676844754456419)
                ·
                  refine ⟨15130643617015267131684629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087095744676844754456419 15130643617015267131684629)
                  ·
                    refine ⟨709248919547590646797717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15130643617015267131684629 709248919547590646797717)
                    ·
                      rfl

theorem cell22_2071886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2071886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071886 prefixEnd_2071886 := by exact prefixLift 2071886
  have htrace : WordTrace (prefixWord ++ tailWord_2071886) baseStart_2071886 baseEnd_2071886 := by
    simpa [prefixWord, tailWord_2071886, baseEnd_2071886] using wordTrace_append hprefix tailTrace_2071886
  have hstable : (prefixWord ++ tailWord_2071886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071886).length < 2 ^ (prefixWord ++ tailWord_2071886).sum := by decide
  have hdescent : baseEnd_2071886 < baseStart_2071886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071933 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_2071933 : Nat := 118140960795 + 2071933 * 2 ^ 59
def prefixEnd_2071933 : Nat := 4983230072969 + 3 ^ 40 * 2071933 * 2
def baseEnd_2071933 : Nat := 709265008608098190872573

theorem tailTrace_2071933 : CollatzResearch.WordTrace tailWord_2071933 prefixEnd_2071933 709265008608098190872573 := by
  unfold tailWord_2071933
  simp only [CollatzResearch.WordTrace]
  refine ⟨75569604802748073829436453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50379736535165382552957635 75569604802748073829436453)
  ·
    refine ⟨14169300900515263843019335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75569604802748073829436453 14169300900515263843019335)
    ·
      refine ⟨21253951350772895764529003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169300900515263843019335 21253951350772895764529003)
      ·
        refine ⟨31880927026159343646793505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253951350772895764529003 31880927026159343646793505)
        ·
          refine ⟨23910695269619507735095129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31880927026159343646793505 23910695269619507735095129)
          ·
            refine ⟨17933021452214630801321347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23910695269619507735095129 17933021452214630801321347)
            ·
              refine ⟨26899532178321946201982021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933021452214630801321347 26899532178321946201982021)
              ·
                refine ⟨5043662283435364912871629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26899532178321946201982021 5043662283435364912871629)
                ·
                  refine ⟨1891373356288261842326861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5043662283435364912871629 1891373356288261842326861)
                  ·
                    refine ⟨709265008608098190872573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891373356288261842326861 709265008608098190872573)
                    ·
                      rfl

theorem cell22_2071933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_2071933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071933 prefixEnd_2071933 := by exact prefixLift 2071933
  have htrace : WordTrace (prefixWord ++ tailWord_2071933) baseStart_2071933 baseEnd_2071933 := by
    simpa [prefixWord, tailWord_2071933, baseEnd_2071933] using wordTrace_append hprefix tailTrace_2071933
  have hstable : (prefixWord ++ tailWord_2071933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071933).length < 2 ^ (prefixWord ++ tailWord_2071933).sum := by decide
  have hdescent : baseEnd_2071933 < baseStart_2071933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071991 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 8]
def baseStart_2071991 : Nat := 118140960795 + 2071991 * 2 ^ 59
def prefixEnd_2071991 : Nat := 4983230072969 + 3 ^ 40 * 2071991 * 2
def baseEnd_2071991 : Nat := 236428287731135124307465

theorem tailTrace_2071991 : CollatzResearch.WordTrace tailWord_2071991 prefixEnd_2071991 236428287731135124307465 := by
  unfold tailWord_2071991
  simp only [CollatzResearch.WordTrace]
  refine ⟨75571720236537949735047827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50381146824358633156698551 75571720236537949735047827)
  ·
    refine ⟨113357580354806924602571741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75571720236537949735047827 113357580354806924602571741)
    ·
      refine ⟨42509092633052596725964403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113357580354806924602571741 42509092633052596725964403)
      ·
        refine ⟨63763638949578895088946605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42509092633052596725964403 63763638949578895088946605)
        ·
          refine ⟨23911364606092085658354977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63763638949578895088946605 23911364606092085658354977)
          ·
            refine ⟨17933523454569064243766233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23911364606092085658354977 17933523454569064243766233)
            ·
              refine ⟨13450142590926798182824675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17933523454569064243766233 13450142590926798182824675)
              ·
                refine ⟨20175213886390197274237013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450142590926798182824675 20175213886390197274237013)
                ·
                  refine ⟨236428287731135124307465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20175213886390197274237013 236428287731135124307465)
                  ·
                    rfl

theorem cell22_2071991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_2071991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2071991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2071991 prefixEnd_2071991 := by exact prefixLift 2071991
  have htrace : WordTrace (prefixWord ++ tailWord_2071991) baseStart_2071991 baseEnd_2071991 := by
    simpa [prefixWord, tailWord_2071991, baseEnd_2071991] using wordTrace_append hprefix tailTrace_2071991
  have hstable : (prefixWord ++ tailWord_2071991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071991).length < 2 ^ (prefixWord ++ tailWord_2071991).sum := by decide
  have hdescent : baseEnd_2071991 < baseStart_2071991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072023 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2072023 : Nat := 118140960795 + 2072023 * 2 ^ 59
def prefixEnd_2072023 : Nat := 4983230072969 + 3 ^ 40 * 2072023 * 2
def baseEnd_2072023 : Nat := 709295817447367956122297

theorem tailTrace_2072023 : CollatzResearch.WordTrace tailWord_2072023 prefixEnd_2072023 709295817447367956122297 := by
  unfold tailWord_2072023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75572887372422019200212723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50381924914948012800141815 75572887372422019200212723)
  ·
    refine ⟨113359331058633028800319085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75572887372422019200212723 113359331058633028800319085)
    ·
      refine ⟨42509749146987385800119657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113359331058633028800319085 42509749146987385800119657)
      ·
        refine ⟨31882311860240539350089743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42509749146987385800119657 31882311860240539350089743)
        ·
          refine ⟨47823467790360809025134615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31882311860240539350089743 47823467790360809025134615)
          ·
            refine ⟨71735201685541213537701923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47823467790360809025134615 71735201685541213537701923)
            ·
              refine ⟨107602802528311820306552885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71735201685541213537701923 107602802528311820306552885)
              ·
                refine ⟨10087762737029233153739333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107602802528311820306552885 10087762737029233153739333)
                ·
                  refine ⟨1891455513192981216326125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10087762737029233153739333 1891455513192981216326125)
                  ·
                    refine ⟨709295817447367956122297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891455513192981216326125 709295817447367956122297)
                    ·
                      rfl

theorem cell22_2072023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2072023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072023 prefixEnd_2072023 := by exact prefixLift 2072023
  have htrace : WordTrace (prefixWord ++ tailWord_2072023) baseStart_2072023 baseEnd_2072023 := by
    simpa [prefixWord, tailWord_2072023, baseEnd_2072023] using wordTrace_append hprefix tailTrace_2072023
  have hstable : (prefixWord ++ tailWord_2072023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072023).length < 2 ^ (prefixWord ++ tailWord_2072023).sum := by decide
  have hdescent : baseEnd_2072023 < baseStart_2072023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072025 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 4]
def baseStart_2072025 : Nat := 118140960795 + 2072025 * 2 ^ 59
def prefixEnd_2072025 : Nat := 4983230072969 + 3 ^ 40 * 2072025 * 2
def baseEnd_2072025 : Nat := 236432167362746872524097

theorem tailTrace_2072025 : CollatzResearch.WordTrace tailWord_2072025 prefixEnd_2072025 236432167362746872524097 := by
  unfold tailWord_2072025
  simp only [CollatzResearch.WordTrace]
  refine ⟨75572960318414773541785529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50381973545609849027857019 75572960318414773541785529)
  ·
    refine ⟨56679720238811080156339147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75572960318414773541785529 56679720238811080156339147)
    ·
      refine ⟨85019580358216620234508721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56679720238811080156339147 85019580358216620234508721)
      ·
        refine ⟨63764685268662465175881541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85019580358216620234508721 63764685268662465175881541)
        ·
          refine ⟨11955878487874212220477789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63764685268662465175881541 11955878487874212220477789)
          ·
            refine ⟨4483454432952829582679171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11955878487874212220477789 4483454432952829582679171)
            ·
              refine ⟨6725181649429244374018757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483454432952829582679171 6725181649429244374018757)
              ·
                refine ⟨1260971559267983320128517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6725181649429244374018757 1260971559267983320128517)
                ·
                  refine ⟨236432167362746872524097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260971559267983320128517 236432167362746872524097)
                  ·
                    rfl

theorem cell22_2072025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_2072025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072025 prefixEnd_2072025 := by exact prefixLift 2072025
  have htrace : WordTrace (prefixWord ++ tailWord_2072025) baseStart_2072025 baseEnd_2072025 := by
    simpa [prefixWord, tailWord_2072025, baseEnd_2072025] using wordTrace_append hprefix tailTrace_2072025
  have hstable : (prefixWord ++ tailWord_2072025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072025).length < 2 ^ (prefixWord ++ tailWord_2072025).sum := by decide
  have hdescent : baseEnd_2072025 < baseStart_2072025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072040 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2072040 : Nat := 118140960795 + 2072040 * 2 ^ 59
def prefixEnd_2072040 : Nat := 4983230072969 + 3 ^ 40 * 2072040 * 2
def baseEnd_2072040 : Nat := 709301636894785578447245

theorem tailTrace_2072040 : CollatzResearch.WordTrace tailWord_2072040 prefixEnd_2072040 709301636894785578447245 := by
  unfold tailWord_2072040
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786753706680215551790787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50382338275573620735721049 37786753706680215551790787)
  ·
    refine ⟨56680130560020323327686181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37786753706680215551790787 56680130560020323327686181)
    ·
      refine ⟨10627524480003810623941159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56680130560020323327686181 10627524480003810623941159)
      ·
        refine ⟨15941286720005715935911739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627524480003810623941159 15941286720005715935911739)
        ·
          refine ⟨23911930080008573903867609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15941286720005715935911739 23911930080008573903867609)
          ·
            refine ⟨17933947560006430427900707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23911930080008573903867609 17933947560006430427900707)
            ·
              refine ⟨26900921340009645641851061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933947560006430427900707 26900921340009645641851061)
              ·
                refine ⟨2521961375625904278923537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26900921340009645641851061 2521961375625904278923537)
                ·
                  refine ⟨1891471031719428209192653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521961375625904278923537 1891471031719428209192653)
                  ·
                    refine ⟨709301636894785578447245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891471031719428209192653 709301636894785578447245)
                    ·
                      rfl

theorem cell22_2072040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2072040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072040 prefixEnd_2072040 := by exact prefixLift 2072040
  have htrace : WordTrace (prefixWord ++ tailWord_2072040) baseStart_2072040 baseEnd_2072040 := by
    simpa [prefixWord, tailWord_2072040, baseEnd_2072040] using wordTrace_append hprefix tailTrace_2072040
  have hstable : (prefixWord ++ tailWord_2072040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072040).length < 2 ^ (prefixWord ++ tailWord_2072040).sum := by decide
  have hdescent : baseEnd_2072040 < baseStart_2072040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072051 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_2072051 : Nat := 118140960795 + 2072051 * 2 ^ 59
def prefixEnd_2072051 : Nat := 4983230072969 + 3 ^ 40 * 2072051 * 2
def baseEnd_2072051 : Nat := 709305402419585216422211

theorem tailTrace_2072051 : CollatzResearch.WordTrace tailWord_2072051 prefixEnd_2072051 709305402419585216422211 := by
  unfold tailWord_2072051
  simp only [CollatzResearch.WordTrace]
  refine ⟨75573908616320579982232007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50382605744213719988154671 75573908616320579982232007)
  ·
    refine ⟨113360862924480869973348011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75573908616320579982232007 113360862924480869973348011)
    ·
      refine ⟨170041294386721304960022017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113360862924480869973348011 170041294386721304960022017)
      ·
        refine ⟨127530970790040978720016513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170041294386721304960022017 127530970790040978720016513)
        ·
          refine ⟨95648228092530734040012385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127530970790040978720016513 95648228092530734040012385)
          ·
            refine ⟨71736171069398050530009289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95648228092530734040012385 71736171069398050530009289)
            ·
              refine ⟨53802128302048537897506967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71736171069398050530009289 53802128302048537897506967)
              ·
                refine ⟨80703192453072806846260451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53802128302048537897506967 80703192453072806846260451)
                ·
                  refine ⟨121054788679609210269390677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80703192453072806846260451 121054788679609210269390677)
                  ·
                    refine ⟨709305402419585216422211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121054788679609210269390677 709305402419585216422211)
                    ·
                      rfl

theorem cell22_2072051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_2072051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072051 prefixEnd_2072051 := by exact prefixLift 2072051
  have htrace : WordTrace (prefixWord ++ tailWord_2072051) baseStart_2072051 baseEnd_2072051 := by
    simpa [prefixWord, tailWord_2072051, baseEnd_2072051] using wordTrace_append hprefix tailTrace_2072051
  have hstable : (prefixWord ++ tailWord_2072051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072051).length < 2 ^ (prefixWord ++ tailWord_2072051).sum := by decide
  have hdescent : baseEnd_2072051 < baseStart_2072051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072085 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_2072085 : Nat := 118140960795 + 2072085 * 2 ^ 59
def prefixEnd_2072085 : Nat := 4983230072969 + 3 ^ 40 * 2072085 * 2
def baseEnd_2072085 : Nat := 709317041314420461072107

theorem tailTrace_2072085 : CollatzResearch.WordTrace tailWord_2072085 prefixEnd_2072085 709317041314420461072107 := by
  unfold tailWord_2072085
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575148698197403788969709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50383432465464935859313139 75575148698197403788969709)
  ·
    refine ⟨28340680761824026420863641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75575148698197403788969709 28340680761824026420863641)
    ·
      refine ⟨21255510571368019815647731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28340680761824026420863641 21255510571368019815647731)
      ·
        refine ⟨31883265857052029723471597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255510571368019815647731 31883265857052029723471597)
        ·
          refine ⟨11956224696394511146301849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31883265857052029723471597 11956224696394511146301849)
          ·
            refine ⟨8967168522295883359726387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11956224696394511146301849 8967168522295883359726387)
            ·
              refine ⟨13450752783443825039589581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967168522295883359726387 13450752783443825039589581)
              ·
                refine ⟨5044032293791434389846093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13450752783443825039589581 5044032293791434389846093)
                ·
                  refine ⟨1891512110171787896192285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5044032293791434389846093 1891512110171787896192285)
                  ·
                    refine ⟨709317041314420461072107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891512110171787896192285 709317041314420461072107)
                    ·
                      rfl

theorem cell22_2072085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_2072085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072085 prefixEnd_2072085 := by exact prefixLift 2072085
  have htrace : WordTrace (prefixWord ++ tailWord_2072085) baseStart_2072085 baseEnd_2072085 := by
    simpa [prefixWord, tailWord_2072085, baseEnd_2072085] using wordTrace_append hprefix tailTrace_2072085
  have hstable : (prefixWord ++ tailWord_2072085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072085).length < 2 ^ (prefixWord ++ tailWord_2072085).sum := by decide
  have hdescent : baseEnd_2072085 < baseStart_2072085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072104 : List Nat := [2, 1, 5, 2, 3, 1, 2, 6]
def baseStart_2072104 : Nat := 118140960795 + 2072104 * 2 ^ 59
def prefixEnd_2072104 : Nat := 4983230072969 + 3 ^ 40 * 2072104 * 2
def baseEnd_2072104 : Nat := 78813727266967860538561

theorem tailTrace_2072104 : CollatzResearch.WordTrace tailWord_2072104 prefixEnd_2072104 78813727266967860538561 := by
  unfold tailWord_2072104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37787920842564285016955683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50383894456752380022607577 37787920842564285016955683)
  ·
    refine ⟨56681881263846427525433525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37787920842564285016955683 56681881263846427525433525)
    ·
      refine ⟨5313926368485602580509393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56681881263846427525433525 5313926368485602580509393)
      ·
        refine ⟨3985444776364201935382045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313926368485602580509393 3985444776364201935382045)
        ·
          refine ⟨1494541791136575725768267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3985444776364201935382045 1494541791136575725768267)
          ·
            refine ⟨2241812686704863588652401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494541791136575725768267 2241812686704863588652401)
            ·
              refine ⟨1681359515028647691489301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241812686704863588652401 1681359515028647691489301)
              ·
                refine ⟨78813727266967860538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1681359515028647691489301 78813727266967860538561)
                ·
                  rfl

theorem cell22_2072104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_2072104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072104 prefixEnd_2072104 := by exact prefixLift 2072104
  have htrace : WordTrace (prefixWord ++ tailWord_2072104) baseStart_2072104 baseEnd_2072104 := by
    simpa [prefixWord, tailWord_2072104, baseEnd_2072104] using wordTrace_append hprefix tailTrace_2072104
  have hstable : (prefixWord ++ tailWord_2072104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072104).length < 2 ^ (prefixWord ++ tailWord_2072104).sum := by decide
  have hdescent : baseEnd_2072104 < baseStart_2072104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072119 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2072119 : Nat := 118140960795 + 2072119 * 2 ^ 59
def prefixEnd_2072119 : Nat := 4983230072969 + 3 ^ 40 * 2072119 * 2
def baseEnd_2072119 : Nat := 709328680209255705722003

theorem tailTrace_2072119 : CollatzResearch.WordTrace tailWord_2072119 prefixEnd_2072119 709328680209255705722003 := by
  unfold tailWord_2072119
  simp only [CollatzResearch.WordTrace]
  refine ⟨75576388780074227595707411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50384259186716151730471607 75576388780074227595707411)
  ·
    refine ⟨113364583170111341393561117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75576388780074227595707411 113364583170111341393561117)
    ·
      refine ⟨42511718688791753022585419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113364583170111341393561117 42511718688791753022585419)
      ·
        refine ⟨63767578033187629533878129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42511718688791753022585419 63767578033187629533878129)
        ·
          refine ⟨47825683524890722150408597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63767578033187629533878129 47825683524890722150408597)
          ·
            refine ⟨2241828915229252600800403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47825683524890722150408597 2241828915229252600800403)
            ·
              refine ⟨3362743372843878901200605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241828915229252600800403 3362743372843878901200605)
              ·
                refine ⟨1261028764816454587950227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3362743372843878901200605 1261028764816454587950227)
                ·
                  refine ⟨1891543147224681881925341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261028764816454587950227 1891543147224681881925341)
                  ·
                    refine ⟨709328680209255705722003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891543147224681881925341 709328680209255705722003)
                    ·
                      rfl

theorem cell22_2072119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2072119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072119 prefixEnd_2072119 := by exact prefixLift 2072119
  have htrace : WordTrace (prefixWord ++ tailWord_2072119) baseStart_2072119 baseEnd_2072119 := by
    simpa [prefixWord, tailWord_2072119, baseEnd_2072119] using wordTrace_append hprefix tailTrace_2072119
  have hstable : (prefixWord ++ tailWord_2072119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072119).length < 2 ^ (prefixWord ++ tailWord_2072119).sum := by decide
  have hdescent : baseEnd_2072119 < baseStart_2072119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_2072128 : Nat := 118140960795 + 2072128 * 2 ^ 59
def prefixEnd_2072128 : Nat := 4983230072969 + 3 ^ 40 * 2072128 * 2
def baseEnd_2072128 : Nat := 709331761093182682246975

theorem tailTrace_2072128 : CollatzResearch.WordTrace tailWord_2072128 prefixEnd_2072128 709331761093182682246975 := by
  unfold tailWord_2072128
  simp only [CollatzResearch.WordTrace]
  refine ⟨37788358518520811066392519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50384478024694414755190025 37788358518520811066392519)
  ·
    refine ⟨56682537777781216599588779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37788358518520811066392519 56682537777781216599588779)
    ·
      refine ⟨85023806666671824899383169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56682537777781216599588779 85023806666671824899383169)
      ·
        refine ⟨63767855000003868674537377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85023806666671824899383169 63767855000003868674537377)
        ·
          refine ⟨47825891250002901505903033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63767855000003868674537377 47825891250002901505903033)
          ·
            refine ⟨35869418437502176129427275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47825891250002901505903033 35869418437502176129427275)
            ·
              refine ⟨53804127656253264194140913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35869418437502176129427275 53804127656253264194140913)
              ·
                refine ⟨40353095742189948145605685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53804127656253264194140913 40353095742189948145605685)
                ·
                  refine ⟨3783102725830307638650533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40353095742189948145605685 3783102725830307638650533)
                  ·
                    refine ⟨709331761093182682246975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783102725830307638650533 709331761093182682246975)
                    ·
                      rfl

theorem cell22_2072128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_2072128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072128 prefixEnd_2072128 := by exact prefixLift 2072128
  have htrace : WordTrace (prefixWord ++ tailWord_2072128) baseStart_2072128 baseEnd_2072128 := by
    simpa [prefixWord, tailWord_2072128, baseEnd_2072128] using wordTrace_append hprefix tailTrace_2072128
  have hstable : (prefixWord ++ tailWord_2072128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072128).length < 2 ^ (prefixWord ++ tailWord_2072128).sum := by decide
  have hdescent : baseEnd_2072128 < baseStart_2072128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072192 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_2072192 : Nat := 118140960795 + 2072192 * 2 ^ 59
def prefixEnd_2072192 : Nat := 4983230072969 + 3 ^ 40 * 2072192 * 2
def baseEnd_2072192 : Nat := 709353669601107848646779

theorem tailTrace_2072192 : CollatzResearch.WordTrace tailWord_2072192 prefixEnd_2072192 709353669601107848646779 := by
  unfold tailWord_2072192
  simp only [CollatzResearch.WordTrace]
  refine ⟨37789525654404880531557415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50386034205873174042076553 37789525654404880531557415)
  ·
    refine ⟨56684288481607320797336123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37789525654404880531557415 56684288481607320797336123)
    ·
      refine ⟨85026432722410981196004185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56684288481607320797336123 85026432722410981196004185)
      ·
        refine ⟨63769824541808235897003139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85026432722410981196004185 63769824541808235897003139)
        ·
          refine ⟨95654736812712353845504709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63769824541808235897003139 95654736812712353845504709)
          ·
            refine ⟨17935263152383566346032133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95654736812712353845504709 17935263152383566346032133)
            ·
              refine ⟨3362861841071918689881025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17935263152383566346032133 3362861841071918689881025)
              ·
                refine ⟨2522146380803939017410769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362861841071918689881025 2522146380803939017410769)
                ·
                  refine ⟨1891609785602954263058077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522146380803939017410769 1891609785602954263058077)
                  ·
                    refine ⟨709353669601107848646779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891609785602954263058077 709353669601107848646779)
                    ·
                      rfl

theorem cell22_2072192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_2072192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072192 prefixEnd_2072192 := by exact prefixLift 2072192
  have htrace : WordTrace (prefixWord ++ tailWord_2072192) baseStart_2072192 baseEnd_2072192 := by
    simpa [prefixWord, tailWord_2072192, baseEnd_2072192] using wordTrace_append hprefix tailTrace_2072192
  have hstable : (prefixWord ++ tailWord_2072192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072192).length < 2 ^ (prefixWord ++ tailWord_2072192).sum := by decide
  have hdescent : baseEnd_2072192 < baseStart_2072192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072237 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2072237 : Nat := 118140960795 + 2072237 * 2 ^ 59
def prefixEnd_2072237 : Nat := 4983230072969 + 3 ^ 40 * 2072237 * 2
def baseEnd_2072237 : Nat := 709369074020742731271641

theorem tailTrace_2072237 : CollatzResearch.WordTrace tailWord_2072237 prefixEnd_2072237 709369074020742731271641 := by
  unfold tailWord_2072237
  simp only [CollatzResearch.WordTrace]
  refine ⟨75580692593646733748502965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50387128395764489165668643 75580692593646733748502965)
  ·
    refine ⟨7085689930654381288922153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75580692593646733748502965 7085689930654381288922153)
    ·
      refine ⟨5314267447990785966691615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7085689930654381288922153 5314267447990785966691615)
      ·
        refine ⟨7971401171986178950037423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314267447990785966691615 7971401171986178950037423)
        ·
          refine ⟨11957101757979268425056135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971401171986178950037423 11957101757979268425056135)
          ·
            refine ⟨17935652636968902637584203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957101757979268425056135 17935652636968902637584203)
            ·
              refine ⟨26903478955453353956376305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17935652636968902637584203 26903478955453353956376305)
              ·
                refine ⟨20177609216590015467282229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26903478955453353956376305 20177609216590015467282229)
                ·
                  refine ⟨1891650864055313950057709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20177609216590015467282229 1891650864055313950057709)
                  ·
                    refine ⟨709369074020742731271641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891650864055313950057709 709369074020742731271641)
                    ·
                      rfl

theorem cell22_2072237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2072237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072237 prefixEnd_2072237 := by exact prefixLift 2072237
  have htrace : WordTrace (prefixWord ++ tailWord_2072237) baseStart_2072237 baseEnd_2072237 := by
    simpa [prefixWord, tailWord_2072237, baseEnd_2072237] using wordTrace_append hprefix tailTrace_2072237
  have hstable : (prefixWord ++ tailWord_2072237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072237).length < 2 ^ (prefixWord ++ tailWord_2072237).sum := by decide
  have hdescent : baseEnd_2072237 < baseStart_2072237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072250 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_2072250 : Nat := 118140960795 + 2072250 * 2 ^ 59
def prefixEnd_2072250 : Nat := 4983230072969 + 3 ^ 40 * 2072250 * 2
def baseEnd_2072250 : Nat := 236457841395471676898867

theorem tailTrace_2072250 : CollatzResearch.WordTrace tailWord_2072250 prefixEnd_2072250 236457841395471676898867 := by
  unfold tailWord_2072250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895291685649909242181551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50387444495066424645817469 18895291685649909242181551)
  ·
    refine ⟨28342937528474863863272327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18895291685649909242181551 28342937528474863863272327)
    ·
      refine ⟨42514406292712295794908491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28342937528474863863272327 42514406292712295794908491)
      ·
        refine ⟨63771609439068443692362737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42514406292712295794908491 63771609439068443692362737)
        ·
          refine ⟨47828707079301332769272053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63771609439068443692362737 47828707079301332769272053)
          ·
            refine ⟨4483941288684499947119255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47828707079301332769272053 4483941288684499947119255)
            ·
              refine ⟨6725911933026749920678883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483941288684499947119255 6725911933026749920678883)
              ·
                refine ⟨10088867899540124881018325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725911933026749920678883 10088867899540124881018325)
                ·
                  refine ⟨236457841395471676898867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10088867899540124881018325 236457841395471676898867)
                  ·
                    rfl

theorem cell22_2072250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_2072250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072250 prefixEnd_2072250 := by exact prefixLift 2072250
  have htrace : WordTrace (prefixWord ++ tailWord_2072250) baseStart_2072250 baseEnd_2072250 := by
    simpa [prefixWord, tailWord_2072250, baseEnd_2072250] using wordTrace_append hprefix tailTrace_2072250
  have hstable : (prefixWord ++ tailWord_2072250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072250).length < 2 ^ (prefixWord ++ tailWord_2072250).sum := by decide
  have hdescent : baseEnd_2072250 < baseStart_2072250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072254 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2072254 : Nat := 118140960795 + 2072254 * 2 ^ 59
def prefixEnd_2072254 : Nat := 4983230072969 + 3 ^ 40 * 2072254 * 2
def baseEnd_2072254 : Nat := 709374893468160353596589

theorem tailTrace_2072254 : CollatzResearch.WordTrace tailWord_2072254 prefixEnd_2072254 709374893468160353596589 := by
  unfold tailWord_2072254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447664079323143206483977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50387541756390097101247877 9447664079323143206483977)
  ·
    refine ⟨7085748059492357404862983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9447664079323143206483977 7085748059492357404862983)
    ·
      refine ⟨10628622089238536107294475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085748059492357404862983 10628622089238536107294475)
      ·
        refine ⟨15942933133857804160941713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628622089238536107294475 15942933133857804160941713)
        ·
          refine ⟨11957199850393353120706285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15942933133857804160941713 11957199850393353120706285)
          ·
            refine ⟨4483949943897507420264857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11957199850393353120706285 4483949943897507420264857)
            ·
              refine ⟨3362962457923130565198643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4483949943897507420264857 3362962457923130565198643)
              ·
                refine ⟨5044443686884695847797965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362962457923130565198643 5044443686884695847797965)
                ·
                  refine ⟨1891666382581760942924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5044443686884695847797965 1891666382581760942924237)
                  ·
                    refine ⟨709374893468160353596589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891666382581760942924237 709374893468160353596589)
                    ·
                      rfl

theorem cell22_2072254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2072254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072254 prefixEnd_2072254 := by exact prefixLift 2072254
  have htrace : WordTrace (prefixWord ++ tailWord_2072254) baseStart_2072254 baseEnd_2072254 := by
    simpa [prefixWord, tailWord_2072254, baseEnd_2072254] using wordTrace_append hprefix tailTrace_2072254
  have hstable : (prefixWord ++ tailWord_2072254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072254).length < 2 ^ (prefixWord ++ tailWord_2072254).sum := by decide
  have hdescent : baseEnd_2072254 < baseStart_2072254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072318 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2072318 : Nat := 118140960795 + 2072318 * 2 ^ 59
def prefixEnd_2072318 : Nat := 4983230072969 + 3 ^ 40 * 2072318 * 2
def baseEnd_2072318 : Nat := 236465600658695173332131

theorem tailTrace_2072318 : CollatzResearch.WordTrace tailWord_2072318 prefixEnd_2072318 236465600658695173332131 := by
  unfold tailWord_2072318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447955863294160572775201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50389097937568856388134405 9447955863294160572775201)
  ·
    refine ⟨7085966897470620429581401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9447955863294160572775201 7085966897470620429581401)
    ·
      refine ⟨5314475173102965322186051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7085966897470620429581401 5314475173102965322186051)
      ·
        refine ⟨7971712759654447983279077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314475173102965322186051 7971712759654447983279077)
        ·
          refine ⟨1494696142435208996864827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7971712759654447983279077 1494696142435208996864827)
          ·
            refine ⟨2242044213652813495297241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494696142435208996864827 2242044213652813495297241)
            ·
              refine ⟨1681533160239610121472931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242044213652813495297241 1681533160239610121472931)
              ·
                refine ⟨2522299740359415182209397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681533160239610121472931 2522299740359415182209397)
                ·
                  refine ⟨236465600658695173332131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522299740359415182209397 236465600658695173332131)
                  ·
                    rfl

theorem cell22_2072318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2072318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072318 prefixEnd_2072318 := by exact prefixLift 2072318
  have htrace : WordTrace (prefixWord ++ tailWord_2072318) baseStart_2072318 baseEnd_2072318 := by
    simpa [prefixWord, tailWord_2072318, baseEnd_2072318] using wordTrace_append hprefix tailTrace_2072318
  have hstable : (prefixWord ++ tailWord_2072318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072318).length < 2 ^ (prefixWord ++ tailWord_2072318).sum := by decide
  have hdescent : baseEnd_2072318 < baseStart_2072318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072374 : List Nat := [5, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2072374 : Nat := 118140960795 + 2072374 * 2 ^ 59
def prefixEnd_2072374 : Nat := 4983230072969 + 3 ^ 40 * 2072374 * 2
def baseEnd_2072374 : Nat := 78823996880057782288469

theorem tailTrace_2072374 : CollatzResearch.WordTrace tailWord_2072374 prefixEnd_2072374 78823996880057782288469 := by
  unfold tailWord_2072374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724105587134400384140011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50390459596100270764160117 4724105587134400384140011)
  ·
    refine ⟨7086158380701600576210017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4724105587134400384140011 7086158380701600576210017)
    ·
      refine ⟨5314618785526200432157513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086158380701600576210017 5314618785526200432157513)
      ·
        refine ⟨3985964089144650324118135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5314618785526200432157513 3985964089144650324118135)
        ·
          refine ⟨5978946133716975486177203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985964089144650324118135 5978946133716975486177203)
          ·
            refine ⟨8968419200575463229265805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978946133716975486177203 8968419200575463229265805)
            ·
              refine ⟨3363157200215798710974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8968419200575463229265805 3363157200215798710974677)
              ·
                refine ⟨78823996880057782288469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3363157200215798710974677 78823996880057782288469)
                ·
                  rfl

theorem cell22_2072374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2072374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072374 prefixEnd_2072374 := by exact prefixLift 2072374
  have htrace : WordTrace (prefixWord ++ tailWord_2072374) baseStart_2072374 baseEnd_2072374 := by
    simpa [prefixWord, tailWord_2072374, baseEnd_2072374] using wordTrace_append hprefix tailTrace_2072374
  have hstable : (prefixWord ++ tailWord_2072374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072374).length < 2 ^ (prefixWord ++ tailWord_2072374).sum := by decide
  have hdescent : baseEnd_2072374 < baseStart_2072374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072400 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_2072400 : Nat := 118140960795 + 2072400 * 2 ^ 59
def prefixEnd_2072400 : Nat := 4983230072969 + 3 ^ 40 * 2072400 * 2
def baseEnd_2072400 : Nat := 709424872251864639446141

theorem tailTrace_2072400 : CollatzResearch.WordTrace tailWord_2072400 prefixEnd_2072400 709424872251864639446141 := by
  unfold tailWord_2072400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793318846028106293343327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50391091794704141724457769 37793318846028106293343327)
  ·
    refine ⟨56689978269042159440014991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37793318846028106293343327 56689978269042159440014991)
    ·
      refine ⟨85034967403563239160022487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56689978269042159440014991 85034967403563239160022487)
      ·
        refine ⟨127552451105344858740033731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85034967403563239160022487 127552451105344858740033731)
        ·
          refine ⟨191328676658017288110050597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127552451105344858740033731 191328676658017288110050597)
          ·
            refine ⟨35874126873378241520634487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191328676658017288110050597 35874126873378241520634487)
            ·
              refine ⟨53811190310067362280951731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35874126873378241520634487 53811190310067362280951731)
              ·
                refine ⟨80716785465101043421427597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53811190310067362280951731 80716785465101043421427597)
                ·
                  refine ⟨30268794549412891283035349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80716785465101043421427597 30268794549412891283035349)
                  ·
                    refine ⟨709424872251864639446141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30268794549412891283035349 709424872251864639446141)
                    ·
                      rfl

theorem cell22_2072400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_2072400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072400 prefixEnd_2072400 := by exact prefixLift 2072400
  have htrace : WordTrace (prefixWord ++ tailWord_2072400) baseStart_2072400 baseEnd_2072400 := by
    simpa [prefixWord, tailWord_2072400, baseEnd_2072400] using wordTrace_append hprefix tailTrace_2072400
  have hstable : (prefixWord ++ tailWord_2072400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072400).length < 2 ^ (prefixWord ++ tailWord_2072400).sum := by decide
  have hdescent : baseEnd_2072400 < baseStart_2072400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072466 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2072466 : Nat := 118140960795 + 2072466 * 2 ^ 59
def prefixEnd_2072466 : Nat := 4983230072969 + 3 ^ 40 * 2072466 * 2
def baseEnd_2072466 : Nat := 709447465400662467295939

theorem tailTrace_2072466 : CollatzResearch.WordTrace tailWord_2072466 prefixEnd_2072466 709447465400662467295939 := by
  unfold tailWord_2072466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897261227454276464647313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50392696606544737239059501 18897261227454276464647313)
  ·
    refine ⟨14172945920590707348485485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18897261227454276464647313 14172945920590707348485485)
    ·
      refine ⟨5314854720221515255682057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14172945920590707348485485 5314854720221515255682057)
      ·
        refine ⟨3986141040166136441761543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5314854720221515255682057 3986141040166136441761543)
        ·
          refine ⟨5979211560249204662642315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986141040166136441761543 5979211560249204662642315)
          ·
            refine ⟨8968817340373806993963473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979211560249204662642315 8968817340373806993963473)
            ·
              refine ⟨6726613005280355245472605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8968817340373806993963473 6726613005280355245472605)
              ·
                refine ⟨2522479876980133217052227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726613005280355245472605 2522479876980133217052227)
                ·
                  refine ⟨3783719815470199825578341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522479876980133217052227 3783719815470199825578341)
                  ·
                    refine ⟨709447465400662467295939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783719815470199825578341 709447465400662467295939)
                    ·
                      rfl

theorem cell22_2072466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2072466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072466 prefixEnd_2072466 := by exact prefixLift 2072466
  have htrace : WordTrace (prefixWord ++ tailWord_2072466) baseStart_2072466 baseEnd_2072466 := by
    simpa [prefixWord, tailWord_2072466, baseEnd_2072466] using wordTrace_append hprefix tailTrace_2072466
  have hstable : (prefixWord ++ tailWord_2072466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072466).length < 2 ^ (prefixWord ++ tailWord_2072466).sum := by decide
  have hdescent : baseEnd_2072466 < baseStart_2072466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072481 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 6]
def baseStart_2072481 : Nat := 118140960795 + 2072481 * 2 ^ 59
def prefixEnd_2072481 : Nat := 4983230072969 + 3 ^ 40 * 2072481 * 2
def baseEnd_2072481 : Nat := 236484200069069142723631

theorem tailTrace_2072481 : CollatzResearch.WordTrace tailWord_2072481 prefixEnd_2072481 236484200069069142723631 := by
  unfold tailWord_2072481
  simp only [CollatzResearch.WordTrace]
  refine ⟨75589592004762763420385297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50393061336508508946923531 75589592004762763420385297)
  ·
    refine ⟨56692194003572072565288973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75589592004762763420385297 56692194003572072565288973)
    ·
      refine ⟨21259572751339527211983365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56692194003572072565288973 21259572751339527211983365)
      ·
        refine ⟨3986169890876161352246881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21259572751339527211983365 3986169890876161352246881)
        ·
          refine ⟨2989627418157121014185161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986169890876161352246881 2989627418157121014185161)
          ·
            refine ⟨2242220563617840760638871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989627418157121014185161 2242220563617840760638871)
            ·
              refine ⟨3363330845426761140958307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242220563617840760638871 3363330845426761140958307)
              ·
                refine ⟨5044996268140141711437461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363330845426761140958307 5044996268140141711437461)
                ·
                  refine ⟨236484200069069142723631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5044996268140141711437461 236484200069069142723631)
                  ·
                    rfl

theorem cell22_2072481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_2072481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072481 prefixEnd_2072481 := by exact prefixLift 2072481
  have htrace : WordTrace (prefixWord ++ tailWord_2072481) baseStart_2072481 baseEnd_2072481 := by
    simpa [prefixWord, tailWord_2072481, baseEnd_2072481] using wordTrace_append hprefix tailTrace_2072481
  have hstable : (prefixWord ++ tailWord_2072481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072481).length < 2 ^ (prefixWord ++ tailWord_2072481).sum := by decide
  have hdescent : baseEnd_2072481 < baseStart_2072481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072500 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2072500 : Nat := 118140960795 + 2072500 * 2 ^ 59
def prefixEnd_2072500 : Nat := 4983230072969 + 3 ^ 40 * 2072500 * 2
def baseEnd_2072500 : Nat := 709459104295497711945835

theorem tailTrace_2072500 : CollatzResearch.WordTrace tailWord_2072500 prefixEnd_2072500 709459104295497711945835 := by
  unfold tailWord_2072500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795142495846964832663477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50393523327795953110217969 37795142495846964832663477)
  ·
    refine ⟨3543294608985652953062201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37795142495846964832663477 3543294608985652953062201)
    ·
      refine ⟨2657470956739239714796651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3543294608985652953062201 2657470956739239714796651)
      ·
        refine ⟨3986206435108859572194977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657470956739239714796651 3986206435108859572194977)
        ·
          refine ⟨2989654826331644679146233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986206435108859572194977 2989654826331644679146233)
          ·
            refine ⟨2242241119748733509359675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989654826331644679146233 2242241119748733509359675)
            ·
              refine ⟨3363361679623100264039513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242241119748733509359675 3363361679623100264039513)
              ·
                refine ⟨2522521259717325198029635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363361679623100264039513 2522521259717325198029635)
                ·
                  refine ⟨3783781889575987797044453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522521259717325198029635 3783781889575987797044453)
                  ·
                    refine ⟨709459104295497711945835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783781889575987797044453 709459104295497711945835)
                    ·
                      rfl

theorem cell22_2072500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2072500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072500 prefixEnd_2072500 := by exact prefixLift 2072500
  have htrace : WordTrace (prefixWord ++ tailWord_2072500) baseStart_2072500 baseEnd_2072500 := by
    simpa [prefixWord, tailWord_2072500, baseEnd_2072500] using wordTrace_append hprefix tailTrace_2072500
  have hstable : (prefixWord ++ tailWord_2072500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072500).length < 2 ^ (prefixWord ++ tailWord_2072500).sum := by decide
  have hdescent : baseEnd_2072500 < baseStart_2072500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072554 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_2072554 : Nat := 118140960795 + 2072554 * 2 ^ 59
def prefixEnd_2072554 : Nat := 4983230072969 + 3 ^ 40 * 2072554 * 2
def baseEnd_2072554 : Nat := 236492529866353190365223

theorem tailTrace_2072554 : CollatzResearch.WordTrace tailWord_2072554 prefixEnd_2072554 236492529866353190365223 := by
  unfold tailWord_2072554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898063633374574221948179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50394836355665531258528477 18898063633374574221948179)
  ·
    refine ⟨28347095450061861332922269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18898063633374574221948179 28347095450061861332922269)
    ·
      refine ⟨10630160793773197999845851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28347095450061861332922269 10630160793773197999845851)
      ·
        refine ⟨15945241190659796999768777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10630160793773197999845851 15945241190659796999768777)
        ·
          refine ⟨11958930892994847749826583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15945241190659796999768777 11958930892994847749826583)
          ·
            refine ⟨17938396339492271624739875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958930892994847749826583 17938396339492271624739875)
            ·
              refine ⟨26907594509238407437109813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17938396339492271624739875 26907594509238407437109813)
              ·
                refine ⟨2522586985241100697229045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26907594509238407437109813 2522586985241100697229045)
                ·
                  refine ⟨236492529866353190365223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522586985241100697229045 236492529866353190365223)
                  ·
                    rfl

theorem cell22_2072554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_2072554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072554 prefixEnd_2072554 := by exact prefixLift 2072554
  have htrace : WordTrace (prefixWord ++ tailWord_2072554) baseStart_2072554 baseEnd_2072554 := by
    simpa [prefixWord, tailWord_2072554, baseEnd_2072554] using wordTrace_append hprefix tailTrace_2072554
  have hstable : (prefixWord ++ tailWord_2072554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072554).length < 2 ^ (prefixWord ++ tailWord_2072554).sum := by decide
  have hdescent : baseEnd_2072554 < baseStart_2072554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072618 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2072618 : Nat := 118140960795 + 2072618 * 2 ^ 59
def prefixEnd_2072618 : Nat := 4983230072969 + 3 ^ 40 * 2072618 * 2
def baseEnd_2072618 : Nat := 709499498106984737495473

theorem tailTrace_2072618 : CollatzResearch.WordTrace tailWord_2072618 prefixEnd_2072618 709499498106984737495473 := by
  unfold tailWord_2072618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898647201316608954530627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50396392536844290545415005 18898647201316608954530627)
  ·
    refine ⟨28347970801974913431795941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18898647201316608954530627 28347970801974913431795941)
    ·
      refine ⟨5315244525370296268461739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28347970801974913431795941 5315244525370296268461739)
      ·
        refine ⟨7972866788055444402692609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315244525370296268461739 7972866788055444402692609)
        ·
          refine ⟨5979650091041583302019457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972866788055444402692609 5979650091041583302019457)
          ·
            refine ⟨4484737568281187476514593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5979650091041583302019457 4484737568281187476514593)
            ·
              refine ⟨3363553176210890607385945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484737568281187476514593 3363553176210890607385945)
              ·
                refine ⟨2522664882158167955539459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363553176210890607385945 2522664882158167955539459)
                ·
                  refine ⟨3783997323237251933309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522664882158167955539459 3783997323237251933309189)
                  ·
                    refine ⟨709499498106984737495473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783997323237251933309189 709499498106984737495473)
                    ·
                      rfl

theorem cell22_2072618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2072618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072618 prefixEnd_2072618 := by exact prefixLift 2072618
  have htrace : WordTrace (prefixWord ++ tailWord_2072618) baseStart_2072618 baseEnd_2072618 := by
    simpa [prefixWord, tailWord_2072618, baseEnd_2072618] using wordTrace_append hprefix tailTrace_2072618
  have hstable : (prefixWord ++ tailWord_2072618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072618).length < 2 ^ (prefixWord ++ tailWord_2072618).sum := by decide
  have hdescent : baseEnd_2072618 < baseStart_2072618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072629 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2072629 : Nat := 118140960795 + 2072629 * 2 ^ 59
def prefixEnd_2072629 : Nat := 4983230072969 + 3 ^ 40 * 2072629 * 2
def baseEnd_2072629 : Nat := 709503263631784375470439

theorem tailTrace_2072629 : CollatzResearch.WordTrace tailWord_2072629 prefixEnd_2072629 709503263631784375470439 := by
  unfold tailWord_2072629
  simp only [CollatzResearch.WordTrace]
  refine ⟨75594990008226584696772941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50396660005484389797848627 75594990008226584696772941)
  ·
    refine ⟨28348121253084969261289853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75594990008226584696772941 28348121253084969261289853)
    ·
      refine ⟨10630545469906863472983695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28348121253084969261289853 10630545469906863472983695)
      ·
        refine ⟨15945818204860295209475543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10630545469906863472983695 15945818204860295209475543)
        ·
          refine ⟨23918727307290442814213315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15945818204860295209475543 23918727307290442814213315)
          ·
            refine ⟨35878090960935664221319973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23918727307290442814213315 35878090960935664221319973)
            ·
              refine ⟨6727142055175437041497495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35878090960935664221319973 6727142055175437041497495)
              ·
                refine ⟨10090713082763155562246243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727142055175437041497495 10090713082763155562246243)
                ·
                  refine ⟨15136069624144733343369365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090713082763155562246243 15136069624144733343369365)
                  ·
                    refine ⟨709503263631784375470439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15136069624144733343369365 709503263631784375470439)
                    ·
                      rfl

theorem cell22_2072629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2072629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072629 prefixEnd_2072629 := by exact prefixLift 2072629
  have htrace : WordTrace (prefixWord ++ tailWord_2072629) baseStart_2072629 baseEnd_2072629 := by
    simpa [prefixWord, tailWord_2072629, baseEnd_2072629] using wordTrace_append hprefix tailTrace_2072629
  have hstable : (prefixWord ++ tailWord_2072629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072629).length < 2 ^ (prefixWord ++ tailWord_2072629).sum := by decide
  have hdescent : baseEnd_2072629 < baseStart_2072629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072676 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_2072676 : Nat := 118140960795 + 2072676 * 2 ^ 59
def prefixEnd_2072676 : Nat := 4983230072969 + 3 ^ 40 * 2072676 * 2
def baseEnd_2072676 : Nat := 709519352692291919545295

theorem tailTrace_2072676 : CollatzResearch.WordTrace tailWord_2072676 prefixEnd_2072676 709519352692291919545295 := by
  unfold tailWord_2072676
  simp only [CollatzResearch.WordTrace]
  refine ⟨37798352119528155861866941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50397802826037541149155921 37798352119528155861866941)
  ·
    refine ⟨14174382044823058448200103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37798352119528155861866941 14174382044823058448200103)
    ·
      refine ⟨21261573067234587672300155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14174382044823058448200103 21261573067234587672300155)
      ·
        refine ⟨31892359600851881508450233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21261573067234587672300155 31892359600851881508450233)
        ·
          refine ⟨23919269700638911131337675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31892359600851881508450233 23919269700638911131337675)
          ·
            refine ⟨35878904550958366697006513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23919269700638911131337675 35878904550958366697006513)
            ·
              refine ⟨26909178413218775022754885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35878904550958366697006513 26909178413218775022754885)
              ·
                refine ⟨5045470952478520316766541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26909178413218775022754885 5045470952478520316766541)
                ·
                  refine ⟨1892051607179445118787453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5045470952478520316766541 1892051607179445118787453)
                  ·
                    refine ⟨709519352692291919545295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892051607179445118787453 709519352692291919545295)
                    ·
                      rfl

theorem cell22_2072676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_2072676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072676 prefixEnd_2072676 := by exact prefixLift 2072676
  have htrace : WordTrace (prefixWord ++ tailWord_2072676) baseStart_2072676 baseEnd_2072676 := by
    simpa [prefixWord, tailWord_2072676, baseEnd_2072676] using wordTrace_append hprefix tailTrace_2072676
  have hstable : (prefixWord ++ tailWord_2072676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072676).length < 2 ^ (prefixWord ++ tailWord_2072676).sum := by decide
  have hdescent : baseEnd_2072676 < baseStart_2072676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_2072704 : Nat := 118140960795 + 2072704 * 2 ^ 59
def prefixEnd_2072704 : Nat := 4983230072969 + 3 ^ 40 * 2072704 * 2
def baseEnd_2072704 : Nat := 709528937664509179845209

theorem tailTrace_2072704 : CollatzResearch.WordTrace tailWord_2072704 prefixEnd_2072704 709528937664509179845209 := by
  unfold tailWord_2072704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37798862741477436252876583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50398483655303248337168777 37798862741477436252876583)
  ·
    refine ⟨56698294112216154379314875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37798862741477436252876583 56698294112216154379314875)
    ·
      refine ⟨85047441168324231568972313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56698294112216154379314875 85047441168324231568972313)
      ·
        refine ⟨63785580876243173676729235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85047441168324231568972313 63785580876243173676729235)
        ·
          refine ⟨95678371314364760515093853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63785580876243173676729235 95678371314364760515093853)
          ·
            refine ⟨35879389242886785193160195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95678371314364760515093853 35879389242886785193160195)
            ·
              refine ⟨53819083864330177789740293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35879389242886785193160195 53819083864330177789740293)
              ·
                refine ⟨10091078224561908335576305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53819083864330177789740293 10091078224561908335576305)
                ·
                  refine ⟨7568308668421431251682229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091078224561908335576305 7568308668421431251682229)
                  ·
                    refine ⟨709528937664509179845209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7568308668421431251682229 709528937664509179845209)
                    ·
                      rfl

theorem cell22_2072704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_2072704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072704 prefixEnd_2072704 := by exact prefixLift 2072704
  have htrace : WordTrace (prefixWord ++ tailWord_2072704) baseStart_2072704 baseEnd_2072704 := by
    simpa [prefixWord, tailWord_2072704, baseEnd_2072704] using wordTrace_append hprefix tailTrace_2072704
  have hstable : (prefixWord ++ tailWord_2072704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072704).length < 2 ^ (prefixWord ++ tailWord_2072704).sum := by decide
  have hdescent : baseEnd_2072704 < baseStart_2072704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072736 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_2072736 : Nat := 118140960795 + 2072736 * 2 ^ 59
def prefixEnd_2072736 : Nat := 4983230072969 + 3 ^ 40 * 2072736 * 2
def baseEnd_2072736 : Nat := 709539891918471763045111

theorem tailTrace_2072736 : CollatzResearch.WordTrace tailWord_2072736 prefixEnd_2072736 709539891918471763045111 := by
  unfold tailWord_2072736
  simp only [CollatzResearch.WordTrace]
  refine ⟨37799446309419470985459031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50399261745892627980612041 37799446309419470985459031)
  ·
    refine ⟨56699169464129206478188547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37799446309419470985459031 56699169464129206478188547)
    ·
      refine ⟨85048754196193809717282821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56699169464129206478188547 85048754196193809717282821)
      ·
        refine ⟨15946641411786339321990529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85048754196193809717282821 15946641411786339321990529)
        ·
          refine ⟨11959981058839754491492897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15946641411786339321990529 11959981058839754491492897)
          ·
            refine ⟨8969985794129815868619673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11959981058839754491492897 8969985794129815868619673)
            ·
              refine ⟨6727489345597361901464755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969985794129815868619673 6727489345597361901464755)
              ·
                refine ⟨10091234018396042852197133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727489345597361901464755 10091234018396042852197133)
                ·
                  refine ⟨3784212756898516069573925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10091234018396042852197133 3784212756898516069573925)
                  ·
                    refine ⟨709539891918471763045111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3784212756898516069573925 709539891918471763045111)
                    ·
                      rfl

theorem cell22_2072736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_2072736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072736 prefixEnd_2072736 := by exact prefixLift 2072736
  have htrace : WordTrace (prefixWord ++ tailWord_2072736) baseStart_2072736 baseEnd_2072736 := by
    simpa [prefixWord, tailWord_2072736, baseEnd_2072736] using wordTrace_append hprefix tailTrace_2072736
  have hstable : (prefixWord ++ tailWord_2072736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072736).length < 2 ^ (prefixWord ++ tailWord_2072736).sum := by decide
  have hdescent : baseEnd_2072736 < baseStart_2072736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072757 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2072757 : Nat := 118140960795 + 2072757 * 2 ^ 59
def prefixEnd_2072757 : Nat := 4983230072969 + 3 ^ 40 * 2072757 * 2
def baseEnd_2072757 : Nat := 236515693549211569423349

theorem tailTrace_2072757 : CollatzResearch.WordTrace tailWord_2072757 prefixEnd_2072757 236515693549211569423349 := by
  unfold tailWord_2072757
  simp only [CollatzResearch.WordTrace]
  refine ⟨75599658551762862557432525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50399772367841908371621683 75599658551762862557432525)
  ·
    refine ⟨28349871956911073459037197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75599658551762862557432525 28349871956911073459037197)
    ·
      refine ⟨10631201983841652547138949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28349871956911073459037197 10631201983841652547138949)
      ·
        refine ⟨1993350371970309852588553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10631201983841652547138949 1993350371970309852588553)
        ·
          refine ⟨1495012778977732389441415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993350371970309852588553 1495012778977732389441415)
          ·
            refine ⟨2242519168466598584162123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495012778977732389441415 2242519168466598584162123)
            ·
              refine ⟨3363778752699897876243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242519168466598584162123 3363778752699897876243185)
              ·
                refine ⟨2522834064524923407182389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363778752699897876243185 2522834064524923407182389)
                ·
                  refine ⟨236515693549211569423349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522834064524923407182389 236515693549211569423349)
                  ·
                    rfl

theorem cell22_2072757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2072757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072757 prefixEnd_2072757 := by exact prefixLift 2072757
  have htrace : WordTrace (prefixWord ++ tailWord_2072757) baseStart_2072757 baseEnd_2072757 := by
    simpa [prefixWord, tailWord_2072757, baseEnd_2072757] using wordTrace_append hprefix tailTrace_2072757
  have hstable : (prefixWord ++ tailWord_2072757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072757).length < 2 ^ (prefixWord ++ tailWord_2072757).sum := by decide
  have hdescent : baseEnd_2072757 < baseStart_2072757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072768 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_2072768 : Nat := 118140960795 + 2072768 * 2 ^ 59
def prefixEnd_2072768 : Nat := 4983230072969 + 3 ^ 40 * 2072768 * 2
def baseEnd_2072768 : Nat := 236516948724144782081671

theorem tailTrace_2072768 : CollatzResearch.WordTrace tailWord_2072768 prefixEnd_2072768 236516948724144782081671 := by
  unfold tailWord_2072768
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800029877361505718041479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50400039836482007624055305 37800029877361505718041479)
  ·
    refine ⟨56700044816042258577062219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37800029877361505718041479 56700044816042258577062219)
    ·
      refine ⟨85050067224063387865593329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56700044816042258577062219 85050067224063387865593329)
      ·
        refine ⟨63787550418047540899194997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85050067224063387865593329 63787550418047540899194997)
        ·
          refine ⟨5980082851691956959299531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63787550418047540899194997 5980082851691956959299531)
          ·
            refine ⟨8970124277537935438949297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980082851691956959299531 8970124277537935438949297)
            ·
              refine ⟨6727593208153451579211973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970124277537935438949297 6727593208153451579211973)
              ·
                refine ⟨1261423726528772171102245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6727593208153451579211973 1261423726528772171102245)
                ·
                  refine ⟨236516948724144782081671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261423726528772171102245 236516948724144782081671)
                  ·
                    rfl

theorem cell22_2072768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_2072768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072768 prefixEnd_2072768 := by exact prefixLift 2072768
  have htrace : WordTrace (prefixWord ++ tailWord_2072768) baseStart_2072768 baseEnd_2072768 := by
    simpa [prefixWord, tailWord_2072768, baseEnd_2072768] using wordTrace_append hprefix tailTrace_2072768
  have hstable : (prefixWord ++ tailWord_2072768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072768).length < 2 ^ (prefixWord ++ tailWord_2072768).sum := by decide
  have hdescent : baseEnd_2072768 < baseStart_2072768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072779 : List Nat := [1, 1, 1, 1, 3, 2, 4, 9]
def baseStart_2072779 : Nat := 118140960795 + 2072779 * 2 ^ 59
def prefixEnd_2072779 : Nat := 4983230072969 + 3 ^ 40 * 2072779 * 2
def baseEnd_2072779 : Nat := 78839401299692664913331

theorem tailTrace_2072779 : CollatzResearch.WordTrace tailWord_2072779 prefixEnd_2072779 78839401299692664913331 := by
  unfold tailWord_2072779
  simp only [CollatzResearch.WordTrace]
  refine ⟨75600460957683160314733391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50400307305122106876488927 75600460957683160314733391)
  ·
    refine ⟨113400691436524740472100087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75600460957683160314733391 113400691436524740472100087)
    ·
      refine ⟨170101037154787110708150131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113400691436524740472100087 170101037154787110708150131)
      ·
        refine ⟨255151555732180666062225197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170101037154787110708150131 255151555732180666062225197)
        ·
          refine ⟨95681833399567749773334449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255151555732180666062225197 95681833399567749773334449)
          ·
            refine ⟨71761375049675812330000837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95681833399567749773334449 71761375049675812330000837)
            ·
              refine ⟨13455257821814214811875157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71761375049675812330000837 13455257821814214811875157)
              ·
                refine ⟨78839401299692664913331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13455257821814214811875157 78839401299692664913331)
                ·
                  rfl

theorem cell22_2072779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_2072779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072779 prefixEnd_2072779 := by exact prefixLift 2072779
  have htrace : WordTrace (prefixWord ++ tailWord_2072779) baseStart_2072779 baseEnd_2072779 := by
    simpa [prefixWord, tailWord_2072779, baseEnd_2072779] using wordTrace_append hprefix tailTrace_2072779
  have hstable : (prefixWord ++ tailWord_2072779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072779).length < 2 ^ (prefixWord ++ tailWord_2072779).sum := by decide
  have hdescent : baseEnd_2072779 < baseStart_2072779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072813 : List Nat := [1, 5, 1, 2, 3, 2, 8]
def baseStart_2072813 : Nat := 118140960795 + 2072813 * 2 ^ 59
def prefixEnd_2072813 : Nat := 4983230072969 + 3 ^ 40 * 2072813 * 2
def baseEnd_2072813 : Nat := 26280231503409971439625

theorem tailTrace_2072813 : CollatzResearch.WordTrace tailWord_2072813 prefixEnd_2072813 26280231503409971439625 := by
  unfold tailWord_2072813
  simp only [CollatzResearch.WordTrace]
  refine ⟨75601701039559984121471093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50401134026373322747647395 75601701039559984121471093)
  ·
    refine ⟨7087659472458748511387915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75601701039559984121471093 7087659472458748511387915)
    ·
      refine ⟨10631489208688122767081873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7087659472458748511387915 10631489208688122767081873)
      ·
        refine ⟨7973616906516092075311405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10631489208688122767081873 7973616906516092075311405)
        ·
          refine ⟨2990106339943534528241777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7973616906516092075311405 2990106339943534528241777)
          ·
            refine ⟨2242579754957650896181333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990106339943534528241777 2242579754957650896181333)
            ·
              refine ⟨26280231503409971439625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2242579754957650896181333 26280231503409971439625)
              ·
                rfl

theorem cell22_2072813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 8].length) (baseStart_2072813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072813 prefixEnd_2072813 := by exact prefixLift 2072813
  have htrace : WordTrace (prefixWord ++ tailWord_2072813) baseStart_2072813 baseEnd_2072813 := by
    simpa [prefixWord, tailWord_2072813, baseEnd_2072813] using wordTrace_append hprefix tailTrace_2072813
  have hstable : (prefixWord ++ tailWord_2072813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072813).length < 2 ^ (prefixWord ++ tailWord_2072813).sum := by decide
  have hdescent : baseEnd_2072813 < baseStart_2072813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072834 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2072834 : Nat := 118140960795 + 2072834 * 2 ^ 59
def prefixEnd_2072834 : Nat := 4983230072969 + 3 ^ 40 * 2072834 * 2
def baseEnd_2072834 : Nat := 709573439321232174094811

theorem tailTrace_2072834 : CollatzResearch.WordTrace tailWord_2072834 prefixEnd_2072834 709573439321232174094811 := by
  unfold tailWord_2072834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900616743120976176996389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50401644648322603138657037 18900616743120976176996389)
  ·
    refine ⟨3543865639335183033186823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18900616743120976176996389 3543865639335183033186823)
    ·
      refine ⟨5315798459002774549780235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543865639335183033186823 5315798459002774549780235)
      ·
        refine ⟨7973697688504161824670353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315798459002774549780235 7973697688504161824670353)
        ·
          refine ⟨5980273266378121368502765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7973697688504161824670353 5980273266378121368502765)
          ·
            refine ⟨2242602474891795513188537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5980273266378121368502765 2242602474891795513188537)
            ·
              refine ⟨1681951856168846634891403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242602474891795513188537 1681951856168846634891403)
              ·
                refine ⟨2522927784253269952337105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681951856168846634891403 2522927784253269952337105)
                ·
                  refine ⟨1892195838189952464252829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522927784253269952337105 1892195838189952464252829)
                  ·
                    refine ⟨709573439321232174094811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892195838189952464252829 709573439321232174094811)
                    ·
                      rfl

theorem cell22_2072834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2072834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072834 prefixEnd_2072834 := by exact prefixLift 2072834
  have htrace : WordTrace (prefixWord ++ tailWord_2072834) baseStart_2072834 baseEnd_2072834 := by
    simpa [prefixWord, tailWord_2072834, baseEnd_2072834] using wordTrace_append hprefix tailTrace_2072834
  have hstable : (prefixWord ++ tailWord_2072834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072834).length < 2 ^ (prefixWord ++ tailWord_2072834).sum := by decide
  have hdescent : baseEnd_2072834 < baseStart_2072834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072931 : List Nat := [1, 1, 1, 5, 2, 1, 11]
def baseStart_2072931 : Nat := 118140960795 + 2072931 * 2 ^ 59
def prefixEnd_2072931 : Nat := 4983230072969 + 3 ^ 40 * 2072931 * 2
def baseEnd_2072931 : Nat := 26281727570502083497019

theorem tailTrace_2072931 : CollatzResearch.WordTrace tailWord_2072931 prefixEnd_2072931 26281727570502083497019 := by
  unfold tailWord_2072931
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606004853132490274266647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50404003235421660182844431 75606004853132490274266647)
  ·
    refine ⟨113409007279698735411399971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75606004853132490274266647 113409007279698735411399971)
    ·
      refine ⟨170113510919548103117099957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113409007279698735411399971 170113510919548103117099957)
      ·
        refine ⟨15948141648707634667228121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170113510919548103117099957 15948141648707634667228121)
        ·
          refine ⟨11961106236530726000421091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15948141648707634667228121 11961106236530726000421091)
          ·
            refine ⟨17941659354796089000631637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961106236530726000421091 17941659354796089000631637)
            ·
              refine ⟨26281727570502083497019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17941659354796089000631637 26281727570502083497019)
              ·
                rfl

theorem cell22_2072931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 11].length) (baseStart_2072931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072931 prefixEnd_2072931 := by exact prefixLift 2072931
  have htrace : WordTrace (prefixWord ++ tailWord_2072931) baseStart_2072931 baseEnd_2072931 := by
    simpa [prefixWord, tailWord_2072931, baseEnd_2072931] using wordTrace_append hprefix tailTrace_2072931
  have hstable : (prefixWord ++ tailWord_2072931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072931).length < 2 ^ (prefixWord ++ tailWord_2072931).sum := by decide
  have hdescent : baseEnd_2072931 < baseStart_2072931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072935 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2072935 : Nat := 118140960795 + 2072935 * 2 ^ 59
def prefixEnd_2072935 : Nat := 4983230072969 + 3 ^ 40 * 2072935 * 2
def baseEnd_2072935 : Nat := 709608013685301577319501

theorem tailTrace_2072935 : CollatzResearch.WordTrace tailWord_2072935 prefixEnd_2072935 709608013685301577319501 := by
  unfold tailWord_2072935
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606150745117998957412259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50404100496745332638274839 75606150745117998957412259)
  ·
    refine ⟨113409226117676998436118389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75606150745117998957412259 113409226117676998436118389)
    ·
      refine ⟨10632114948532218603386099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113409226117676998436118389 10632114948532218603386099)
      ·
        refine ⟨15948172422798327905079149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632114948532218603386099 15948172422798327905079149)
        ·
          refine ⟨5980564658549372964404681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15948172422798327905079149 5980564658549372964404681)
          ·
            refine ⟨4485423493912029723303511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5980564658549372964404681 4485423493912029723303511)
            ·
              refine ⟨6728135240868044584955267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485423493912029723303511 6728135240868044584955267)
              ·
                refine ⟨10092202861302066877432901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728135240868044584955267 10092202861302066877432901)
                ·
                  refine ⟨1892288036494137539518669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10092202861302066877432901 1892288036494137539518669)
                  ·
                    refine ⟨709608013685301577319501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892288036494137539518669 709608013685301577319501)
                    ·
                      rfl

theorem cell22_2072935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2072935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2072935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2072935 prefixEnd_2072935 := by exact prefixLift 2072935
  have htrace : WordTrace (prefixWord ++ tailWord_2072935) baseStart_2072935 baseEnd_2072935 := by
    simpa [prefixWord, tailWord_2072935, baseEnd_2072935] using wordTrace_append hprefix tailTrace_2072935
  have hstable : (prefixWord ++ tailWord_2072935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072935).length < 2 ^ (prefixWord ++ tailWord_2072935).sum := by decide
  have hdescent : baseEnd_2072935 < baseStart_2072935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073068 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_2073068 : Nat := 118140960795 + 2073068 * 2 ^ 59
def prefixEnd_2073068 : Nat := 4983230072969 + 3 ^ 40 * 2073068 * 2
def baseEnd_2073068 : Nat := 709653542303333563744093

theorem tailTrace_2073068 : CollatzResearch.WordTrace tailWord_2073068 prefixEnd_2073068 709653542303333563744093 := by
  unfold tailWord_2073068
  simp only [CollatzResearch.WordTrace]
  refine ⟨37805500826818081336001929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50407334435757441781335905 37805500826818081336001929)
  ·
    refine ⟨28354125620113561002001447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37805500826818081336001929 28354125620113561002001447)
    ·
      refine ⟨42531188430170341503002171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354125620113561002001447 42531188430170341503002171)
      ·
        refine ⟨63796782645255512254503257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42531188430170341503002171 63796782645255512254503257)
        ·
          refine ⟨47847586983941634190877443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63796782645255512254503257 47847586983941634190877443)
          ·
            refine ⟨71771380475912451286316165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47847586983941634190877443 71771380475912451286316165)
            ·
              refine ⟨13457133839233584616184281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71771380475912451286316165 13457133839233584616184281)
              ·
                refine ⟨10092850379425188462138211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13457133839233584616184281 10092850379425188462138211)
                ·
                  refine ⟨15139275569137782693207317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092850379425188462138211 15139275569137782693207317)
                  ·
                    refine ⟨709653542303333563744093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15139275569137782693207317 709653542303333563744093)
                    ·
                      rfl

theorem cell22_2073068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_2073068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073068 prefixEnd_2073068 := by exact prefixLift 2073068
  have htrace : WordTrace (prefixWord ++ tailWord_2073068) baseStart_2073068 baseEnd_2073068 := by
    simpa [prefixWord, tailWord_2073068, baseEnd_2073068] using wordTrace_append hprefix tailTrace_2073068
  have hstable : (prefixWord ++ tailWord_2073068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073068).length < 2 ^ (prefixWord ++ tailWord_2073068).sum := by decide
  have hdescent : baseEnd_2073068 < baseStart_2073068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073070 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2073070 : Nat := 118140960795 + 2073070 * 2 ^ 59
def prefixEnd_2073070 : Nat := 4983230072969 + 3 ^ 40 * 2073070 * 2
def baseEnd_2073070 : Nat := 709654226944206225194087

theorem tailTrace_2073070 : CollatzResearch.WordTrace tailWord_2073070 prefixEnd_2073070 709654226944206225194087 := by
  unfold tailWord_2073070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451384324953614626697083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50407383066419278009051109 9451384324953614626697083)
  ·
    refine ⟨14177076487430421940045625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451384324953614626697083 14177076487430421940045625)
    ·
      refine ⟨10632807365572816455034219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14177076487430421940045625 10632807365572816455034219)
      ·
        refine ⟨15949211048359224682551329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632807365572816455034219 15949211048359224682551329)
        ·
          refine ⟨11961908286269418511913497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949211048359224682551329 11961908286269418511913497)
          ·
            refine ⟨8971431214702063883935123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961908286269418511913497 8971431214702063883935123)
            ·
              refine ⟨13457146822053095825902685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971431214702063883935123 13457146822053095825902685)
              ·
                refine ⟨5046430058269910934713507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13457146822053095825902685 5046430058269910934713507)
                ·
                  refine ⟨7569645087404866402070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046430058269910934713507 7569645087404866402070261)
                  ·
                    refine ⟨709654226944206225194087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7569645087404866402070261 709654226944206225194087)
                    ·
                      rfl

theorem cell22_2073070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2073070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073070 prefixEnd_2073070 := by exact prefixLift 2073070
  have htrace : WordTrace (prefixWord ++ tailWord_2073070) baseStart_2073070 baseEnd_2073070 := by
    simpa [prefixWord, tailWord_2073070, baseEnd_2073070] using wordTrace_append hprefix tailTrace_2073070
  have hstable : (prefixWord ++ tailWord_2073070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073070).length < 2 ^ (prefixWord ++ tailWord_2073070).sum := by decide
  have hdescent : baseEnd_2073070 < baseStart_2073070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073134 : List Nat := [4, 1, 3, 1, 3, 2, 2, 6]
def baseStart_2073134 : Nat := 118140960795 + 2073134 * 2 ^ 59
def prefixEnd_2073134 : Nat := 4983230072969 + 3 ^ 40 * 2073134 * 2
def baseEnd_2073134 : Nat := 78852903939125710177099

theorem tailTrace_2073134 : CollatzResearch.WordTrace tailWord_2073134 prefixEnd_2073134 78852903939125710177099 := by
  unfold tailWord_2073134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451676108924631992988307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50408939247598037295937637 9451676108924631992988307)
  ·
    refine ⟨14177514163386947989482461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451676108924631992988307 14177514163386947989482461)
    ·
      refine ⟨5316567811270105496055923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14177514163386947989482461 5316567811270105496055923)
      ·
        refine ⟨7974851716905158244083885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316567811270105496055923 7974851716905158244083885)
        ·
          refine ⟨2990569393839434341531457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7974851716905158244083885 2990569393839434341531457)
          ·
            refine ⟨2242927045379575756148593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990569393839434341531457 2242927045379575756148593)
            ·
              refine ⟨1682195284034681817111445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242927045379575756148593 1682195284034681817111445)
              ·
                refine ⟨78852903939125710177099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1682195284034681817111445 78852903939125710177099)
                ·
                  rfl

theorem cell22_2073134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_2073134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073134 prefixEnd_2073134 := by exact prefixLift 2073134
  have htrace : WordTrace (prefixWord ++ tailWord_2073134) baseStart_2073134 baseEnd_2073134 := by
    simpa [prefixWord, tailWord_2073134, baseEnd_2073134] using wordTrace_append hprefix tailTrace_2073134
  have hstable : (prefixWord ++ tailWord_2073134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073134).length < 2 ^ (prefixWord ++ tailWord_2073134).sum := by decide
  have hdescent : baseEnd_2073134 < baseStart_2073134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073175 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2073175 : Nat := 118140960795 + 2073175 * 2 ^ 59
def prefixEnd_2073175 : Nat := 4983230072969 + 3 ^ 40 * 2073175 * 2
def baseEnd_2073175 : Nat := 709690170590020951318765

theorem tailTrace_2073175 : CollatzResearch.WordTrace tailWord_2073175 prefixEnd_2073175 709690170590020951318765 := by
  unfold tailWord_2073175
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614904264248519946148979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50409936176165679964099319 75614904264248519946148979)
  ·
    refine ⟨113422356396372779919223469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75614904264248519946148979 113422356396372779919223469)
    ·
      refine ⟨42533383648639792469708801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113422356396372779919223469 42533383648639792469708801)
      ·
        refine ⟨31900037736479844352281601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42533383648639792469708801 31900037736479844352281601)
        ·
          refine ⟨23925028302359883264211201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31900037736479844352281601 23925028302359883264211201)
          ·
            refine ⟨17943771226769912448158401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23925028302359883264211201 17943771226769912448158401)
            ·
              refine ⟨13457828420077434336118801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17943771226769912448158401 13457828420077434336118801)
              ·
                refine ⟨10093371315058075752089101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13457828420077434336118801 10093371315058075752089101)
                ·
                  refine ⟨3785014243146778407033413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10093371315058075752089101 3785014243146778407033413)
                  ·
                    refine ⟨709690170590020951318765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785014243146778407033413 709690170590020951318765)
                    ·
                      rfl

theorem cell22_2073175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2073175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073175 prefixEnd_2073175 := by exact prefixLift 2073175
  have htrace : WordTrace (prefixWord ++ tailWord_2073175) baseStart_2073175 baseEnd_2073175 := by
    simpa [prefixWord, tailWord_2073175, baseEnd_2073175] using wordTrace_append hprefix tailTrace_2073175
  have hstable : (prefixWord ++ tailWord_2073175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073175).length < 2 ^ (prefixWord ++ tailWord_2073175).sum := by decide
  have hdescent : baseEnd_2073175 < baseStart_2073175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073209 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_2073209 : Nat := 118140960795 + 2073209 * 2 ^ 59
def prefixEnd_2073209 : Nat := 4983230072969 + 3 ^ 40 * 2073209 * 2
def baseEnd_2073209 : Nat := 709701809484856195968661

theorem tailTrace_2073209 : CollatzResearch.WordTrace tailWord_2073209 prefixEnd_2073209 709701809484856195968661 := by
  unfold tailWord_2073209
  simp only [CollatzResearch.WordTrace]
  refine ⟨75616144346125343752886681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50410762897416895835257787 75616144346125343752886681)
  ·
    refine ⟨56712108259594007814665011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75616144346125343752886681 56712108259594007814665011)
    ·
      refine ⟨85068162389391011721997517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56712108259594007814665011 85068162389391011721997517)
      ·
        refine ⟨31900560896021629395749069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85068162389391011721997517 31900560896021629395749069)
        ·
          refine ⟨11962710336008111023405901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31900560896021629395749069 11962710336008111023405901)
          ·
            refine ⟨4486016376003041633777213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11962710336008111023405901 4486016376003041633777213)
            ·
              refine ⟨1682256141001140612666455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4486016376003041633777213 1682256141001140612666455)
              ·
                refine ⟨2523384211501710918999683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682256141001140612666455 2523384211501710918999683)
                ·
                  refine ⟨3785076317252566378499525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523384211501710918999683 3785076317252566378499525)
                  ·
                    refine ⟨709701809484856195968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785076317252566378499525 709701809484856195968661)
                    ·
                      rfl

theorem cell22_2073209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_2073209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073209 prefixEnd_2073209 := by exact prefixLift 2073209
  have htrace : WordTrace (prefixWord ++ tailWord_2073209) baseStart_2073209 baseEnd_2073209 := by
    simpa [prefixWord, tailWord_2073209, baseEnd_2073209] using wordTrace_append hprefix tailTrace_2073209
  have hstable : (prefixWord ++ tailWord_2073209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073209).length < 2 ^ (prefixWord ++ tailWord_2073209).sum := by decide
  have hdescent : baseEnd_2073209 < baseStart_2073209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073252 : List Nat := [2, 3, 1, 2, 2, 1, 5, 6]
def baseStart_2073252 : Nat := 118140960795 + 2073252 * 2 ^ 59
def prefixEnd_2073252 : Nat := 4983230072969 + 3 ^ 40 * 2073252 * 2
def baseEnd_2073252 : Nat := 78857392140402046349281

theorem tailTrace_2073252 : CollatzResearch.WordTrace tailWord_2073252 prefixEnd_2073252 78857392140402046349281 := by
  unfold tailWord_2073252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37808856342484781048351005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50411808456646374731134673 37808856342484781048351005)
  ·
    refine ⟨14178321128431792893131627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37808856342484781048351005 14178321128431792893131627)
    ·
      refine ⟨21267481692647689339697441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178321128431792893131627 21267481692647689339697441)
      ·
        refine ⟨15950611269485767004773081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21267481692647689339697441 15950611269485767004773081)
        ·
          refine ⟨11962958452114325253579811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15950611269485767004773081 11962958452114325253579811)
          ·
            refine ⟨17944437678171487880369717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962958452114325253579811 17944437678171487880369717)
            ·
              refine ⟨1682291032328576988784661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17944437678171487880369717 1682291032328576988784661)
              ·
                refine ⟨78857392140402046349281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1682291032328576988784661 78857392140402046349281)
                ·
                  rfl

theorem cell22_2073252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_2073252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073252 prefixEnd_2073252 := by exact prefixLift 2073252
  have htrace : WordTrace (prefixWord ++ tailWord_2073252) baseStart_2073252 baseEnd_2073252 := by
    simpa [prefixWord, tailWord_2073252, baseEnd_2073252] using wordTrace_append hprefix tailTrace_2073252
  have hstable : (prefixWord ++ tailWord_2073252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073252).length < 2 ^ (prefixWord ++ tailWord_2073252).sum := by decide
  have hdescent : baseEnd_2073252 < baseStart_2073252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073258 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_2073258 : Nat := 118140960795 + 2073258 * 2 ^ 59
def prefixEnd_2073258 : Nat := 4983230072969 + 3 ^ 40 * 2073258 * 2
def baseEnd_2073258 : Nat := 236572861062078800497837

theorem tailTrace_2073258 : CollatzResearch.WordTrace tailWord_2073258 prefixEnd_2073258 236572861062078800497837 := by
  unfold tailWord_2073258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904482880736956280355107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50411954348631883414280285 18904482880736956280355107)
  ·
    refine ⟨28356724321105434420532661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904482880736956280355107 28356724321105434420532661)
    ·
      refine ⟨2658442905103634476924937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28356724321105434420532661 2658442905103634476924937)
      ·
        refine ⟨1993832178827725857693703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2658442905103634476924937 1993832178827725857693703)
        ·
          refine ⟨2990748268241588786540555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993832178827725857693703 2990748268241588786540555)
          ·
            refine ⟨4486122402362383179810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990748268241588786540555 4486122402362383179810833)
            ·
              refine ⟨3364591801771787384858125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486122402362383179810833 3364591801771787384858125)
              ·
                refine ⟨1261721925664420269321797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3364591801771787384858125 1261721925664420269321797)
                ·
                  refine ⟨236572861062078800497837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261721925664420269321797 236572861062078800497837)
                  ·
                    rfl

theorem cell22_2073258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_2073258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073258 prefixEnd_2073258 := by exact prefixLift 2073258
  have htrace : WordTrace (prefixWord ++ tailWord_2073258) baseStart_2073258 baseEnd_2073258 := by
    simpa [prefixWord, tailWord_2073258, baseEnd_2073258] using wordTrace_append hprefix tailTrace_2073258
  have hstable : (prefixWord ++ tailWord_2073258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073258).length < 2 ^ (prefixWord ++ tailWord_2073258).sum := by decide
  have hdescent : baseEnd_2073258 < baseStart_2073258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073284 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2073284 : Nat := 118140960795 + 2073284 * 2 ^ 59
def prefixEnd_2073284 : Nat := 4983230072969 + 3 ^ 40 * 2073284 * 2
def baseEnd_2073284 : Nat := 709727483517581000343431

theorem tailTrace_2073284 : CollatzResearch.WordTrace tailWord_2073284 prefixEnd_2073284 709727483517581000343431 := by
  unfold tailWord_2073284
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809439910426815780933453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50412586547235754374577937 37809439910426815780933453)
  ·
    refine ⟨14178539966410055917850045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37809439910426815780933453 14178539966410055917850045)
    ·
      refine ⟨5316952487403770969193767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14178539966410055917850045 5316952487403770969193767)
      ·
        refine ⟨7975428731105656453790651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316952487403770969193767 7975428731105656453790651)
        ·
          refine ⟨11963143096658484680685977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975428731105656453790651 11963143096658484680685977)
          ·
            refine ⟨8972357322493863510514483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963143096658484680685977 8972357322493863510514483)
            ·
              refine ⟨13458535983740795265771725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972357322493863510514483 13458535983740795265771725)
              ·
                refine ⟨5046950993902798224664397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13458535983740795265771725 5046950993902798224664397)
                ·
                  refine ⟨1892606622713549334249149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5046950993902798224664397 1892606622713549334249149)
                  ·
                    refine ⟨709727483517581000343431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892606622713549334249149 709727483517581000343431)
                    ·
                      rfl

theorem cell22_2073284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2073284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073284 prefixEnd_2073284 := by exact prefixLift 2073284
  have htrace : WordTrace (prefixWord ++ tailWord_2073284) baseStart_2073284 baseEnd_2073284 := by
    simpa [prefixWord, tailWord_2073284, baseEnd_2073284] using wordTrace_append hprefix tailTrace_2073284
  have hstable : (prefixWord ++ tailWord_2073284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073284).length < 2 ^ (prefixWord ++ tailWord_2073284).sum := by decide
  have hdescent : baseEnd_2073284 < baseStart_2073284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073517 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2073517 : Nat := 118140960795 + 2073517 * 2 ^ 59
def prefixEnd_2073517 : Nat := 4983230072969 + 3 ^ 40 * 2073517 * 2
def baseEnd_2073517 : Nat := 236602414726415353089239

theorem tailTrace_2073517 : CollatzResearch.WordTrace tailWord_2073517 prefixEnd_2073517 236602414726415353089239 := by
  unfold tailWord_2073517
  simp only [CollatzResearch.WordTrace]
  refine ⟨75627378029009512355098805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50418252019339674903399203 75627378029009512355098805)
  ·
    refine ⟨7090066690219641783290513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75627378029009512355098805 7090066690219641783290513)
    ·
      refine ⟨5317550017664731337467885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7090066690219641783290513 5317550017664731337467885)
      ·
        refine ⟨1994081256624274251550457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5317550017664731337467885 1994081256624274251550457)
        ·
          refine ⟨1495560942468205688662843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994081256624274251550457 1495560942468205688662843)
          ·
            refine ⟨2243341413702308532994265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495560942468205688662843 2243341413702308532994265)
            ·
              refine ⟨1682506060276731399745699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243341413702308532994265 1682506060276731399745699)
              ·
                refine ⟨2523759090415097099618549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682506060276731399745699 2523759090415097099618549)
                ·
                  refine ⟨236602414726415353089239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2523759090415097099618549 236602414726415353089239)
                  ·
                    rfl

theorem cell22_2073517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2073517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073517 prefixEnd_2073517 := by exact prefixLift 2073517
  have htrace : WordTrace (prefixWord ++ tailWord_2073517) baseStart_2073517 baseEnd_2073517 := by
    simpa [prefixWord, tailWord_2073517, baseEnd_2073517] using wordTrace_append hprefix tailTrace_2073517
  have hstable : (prefixWord ++ tailWord_2073517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073517).length < 2 ^ (prefixWord ++ tailWord_2073517).sum := by decide
  have hdescent : baseEnd_2073517 < baseStart_2073517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073558 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2073558 : Nat := 118140960795 + 2073558 * 2 ^ 59
def prefixEnd_2073558 : Nat := 4983230072969 + 3 ^ 40 * 2073558 * 2
def baseEnd_2073558 : Nat := 709821279317135618992591

theorem tailTrace_2073558 : CollatzResearch.WordTrace tailWord_2073558 prefixEnd_2073558 709821279317135618992591 := by
  unfold tailWord_2073558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726804588866311022333833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50419248947907317571560885 4726804588866311022333833)
  ·
    refine ⟨3545103441649733266750375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4726804588866311022333833 3545103441649733266750375)
    ·
      refine ⟨5317655162474599900125563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545103441649733266750375 5317655162474599900125563)
      ·
        refine ⟨7976482743711899850188345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317655162474599900125563 7976482743711899850188345)
        ·
          refine ⟨5982362057783924887641259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976482743711899850188345 5982362057783924887641259)
          ·
            refine ⟨8973543086675887331461889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982362057783924887641259 8973543086675887331461889)
            ·
              refine ⟨6730157315006915498596417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973543086675887331461889 6730157315006915498596417)
              ·
                refine ⟨5047617986255186623947313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730157315006915498596417 5047617986255186623947313)
                ·
                  refine ⟨3785713489691389967960485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047617986255186623947313 3785713489691389967960485)
                  ·
                    refine ⟨709821279317135618992591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785713489691389967960485 709821279317135618992591)
                    ·
                      rfl

theorem cell22_2073558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2073558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073558 prefixEnd_2073558 := by exact prefixLift 2073558
  have htrace : WordTrace (prefixWord ++ tailWord_2073558) baseStart_2073558 baseEnd_2073558 := by
    simpa [prefixWord, tailWord_2073558, baseEnd_2073558] using wordTrace_append hprefix tailTrace_2073558
  have hstable : (prefixWord ++ tailWord_2073558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073558).length < 2 ^ (prefixWord ++ tailWord_2073558).sum := by decide
  have hdescent : baseEnd_2073558 < baseStart_2073558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073571 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 3, 3]
def baseStart_2073571 : Nat := 118140960795 + 2073571 * 2 ^ 59
def prefixEnd_2073571 : Nat := 4983230072969 + 3 ^ 40 * 2073571 * 2
def baseEnd_2073571 : Nat := 709825729482807918417551

theorem tailTrace_2073571 : CollatzResearch.WordTrace tailWord_2073571 prefixEnd_2073571 709825729482807918417551 := by
  unfold tailWord_2073571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75629347570813879577564567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50419565047209253051709711 75629347570813879577564567)
  ·
    refine ⟨113444021356220819366346851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75629347570813879577564567 113444021356220819366346851)
    ·
      refine ⟨170166032034331229049520277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113444021356220819366346851 170166032034331229049520277)
      ·
        refine ⟨7976532751609276361696263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170166032034331229049520277 7976532751609276361696263)
        ·
          refine ⟨11964799127413914542544395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976532751609276361696263 11964799127413914542544395)
          ·
            refine ⟨17947198691120871813816593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964799127413914542544395 17947198691120871813816593)
            ·
              refine ⟨13460399018340653860362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17947198691120871813816593 13460399018340653860362445)
              ·
                refine ⟨5047649631877745197635917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13460399018340653860362445 5047649631877745197635917)
                ·
                  refine ⟨1892868611954154449113469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5047649631877745197635917 1892868611954154449113469)
                  ·
                    refine ⟨709825729482807918417551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892868611954154449113469 709825729482807918417551)
                    ·
                      rfl

theorem cell22_2073571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].length) (baseStart_2073571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073571 prefixEnd_2073571 := by exact prefixLift 2073571
  have htrace : WordTrace (prefixWord ++ tailWord_2073571) baseStart_2073571 baseEnd_2073571 := by
    simpa [prefixWord, tailWord_2073571, baseEnd_2073571] using wordTrace_append hprefix tailTrace_2073571
  have hstable : (prefixWord ++ tailWord_2073571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073571).length < 2 ^ (prefixWord ++ tailWord_2073571).sum := by decide
  have hdescent : baseEnd_2073571 < baseStart_2073571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073573 : List Nat := [1, 3, 1, 6, 1, 2, 1, 7]
def baseStart_2073573 : Nat := 118140960795 + 2073573 * 2 ^ 59
def prefixEnd_2073573 : Nat := 4983230072969 + 3 ^ 40 * 2073573 * 2
def baseEnd_2073573 : Nat := 78869601569297842207505

theorem tailTrace_2073573 : CollatzResearch.WordTrace tailWord_2073573 prefixEnd_2073573 78869601569297842207505 := by
  unfold tailWord_2073573
  simp only [CollatzResearch.WordTrace]
  refine ⟨75629420516806633919137373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50419613677871089279424915 75629420516806633919137373)
  ·
    refine ⟨28361032693802487719676515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75629420516806633919137373 28361032693802487719676515)
    ·
      refine ⟨42541549040703731579514773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28361032693802487719676515 42541549040703731579514773)
      ·
        refine ⟨1994135111282987417789755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42541549040703731579514773 1994135111282987417789755)
        ·
          refine ⟨2991202666924481126684633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994135111282987417789755 2991202666924481126684633)
          ·
            refine ⟨2243402000193360845013475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991202666924481126684633 2243402000193360845013475)
            ·
              refine ⟨3365103000290041267520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243402000193360845013475 3365103000290041267520213)
              ·
                refine ⟨78869601569297842207505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3365103000290041267520213 78869601569297842207505)
                ·
                  rfl

theorem cell22_2073573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 7].length) (baseStart_2073573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073573 prefixEnd_2073573 := by exact prefixLift 2073573
  have htrace : WordTrace (prefixWord ++ tailWord_2073573) baseStart_2073573 baseEnd_2073573 := by
    simpa [prefixWord, tailWord_2073573, baseEnd_2073573] using wordTrace_append hprefix tailTrace_2073573
  have hstable : (prefixWord ++ tailWord_2073573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073573).length < 2 ^ (prefixWord ++ tailWord_2073573).sum := by decide
  have hdescent : baseEnd_2073573 < baseStart_2073573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073646 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2073646 : Nat := 118140960795 + 2073646 * 2 ^ 59
def prefixEnd_2073646 : Nat := 4983230072969 + 3 ^ 40 * 2073646 * 2
def baseEnd_2073646 : Nat := 236617134505177574264107

theorem tailTrace_2073646 : CollatzResearch.WordTrace tailWord_2073646 prefixEnd_2073646 236617134505177574264107 := by
  unfold tailWord_2073646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454010380692770923318099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50421388697028111591029861 9454010380692770923318099)
  ·
    refine ⟨14181015571039156384977149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454010380692770923318099 14181015571039156384977149)
    ·
      refine ⟨5317880839139683644366431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14181015571039156384977149 5317880839139683644366431)
      ·
        refine ⟨7976821258709525466549647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317880839139683644366431 7976821258709525466549647)
        ·
          refine ⟨11965231888064288199824471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976821258709525466549647 11965231888064288199824471)
          ·
            refine ⟨17947847832096432299736707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965231888064288199824471 17947847832096432299736707)
            ·
              refine ⟨26921771748144648449605061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947847832096432299736707 26921771748144648449605061)
              ·
                refine ⟨5047832202777121584300949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26921771748144648449605061 5047832202777121584300949)
                ·
                  refine ⟨236617134505177574264107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5047832202777121584300949 236617134505177574264107)
                  ·
                    rfl

theorem cell22_2073646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2073646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073646 prefixEnd_2073646 := by exact prefixLift 2073646
  have htrace : WordTrace (prefixWord ++ tailWord_2073646) baseStart_2073646 baseEnd_2073646 := by
    simpa [prefixWord, tailWord_2073646, baseEnd_2073646] using wordTrace_append hprefix tailTrace_2073646
  have hstable : (prefixWord ++ tailWord_2073646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073646).length < 2 ^ (prefixWord ++ tailWord_2073646).sum := by decide
  have hdescent : baseEnd_2073646 < baseStart_2073646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073674 : List Nat := [3, 1, 2, 1, 1, 2, 12]
def baseStart_2073674 : Nat := 118140960795 + 2073674 * 2 ^ 59
def prefixEnd_2073674 : Nat := 4983230072969 + 3 ^ 40 * 2073674 * 2
def baseEnd_2073674 : Nat := 26291147721768517892305

theorem tailTrace_2073674 : CollatzResearch.WordTrace tailWord_2073674 prefixEnd_2073674 26291147721768517892305 := by
  unfold tailWord_2073674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908276072360182042141019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50422069526293818779042717 18908276072360182042141019)
  ·
    refine ⟨28362414108540273063211529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18908276072360182042141019 28362414108540273063211529)
    ·
      refine ⟨21271810581405204797408647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28362414108540273063211529 21271810581405204797408647)
      ·
        refine ⟨31907715872107807196112971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21271810581405204797408647 31907715872107807196112971)
        ·
          refine ⟨47861573808161710794169457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31907715872107807196112971 47861573808161710794169457)
          ·
            refine ⟨35896180356121283095627093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47861573808161710794169457 35896180356121283095627093)
            ·
              refine ⟨26291147721768517892305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35896180356121283095627093 26291147721768517892305)
              ·
                rfl

theorem cell22_2073674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 12].length) (baseStart_2073674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073674 prefixEnd_2073674 := by exact prefixLift 2073674
  have htrace : WordTrace (prefixWord ++ tailWord_2073674) baseStart_2073674 baseEnd_2073674 := by
    simpa [prefixWord, tailWord_2073674, baseEnd_2073674] using wordTrace_append hprefix tailTrace_2073674
  have hstable : (prefixWord ++ tailWord_2073674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073674).length < 2 ^ (prefixWord ++ tailWord_2073674).sum := by decide
  have hdescent : baseEnd_2073674 < baseStart_2073674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073678 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2073678 : Nat := 118140960795 + 2073678 * 2 ^ 59
def prefixEnd_2073678 : Nat := 4983230072969 + 3 ^ 40 * 2073678 * 2
def baseEnd_2073678 : Nat := 709862357769495305992223

theorem tailTrace_2073678 : CollatzResearch.WordTrace tailWord_2073678 prefixEnd_2073678 709862357769495305992223 := by
  unfold tailWord_2073678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454156272678279606463711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50422166787617491234473125 9454156272678279606463711)
  ·
    refine ⟨14181234409017419409695567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454156272678279606463711 14181234409017419409695567)
    ·
      refine ⟨21271851613526129114543351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181234409017419409695567 21271851613526129114543351)
      ·
        refine ⟨31907777420289193671815027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21271851613526129114543351 31907777420289193671815027)
        ·
          refine ⟨47861666130433790507722541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31907777420289193671815027 47861666130433790507722541)
          ·
            refine ⟨17948124798912671440395953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47861666130433790507722541 17948124798912671440395953)
            ·
              refine ⟨13461093599184503580296965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17948124798912671440395953 13461093599184503580296965)
              ·
                refine ⟨2523955049847094421305681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13461093599184503580296965 2523955049847094421305681)
                ·
                  refine ⟨1892966287385320815979261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523955049847094421305681 1892966287385320815979261)
                  ·
                    refine ⟨709862357769495305992223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892966287385320815979261 709862357769495305992223)
                    ·
                      rfl

theorem cell22_2073678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2073678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073678 prefixEnd_2073678 := by exact prefixLift 2073678
  have htrace : WordTrace (prefixWord ++ tailWord_2073678) baseStart_2073678 baseEnd_2073678 := by
    simpa [prefixWord, tailWord_2073678, baseEnd_2073678] using wordTrace_append hprefix tailTrace_2073678
  have hstable : (prefixWord ++ tailWord_2073678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073678).length < 2 ^ (prefixWord ++ tailWord_2073678).sum := by decide
  have hdescent : baseEnd_2073678 < baseStart_2073678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_2073689 : Nat := 118140960795 + 2073689 * 2 ^ 59
def prefixEnd_2073689 : Nat := 4983230072969 + 3 ^ 40 * 2073689 * 2
def baseEnd_2073689 : Nat := 709866123294294943967189

theorem tailTrace_2073689 : CollatzResearch.WordTrace tailWord_2073689 prefixEnd_2073689 709866123294294943967189 := by
  unfold tailWord_2073689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75633651384386385730360121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50422434256257590486906747 75633651384386385730360121)
  ·
    refine ⟨56725238538289789297770091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75633651384386385730360121 56725238538289789297770091)
    ·
      refine ⟨85087857807434683946655137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56725238538289789297770091 85087857807434683946655137)
      ·
        refine ⟨63815893355576012959991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85087857807434683946655137 63815893355576012959991353)
        ·
          refine ⟨47861920016682009719993515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63815893355576012959991353 47861920016682009719993515)
          ·
            refine ⟨71792880025023014579990273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47861920016682009719993515 71792880025023014579990273)
            ·
              refine ⟨53844660018767260934992705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71792880025023014579990273 53844660018767260934992705)
              ·
                refine ⟨40383495014075445701244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53844660018767260934992705 40383495014075445701244529)
                ·
                  refine ⟨30287621260556584275933397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40383495014075445701244529 30287621260556584275933397)
                  ·
                    refine ⟨709866123294294943967189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30287621260556584275933397 709866123294294943967189)
                    ·
                      rfl

theorem cell22_2073689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_2073689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073689 prefixEnd_2073689 := by exact prefixLift 2073689
  have htrace : WordTrace (prefixWord ++ tailWord_2073689) baseStart_2073689 baseEnd_2073689 := by
    simpa [prefixWord, tailWord_2073689, baseEnd_2073689] using wordTrace_append hprefix tailTrace_2073689
  have hstable : (prefixWord ++ tailWord_2073689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073689).length < 2 ^ (prefixWord ++ tailWord_2073689).sum := by decide
  have hdescent : baseEnd_2073689 < baseStart_2073689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073751 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2073751 : Nat := 118140960795 + 2073751 * 2 ^ 59
def prefixEnd_2073751 : Nat := 4983230072969 + 3 ^ 40 * 2073751 * 2
def baseEnd_2073751 : Nat := 709887347161347448916999

theorem tailTrace_2073751 : CollatzResearch.WordTrace tailWord_2073751 prefixEnd_2073751 709887347161347448916999 := by
  unfold tailWord_2073751
  simp only [CollatzResearch.WordTrace]
  refine ⟨75635912710161770319117107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50423941806774513546078071 75635912710161770319117107)
  ·
    refine ⟨113453869065242655478675661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75635912710161770319117107 113453869065242655478675661)
    ·
      refine ⟨42545200899465995804503373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113453869065242655478675661 42545200899465995804503373)
      ·
        refine ⟨15954450337299748426688765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42545200899465995804503373 15954450337299748426688765)
        ·
          refine ⟨5982918876487405660008287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15954450337299748426688765 5982918876487405660008287)
          ·
            refine ⟨8974378314731108490012431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982918876487405660008287 8974378314731108490012431)
            ·
              refine ⟨13461567472096662735018647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974378314731108490012431 13461567472096662735018647)
              ·
                refine ⟨20192351208144994102527971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461567472096662735018647 20192351208144994102527971)
                ·
                  refine ⟨30288526812217491153791957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20192351208144994102527971 30288526812217491153791957)
                  ·
                    refine ⟨709887347161347448916999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30288526812217491153791957 709887347161347448916999)
                    ·
                      rfl

theorem cell22_2073751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2073751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073751 prefixEnd_2073751 := by exact prefixLift 2073751
  have htrace : WordTrace (prefixWord ++ tailWord_2073751) baseStart_2073751 baseEnd_2073751 := by
    simpa [prefixWord, tailWord_2073751, baseEnd_2073751] using wordTrace_append hprefix tailTrace_2073751
  have hstable : (prefixWord ++ tailWord_2073751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073751).length < 2 ^ (prefixWord ++ tailWord_2073751).sum := by decide
  have hdescent : baseEnd_2073751 < baseStart_2073751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073783 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2073783 : Nat := 118140960795 + 2073783 * 2 ^ 59
def prefixEnd_2073783 : Nat := 4983230072969 + 3 ^ 40 * 2073783 * 2
def baseEnd_2073783 : Nat := 709898301415310032116901

theorem tailTrace_2073783 : CollatzResearch.WordTrace tailWord_2073783 prefixEnd_2073783 709898301415310032116901 := by
  unfold tailWord_2073783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75637079846045839784282003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50424719897363893189521335 75637079846045839784282003)
  ·
    refine ⟨113455619769068759676423005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75637079846045839784282003 113455619769068759676423005)
    ·
      refine ⟨42545857413400784878658627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113455619769068759676423005 42545857413400784878658627)
      ·
        refine ⟨63818786120101177317987941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42545857413400784878658627 63818786120101177317987941)
        ·
          refine ⟨11966022397518970747122739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63818786120101177317987941 11966022397518970747122739)
          ·
            refine ⟨17949033596278456120684109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966022397518970747122739 17949033596278456120684109)
            ·
              refine ⟨6730887598604421045256541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949033596278456120684109 6730887598604421045256541)
              ·
                refine ⟨2524082849476657891971203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6730887598604421045256541 2524082849476657891971203)
                ·
                  refine ⟨3786124274214986837956805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524082849476657891971203 3786124274214986837956805)
                  ·
                    refine ⟨709898301415310032116901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786124274214986837956805 709898301415310032116901)
                    ·
                      rfl

theorem cell22_2073783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2073783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073783 prefixEnd_2073783 := by exact prefixLift 2073783
  have htrace : WordTrace (prefixWord ++ tailWord_2073783) baseStart_2073783 baseEnd_2073783 := by
    simpa [prefixWord, tailWord_2073783, baseEnd_2073783] using wordTrace_append hprefix tailTrace_2073783
  have hstable : (prefixWord ++ tailWord_2073783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073783).length < 2 ^ (prefixWord ++ tailWord_2073783).sum := by decide
  have hdescent : baseEnd_2073783 < baseStart_2073783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_2073811 : Nat := 118140960795 + 2073811 * 2 ^ 59
def prefixEnd_2073811 : Nat := 4983230072969 + 3 ^ 40 * 2073811 * 2
def baseEnd_2073811 : Nat := 709907886387527292416815

theorem tailTrace_2073811 : CollatzResearch.WordTrace tailWord_2073811 prefixEnd_2073811 709907886387527292416815 := by
  unfold tailWord_2073811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75638101089944400566301287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50425400726629600377534191 75638101089944400566301287)
  ·
    refine ⟨113457151634916600849451931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75638101089944400566301287 113457151634916600849451931)
    ·
      refine ⟨170185727452374901274177897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113457151634916600849451931 170185727452374901274177897)
      ·
        refine ⟨127639295589281175955633423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170185727452374901274177897 127639295589281175955633423)
        ·
          refine ⟨191458943383921763933450135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127639295589281175955633423 191458943383921763933450135)
          ·
            refine ⟨287188415075882645900175203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191458943383921763933450135 287188415075882645900175203)
            ·
              refine ⟨430782622613823968850262805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287188415075882645900175203 430782622613823968850262805)
              ·
                refine ⟨20192935435022998539856069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430782622613823968850262805 20192935435022998539856069)
                ·
                  refine ⟨3786175394066812226223013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20192935435022998539856069 3786175394066812226223013)
                  ·
                    refine ⟨709907886387527292416815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786175394066812226223013 709907886387527292416815)
                    ·
                      rfl

theorem cell22_2073811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_2073811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073811 prefixEnd_2073811 := by exact prefixLift 2073811
  have htrace : WordTrace (prefixWord ++ tailWord_2073811) baseStart_2073811 baseEnd_2073811 := by
    simpa [prefixWord, tailWord_2073811, baseEnd_2073811] using wordTrace_append hprefix tailTrace_2073811
  have hstable : (prefixWord ++ tailWord_2073811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073811).length < 2 ^ (prefixWord ++ tailWord_2073811).sum := by decide
  have hdescent : baseEnd_2073811 < baseStart_2073811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073856 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_2073856 : Nat := 118140960795 + 2073856 * 2 ^ 59
def prefixEnd_2073856 : Nat := 4983230072969 + 3 ^ 40 * 2073856 * 2
def baseEnd_2073856 : Nat := 709923290807162175041677

theorem tailTrace_2073856 : CollatzResearch.WordTrace tailWord_2073856 prefixEnd_2073856 709923290807162175041677 := by
  unfold tailWord_2073856
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819871187390686625844711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50426494916520915501126281 37819871187390686625844711)
  ·
    refine ⟨56729806781086029938767067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37819871187390686625844711 56729806781086029938767067)
    ·
      refine ⟨85094710171629044908150601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56729806781086029938767067 85094710171629044908150601)
      ·
        refine ⟨63821032628721783681112951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85094710171629044908150601 63821032628721783681112951)
        ·
          refine ⟨95731548943082675521669427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63821032628721783681112951 95731548943082675521669427)
          ·
            refine ⟨143597323414624013282504141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95731548943082675521669427 143597323414624013282504141)
            ·
              refine ⟨53848996280484004980939053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143597323414624013282504141 53848996280484004980939053)
              ·
                refine ⟨20193373605181501867852145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53848996280484004980939053 20193373605181501867852145)
                ·
                  refine ⟨15145030203886126400889109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20193373605181501867852145 15145030203886126400889109)
                  ·
                    refine ⟨709923290807162175041677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15145030203886126400889109 709923290807162175041677)
                    ·
                      rfl

theorem cell22_2073856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_2073856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073856 prefixEnd_2073856 := by exact prefixLift 2073856
  have htrace : WordTrace (prefixWord ++ tailWord_2073856) baseStart_2073856 baseEnd_2073856 := by
    simpa [prefixWord, tailWord_2073856, baseEnd_2073856] using wordTrace_append hprefix tailTrace_2073856
  have hstable : (prefixWord ++ tailWord_2073856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073856).length < 2 ^ (prefixWord ++ tailWord_2073856).sum := by decide
  have hdescent : baseEnd_2073856 < baseStart_2073856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073864 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2073864 : Nat := 118140960795 + 2073864 * 2 ^ 59
def prefixEnd_2073864 : Nat := 4983230072969 + 3 ^ 40 * 2073864 * 2
def baseEnd_2073864 : Nat := 709926029370652820841653

theorem tailTrace_2073864 : CollatzResearch.WordTrace tailWord_2073864 prefixEnd_2073864 709926029370652820841653 := by
  unfold tailWord_2073864
  simp only [CollatzResearch.WordTrace]
  refine ⟨37820017079376195308990323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50426689439168260411987097 37820017079376195308990323)
  ·
    refine ⟨56730025619064292963485485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37820017079376195308990323 56730025619064292963485485)
    ·
      refine ⟨21273759607149109861307057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56730025619064292963485485 21273759607149109861307057)
      ·
        refine ⟨15955319705361832395980293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21273759607149109861307057 15955319705361832395980293)
        ·
          refine ⟨2991622444755343574246305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15955319705361832395980293 2991622444755343574246305)
          ·
            refine ⟨2243716833566507680684729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991622444755343574246305 2243716833566507680684729)
            ·
              refine ⟨1682787625174880760513547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243716833566507680684729 1682787625174880760513547)
              ·
                refine ⟨2524181437762321140770321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682787625174880760513547 2524181437762321140770321)
                ·
                  refine ⟨1893136078321740855577741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2524181437762321140770321 1893136078321740855577741)
                  ·
                    refine ⟨709926029370652820841653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893136078321740855577741 709926029370652820841653)
                    ·
                      rfl

theorem cell22_2073864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2073864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073864 prefixEnd_2073864 := by exact prefixLift 2073864
  have htrace : WordTrace (prefixWord ++ tailWord_2073864) baseStart_2073864 baseEnd_2073864 := by
    simpa [prefixWord, tailWord_2073864, baseEnd_2073864] using wordTrace_append hprefix tailTrace_2073864
  have hstable : (prefixWord ++ tailWord_2073864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073864).length < 2 ^ (prefixWord ++ tailWord_2073864).sum := by decide
  have hdescent : baseEnd_2073864 < baseStart_2073864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073892 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_2073892 : Nat := 118140960795 + 2073892 * 2 ^ 59
def prefixEnd_2073892 : Nat := 4983230072969 + 3 ^ 40 * 2073892 * 2
def baseEnd_2073892 : Nat := 709935614342870081141567

theorem tailTrace_2073892 : CollatzResearch.WordTrace tailWord_2073892 prefixEnd_2073892 709935614342870081141567 := by
  unfold tailWord_2073892
  simp only [CollatzResearch.WordTrace]
  refine ⟨37820527701325475699999965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50427370268433967599999953 37820527701325475699999965)
  ·
    refine ⟨14182697887997053387499987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37820527701325475699999965 14182697887997053387499987)
    ·
      refine ⟨21274046831995580081249981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14182697887997053387499987 21274046831995580081249981)
      ·
        refine ⟨7977767561998342530468743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21274046831995580081249981 7977767561998342530468743)
        ·
          refine ⟨11966651342997513795703115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977767561998342530468743 11966651342997513795703115)
          ·
            refine ⟨17949977014496270693554673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966651342997513795703115 17949977014496270693554673)
            ·
              refine ⟨13462482760872203020166005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17949977014496270693554673 13462482760872203020166005)
              ·
                refine ⟨1262107758831769033140563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13462482760872203020166005 1262107758831769033140563)
                ·
                  refine ⟨1893161638247653549710845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262107758831769033140563 1893161638247653549710845)
                  ·
                    refine ⟨709935614342870081141567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893161638247653549710845 709935614342870081141567)
                    ·
                      rfl

theorem cell22_2073892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_2073892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073892 prefixEnd_2073892 := by exact prefixLift 2073892
  have htrace : WordTrace (prefixWord ++ tailWord_2073892) baseStart_2073892 baseEnd_2073892 := by
    simpa [prefixWord, tailWord_2073892, baseEnd_2073892] using wordTrace_append hprefix tailTrace_2073892
  have hstable : (prefixWord ++ tailWord_2073892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073892).length < 2 ^ (prefixWord ++ tailWord_2073892).sum := by decide
  have hdescent : baseEnd_2073892 < baseStart_2073892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073905 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 5]
def baseStart_2073905 : Nat := 118140960795 + 2073905 * 2 ^ 59
def prefixEnd_2073905 : Nat := 4983230072969 + 3 ^ 40 * 2073905 * 2
def baseEnd_2073905 : Nat := 236646688169514126855509

theorem tailTrace_2073905 : CollatzResearch.WordTrace tailWord_2073905 prefixEnd_2073905 236646688169514126855509 := by
  unfold tailWord_2073905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641529551603854620223169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50427686367735903080148779 75641529551603854620223169)
  ·
    refine ⟨56731147163702890965167377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75641529551603854620223169 56731147163702890965167377)
    ·
      refine ⟨42548360372777168223875533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56731147163702890965167377 42548360372777168223875533)
      ·
        refine ⟨15955635139791438083953325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42548360372777168223875533 15955635139791438083953325)
        ·
          refine ⟨5983363177421789281482497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15955635139791438083953325 5983363177421789281482497)
          ·
            refine ⟨4487522383066341961111873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983363177421789281482497 4487522383066341961111873)
            ·
              refine ⟨3365641787299756470833905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487522383066341961111873 3365641787299756470833905)
              ·
                refine ⟨2524231340474817353125429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365641787299756470833905 2524231340474817353125429)
                ·
                  refine ⟨236646688169514126855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2524231340474817353125429 236646688169514126855509)
                  ·
                    rfl

theorem cell22_2073905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_2073905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073905 prefixEnd_2073905 := by exact prefixLift 2073905
  have htrace : WordTrace (prefixWord ++ tailWord_2073905) baseStart_2073905 baseEnd_2073905 := by
    simpa [prefixWord, tailWord_2073905, baseEnd_2073905] using wordTrace_append hprefix tailTrace_2073905
  have hstable : (prefixWord ++ tailWord_2073905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073905).length < 2 ^ (prefixWord ++ tailWord_2073905).sum := by decide
  have hdescent : baseEnd_2073905 < baseStart_2073905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073909 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2073909 : Nat := 118140960795 + 2073909 * 2 ^ 59
def prefixEnd_2073909 : Nat := 4983230072969 + 3 ^ 40 * 2073909 * 2
def baseEnd_2073909 : Nat := 709941433790287703466515

theorem tailTrace_2073909 : CollatzResearch.WordTrace tailWord_2073909 prefixEnd_2073909 709941433790287703466515 := by
  unfold tailWord_2073909
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641675443589363303368781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50427783629059575535579187 75641675443589363303368781)
  ·
    refine ⟨28365628291346011238763293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75641675443589363303368781 28365628291346011238763293)
    ·
      refine ⟨10637110609254754214536235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28365628291346011238763293 10637110609254754214536235)
      ·
        refine ⟨15955665913882131321804353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10637110609254754214536235 15955665913882131321804353)
        ·
          refine ⟨11966749435411598491353265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15955665913882131321804353 11966749435411598491353265)
          ·
            refine ⟨8975062076558698868514949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966749435411598491353265 8975062076558698868514949)
            ·
              refine ⟨1682824139354756037846553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8975062076558698868514949 1682824139354756037846553)
              ·
                refine ⟨1262118104516067028384915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682824139354756037846553 1262118104516067028384915)
                ·
                  refine ⟨1893177156774100542577373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262118104516067028384915 1893177156774100542577373)
                  ·
                    refine ⟨709941433790287703466515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893177156774100542577373 709941433790287703466515)
                    ·
                      rfl

theorem cell22_2073909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2073909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073909 prefixEnd_2073909 := by exact prefixLift 2073909
  have htrace : WordTrace (prefixWord ++ tailWord_2073909) baseStart_2073909 baseEnd_2073909 := by
    simpa [prefixWord, tailWord_2073909, baseEnd_2073909] using wordTrace_append hprefix tailTrace_2073909
  have hstable : (prefixWord ++ tailWord_2073909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073909).length < 2 ^ (prefixWord ++ tailWord_2073909).sum := by decide
  have hdescent : baseEnd_2073909 < baseStart_2073909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073926 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2073926 : Nat := 118140960795 + 2073926 * 2 ^ 59
def prefixEnd_2073926 : Nat := 4983230072969 + 3 ^ 40 * 2073926 * 2
def baseEnd_2073926 : Nat := 709947253237705325791463

theorem tailTrace_2073926 : CollatzResearch.WordTrace tailWord_2073926 prefixEnd_2073926 709947253237705325791463 := by
  unfold tailWord_2073926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363821733891492975210551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50428196989685183471158421 2363821733891492975210551)
  ·
    refine ⟨3545732600837239462815827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363821733891492975210551 3545732600837239462815827)
    ·
      refine ⟨5318598901255859194223741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545732600837239462815827 5318598901255859194223741)
      ·
        refine ⟨1994474587970947197833903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5318598901255859194223741 1994474587970947197833903)
        ·
          refine ⟨2991711881956420796750855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994474587970947197833903 2991711881956420796750855)
          ·
            refine ⟨4487567822934631195126283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991711881956420796750855 4487567822934631195126283)
            ·
              refine ⟨6731351734401946792689425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487567822934631195126283 6731351734401946792689425)
              ·
                refine ⟨5048513800801460094517069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731351734401946792689425 5048513800801460094517069)
                ·
                  refine ⟨1893192675300547535443901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5048513800801460094517069 1893192675300547535443901)
                  ·
                    refine ⟨709947253237705325791463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893192675300547535443901 709947253237705325791463)
                    ·
                      rfl

theorem cell22_2073926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2073926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073926 prefixEnd_2073926 := by exact prefixLift 2073926
  have htrace : WordTrace (prefixWord ++ tailWord_2073926) baseStart_2073926 baseEnd_2073926 := by
    simpa [prefixWord, tailWord_2073926, baseEnd_2073926] using wordTrace_append hprefix tailTrace_2073926
  have hstable : (prefixWord ++ tailWord_2073926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073926).length < 2 ^ (prefixWord ++ tailWord_2073926).sum := by decide
  have hdescent : baseEnd_2073926 < baseStart_2073926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073952 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_2073952 : Nat := 118140960795 + 2073952 * 2 ^ 59
def prefixEnd_2073952 : Nat := 4983230072969 + 3 ^ 40 * 2073952 * 2
def baseEnd_2073952 : Nat := 709956153569049924641383

theorem tailTrace_2073952 : CollatzResearch.WordTrace tailWord_2073952 prefixEnd_2073952 709956153569049924641383 := by
  unfold tailWord_2073952
  simp only [CollatzResearch.WordTrace]
  refine ⟨37821621891216790823592055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50428829188289054431456073 37821621891216790823592055)
  ·
    refine ⟨56732432836825186235388083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37821621891216790823592055 56732432836825186235388083)
    ·
      refine ⟨85098649255237779353082125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56732432836825186235388083 85098649255237779353082125)
      ·
        refine ⟨31911993470714167257405797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85098649255237779353082125 31911993470714167257405797)
        ·
          refine ⟨5983498775758906360763587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31911993470714167257405797 5983498775758906360763587)
          ·
            refine ⟨8975248163638359541145381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983498775758906360763587 8975248163638359541145381)
            ·
              refine ⟨1682859030682192413964759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8975248163638359541145381 1682859030682192413964759)
              ·
                refine ⟨2524288546023288620947139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682859030682192413964759 2524288546023288620947139)
                ·
                  refine ⟨3786432819034932931420709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524288546023288620947139 3786432819034932931420709)
                  ·
                    refine ⟨709956153569049924641383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786432819034932931420709 709956153569049924641383)
                    ·
                      rfl

theorem cell22_2073952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_2073952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2073952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2073952 prefixEnd_2073952 := by exact prefixLift 2073952
  have htrace : WordTrace (prefixWord ++ tailWord_2073952) baseStart_2073952 baseEnd_2073952 := by
    simpa [prefixWord, tailWord_2073952, baseEnd_2073952] using wordTrace_append hprefix tailTrace_2073952
  have hstable : (prefixWord ++ tailWord_2073952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073952).length < 2 ^ (prefixWord ++ tailWord_2073952).sum := by decide
  have hdescent : baseEnd_2073952 < baseStart_2073952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074012 : List Nat := [2, 2, 3, 4, 1, 2, 8]
def baseStart_2074012 : Nat := 118140960795 + 2074012 * 2 ^ 59
def prefixEnd_2074012 : Nat := 4983230072969 + 3 ^ 40 * 2074012 * 2
def baseEnd_2074012 : Nat := 26295433066489991412637

theorem tailTrace_2074012 : CollatzResearch.WordTrace tailWord_2074012 prefixEnd_2074012 26295433066489991412637 := by
  unfold tailWord_2074012
  simp only [CollatzResearch.WordTrace]
  refine ⟨37822716081108105947184145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50430288108144141262912193 37822716081108105947184145)
  ·
    refine ⟨28367037060831079460388109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37822716081108105947184145 28367037060831079460388109)
    ·
      refine ⟨10637638897811654797645541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28367037060831079460388109 10637638897811654797645541)
      ·
        refine ⟨1994557293339685274558539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10637638897811654797645541 1994557293339685274558539)
        ·
          refine ⟨2991835940009527911837809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994557293339685274558539 2991835940009527911837809)
          ·
            refine ⟨2243876955007145933878357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991835940009527911837809 2243876955007145933878357)
            ·
              refine ⟨26295433066489991412637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2243876955007145933878357 26295433066489991412637)
              ·
                rfl

theorem cell22_2074012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 8].length) (baseStart_2074012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074012 prefixEnd_2074012 := by exact prefixLift 2074012
  have htrace : WordTrace (prefixWord ++ tailWord_2074012) baseStart_2074012 baseEnd_2074012 := by
    simpa [prefixWord, tailWord_2074012, baseEnd_2074012] using wordTrace_append hprefix tailTrace_2074012
  have hstable : (prefixWord ++ tailWord_2074012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074012).length < 2 ^ (prefixWord ++ tailWord_2074012).sum := by decide
  have hdescent : baseEnd_2074012 < baseStart_2074012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074014 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2074014 : Nat := 118140960795 + 2074014 * 2 ^ 59
def prefixEnd_2074014 : Nat := 4983230072969 + 3 ^ 40 * 2074014 * 2
def baseEnd_2074014 : Nat := 709977377436102429591193

theorem tailTrace_2074014 : CollatzResearch.WordTrace tailWord_2074014 prefixEnd_2074014 709977377436102429591193 := by
  unfold tailWord_2074014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455688138526120779492637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50430336738805977490627397 9455688138526120779492637)
  ·
    refine ⟨3545883051947295292309739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9455688138526120779492637 3545883051947295292309739)
    ·
      refine ⟨5318824577920942938464609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545883051947295292309739 5318824577920942938464609)
      ·
        refine ⟨3989118433440707203848457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5318824577920942938464609 3989118433440707203848457)
        ·
          refine ⟨2991838825080530402886343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989118433440707203848457 2991838825080530402886343)
          ·
            refine ⟨4487758237620795604329515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991838825080530402886343 4487758237620795604329515)
            ·
              refine ⟨6731637356431193406494273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487758237620795604329515 6731637356431193406494273)
              ·
                refine ⟨5048728017323395054870705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731637356431193406494273 5048728017323395054870705)
                ·
                  refine ⟨3786546012992546291153029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048728017323395054870705 3786546012992546291153029)
                  ·
                    refine ⟨709977377436102429591193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786546012992546291153029 709977377436102429591193)
                    ·
                      rfl

theorem cell22_2074014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2074014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074014 prefixEnd_2074014 := by exact prefixLift 2074014
  have htrace : WordTrace (prefixWord ++ tailWord_2074014) baseStart_2074014 baseEnd_2074014 := by
    simpa [prefixWord, tailWord_2074014, baseEnd_2074014] using wordTrace_append hprefix tailTrace_2074014
  have hstable : (prefixWord ++ tailWord_2074014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074014).length < 2 ^ (prefixWord ++ tailWord_2074014).sum := by decide
  have hdescent : baseEnd_2074014 < baseStart_2074014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074102 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2074102 : Nat := 118140960795 + 2074102 * 2 ^ 59
def prefixEnd_2074102 : Nat := 4983230072969 + 3 ^ 40 * 2074102 * 2
def baseEnd_2074102 : Nat := 236669167211499844463641

theorem tailTrace_2074102 : CollatzResearch.WordTrace tailWord_2074102 prefixEnd_2074102 236669167211499844463641 := by
  unfold tailWord_2074102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728044670743134829071535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50432476487926771510096373 4728044670743134829071535)
  ·
    refine ⟨7092067006114702243607303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728044670743134829071535 7092067006114702243607303)
    ·
      refine ⟨10638100509172053365410955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092067006114702243607303 10638100509172053365410955)
      ·
        refine ⟨15957150763758080048116433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638100509172053365410955 15957150763758080048116433)
        ·
          refine ⟨11967863072818560036087325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15957150763758080048116433 11967863072818560036087325)
          ·
            refine ⟨4487948652306960013532747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11967863072818560036087325 4487948652306960013532747)
            ·
              refine ⟨6731922978460440020299121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487948652306960013532747 6731922978460440020299121)
              ·
                refine ⟨5048942233845330015224341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731922978460440020299121 5048942233845330015224341)
                ·
                  refine ⟨236669167211499844463641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5048942233845330015224341 236669167211499844463641)
                  ·
                    rfl

theorem cell22_2074102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2074102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074102 prefixEnd_2074102 := by exact prefixLift 2074102
  have htrace : WordTrace (prefixWord ++ tailWord_2074102) baseStart_2074102 baseEnd_2074102 := by
    simpa [prefixWord, tailWord_2074102, baseEnd_2074102] using wordTrace_append hprefix tailTrace_2074102
  have hstable : (prefixWord ++ tailWord_2074102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074102).length < 2 ^ (prefixWord ++ tailWord_2074102).sum := by decide
  have hdescent : baseEnd_2074102 < baseStart_2074102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074115 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_2074115 : Nat := 118140960795 + 2074115 * 2 ^ 59
def prefixEnd_2074115 : Nat := 4983230072969 + 3 ^ 40 * 2074115 * 2
def baseEnd_2074115 : Nat := 710011951800171832815883

theorem tailTrace_2074115 : CollatzResearch.WordTrace tailWord_2074115 prefixEnd_2074115 710011951800171832815883 := by
  unfold tailWord_2074115
  simp only [CollatzResearch.WordTrace]
  refine ⟨75649188880843060485367799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50432792587228706990245199 75649188880843060485367799)
  ·
    refine ⟨113473783321264590728051699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75649188880843060485367799 113473783321264590728051699)
    ·
      refine ⟨170210674981896886092077549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113473783321264590728051699 170210674981896886092077549)
      ·
        refine ⟨63829003118211332284529081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170210674981896886092077549 63829003118211332284529081)
        ·
          refine ⟨47871752338658499213396811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63829003118211332284529081 47871752338658499213396811)
          ·
            refine ⟨71807628507987748820095217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47871752338658499213396811 71807628507987748820095217)
            ·
              refine ⟨53855721380990811615071413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71807628507987748820095217 53855721380990811615071413)
              ·
                refine ⟨5048973879467888588912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53855721380990811615071413 5048973879467888588912945)
                ·
                  refine ⟨3786730409600916441684709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048973879467888588912945 3786730409600916441684709)
                  ·
                    refine ⟨710011951800171832815883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786730409600916441684709 710011951800171832815883)
                    ·
                      rfl

theorem cell22_2074115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_2074115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074115 prefixEnd_2074115 := by exact prefixLift 2074115
  have htrace : WordTrace (prefixWord ++ tailWord_2074115) baseStart_2074115 baseEnd_2074115 := by
    simpa [prefixWord, tailWord_2074115, baseEnd_2074115] using wordTrace_append hprefix tailTrace_2074115
  have hstable : (prefixWord ++ tailWord_2074115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074115).length < 2 ^ (prefixWord ++ tailWord_2074115).sum := by decide
  have hdescent : baseEnd_2074115 < baseStart_2074115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074119 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 4]
def baseStart_2074119 : Nat := 118140960795 + 2074119 * 2 ^ 59
def prefixEnd_2074119 : Nat := 4983230072969 + 3 ^ 40 * 2074119 * 2
def baseEnd_2074119 : Nat := 236671107027305718571957

theorem tailTrace_2074119 : CollatzResearch.WordTrace tailWord_2074119 prefixEnd_2074119 236671107027305718571957 := by
  unfold tailWord_2074119
  simp only [CollatzResearch.WordTrace]
  refine ⟨75649334772828569168513411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50432889848552379445675607 75649334772828569168513411)
  ·
    refine ⟨113474002159242853752770117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75649334772828569168513411 113474002159242853752770117)
    ·
      refine ⟨21276375404858035078644397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113474002159242853752770117 21276375404858035078644397)
      ·
        refine ⟨7978640776821763154491649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21276375404858035078644397 7978640776821763154491649)
        ·
          refine ⟨5983980582616322365868737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978640776821763154491649 5983980582616322365868737)
          ·
            refine ⟨4487985436962241774401553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983980582616322365868737 4487985436962241774401553)
            ·
              refine ⟨3365989077721681330801165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487985436962241774401553 3365989077721681330801165)
              ·
                refine ⟨1262245904145630499050437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3365989077721681330801165 1262245904145630499050437)
                ·
                  refine ⟨236671107027305718571957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1262245904145630499050437 236671107027305718571957)
                  ·
                    rfl

theorem cell22_2074119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 4].length) (baseStart_2074119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074119 prefixEnd_2074119 := by exact prefixLift 2074119
  have htrace : WordTrace (prefixWord ++ tailWord_2074119) baseStart_2074119 baseEnd_2074119 := by
    simpa [prefixWord, tailWord_2074119, baseEnd_2074119] using wordTrace_append hprefix tailTrace_2074119
  have hstable : (prefixWord ++ tailWord_2074119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074119).length < 2 ^ (prefixWord ++ tailWord_2074119).sum := by decide
  have hdescent : baseEnd_2074119 < baseStart_2074119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074175 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 7]
def baseStart_2074175 : Nat := 118140960795 + 2074175 * 2 ^ 59
def prefixEnd_2074175 : Nat := 4983230072969 + 3 ^ 40 * 2074175 * 2
def baseEnd_2074175 : Nat := 236677497008783892105233

theorem tailTrace_2074175 : CollatzResearch.WordTrace tailWord_2074175 prefixEnd_2074175 236677497008783892105233 := by
  unfold tailWord_2074175
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651377260625690732551979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50434251507083793821701319 75651377260625690732551979)
  ·
    refine ⟨113477065890938536098827969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75651377260625690732551979 113477065890938536098827969)
    ·
      refine ⟨85107799418203902074120977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113477065890938536098827969 85107799418203902074120977)
      ·
        refine ⟨63830849563652926555590733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85107799418203902074120977 63830849563652926555590733)
        ·
          refine ⟨23936568586369847458346525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63830849563652926555590733 23936568586369847458346525)
          ·
            refine ⟨8976213219888692796879947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23936568586369847458346525 8976213219888692796879947)
            ·
              refine ⟨13464319829833039195319921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976213219888692796879947 13464319829833039195319921)
              ·
                refine ⟨10098239872374779396489941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13464319829833039195319921 10098239872374779396489941)
                ·
                  refine ⟨236677497008783892105233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10098239872374779396489941 236677497008783892105233)
                  ·
                    rfl

theorem cell22_2074175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_2074175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074175 prefixEnd_2074175 := by exact prefixLift 2074175
  have htrace : WordTrace (prefixWord ++ tailWord_2074175) baseStart_2074175 baseEnd_2074175 := by
    simpa [prefixWord, tailWord_2074175, baseEnd_2074175] using wordTrace_append hprefix tailTrace_2074175
  have hstable : (prefixWord ++ tailWord_2074175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074175).length < 2 ^ (prefixWord ++ tailWord_2074175).sum := by decide
  have hdescent : baseEnd_2074175 < baseStart_2074175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074220 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_2074220 : Nat := 118140960795 + 2074220 * 2 ^ 59
def prefixEnd_2074220 : Nat := 4983230072969 + 3 ^ 40 * 2074220 * 2
def baseEnd_2074220 : Nat := 236682631815328852980187

theorem tailTrace_2074220 : CollatzResearch.WordTrace tailWord_2074220 prefixEnd_2074220 236682631815328852980187 := by
  unfold tailWord_2074220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826509272731331708970057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50435345696975108945293409 37826509272731331708970057)
  ·
    refine ⟨28369881954548498781727543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37826509272731331708970057 28369881954548498781727543)
    ·
      refine ⟨42554822931822748172591315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28369881954548498781727543 42554822931822748172591315)
      ·
        refine ⟨63832234397734122258886973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42554822931822748172591315 63832234397734122258886973)
        ·
          refine ⟨23937087899150295847082615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63832234397734122258886973 23937087899150295847082615)
          ·
            refine ⟨35905631848725443770623923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23937087899150295847082615 35905631848725443770623923)
            ·
              refine ⟨53858447773088165655935885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35905631848725443770623923 53858447773088165655935885)
              ·
                refine ⟨20196917914908062120975957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53858447773088165655935885 20196917914908062120975957)
                ·
                  refine ⟨236682631815328852980187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20196917914908062120975957 236682631815328852980187)
                  ·
                    rfl

theorem cell22_2074220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_2074220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074220 prefixEnd_2074220 := by exact prefixLift 2074220
  have htrace : WordTrace (prefixWord ++ tailWord_2074220) baseStart_2074220 baseEnd_2074220 := by
    simpa [prefixWord, tailWord_2074220, baseEnd_2074220] using wordTrace_append hprefix tailTrace_2074220
  have hstable : (prefixWord ++ tailWord_2074220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074220).length < 2 ^ (prefixWord ++ tailWord_2074220).sum := by decide
  have hdescent : baseEnd_2074220 < baseStart_2074220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074265 : List Nat := [1, 2, 1, 2, 1, 2, 2, 11]
def baseStart_2074265 : Nat := 118140960795 + 2074265 * 2 ^ 59
def prefixEnd_2074265 : Nat := 4983230072969 + 3 ^ 40 * 2074265 * 2
def baseEnd_2074265 : Nat := 78895922207291271285047

theorem tailTrace_2074265 : CollatzResearch.WordTrace tailWord_2074265 prefixEnd_2074265 78895922207291271285047 := by
  unfold tailWord_2074265
  simp only [CollatzResearch.WordTrace]
  refine ⟨75654659830299636103328249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50436439886866424068885499 75654659830299636103328249)
  ·
    refine ⟨56740994872724727077496187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75654659830299636103328249 56740994872724727077496187)
    ·
      refine ⟨85111492309087090616244281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56740994872724727077496187 85111492309087090616244281)
      ·
        refine ⟨63833619231815317962183211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85111492309087090616244281 63833619231815317962183211)
        ·
          refine ⟨95750428847722976943274817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63833619231815317962183211 95750428847722976943274817)
          ·
            refine ⟨71812821635792232707456113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95750428847722976943274817 71812821635792232707456113)
            ·
              refine ⟨53859616226844174530592085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71812821635792232707456113 53859616226844174530592085)
              ·
                refine ⟨78895922207291271285047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53859616226844174530592085 78895922207291271285047)
                ·
                  rfl

theorem cell22_2074265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 11].length) (baseStart_2074265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074265 prefixEnd_2074265 := by exact prefixLift 2074265
  have htrace : WordTrace (prefixWord ++ tailWord_2074265) baseStart_2074265 baseEnd_2074265 := by
    simpa [prefixWord, tailWord_2074265, baseEnd_2074265] using wordTrace_append hprefix tailTrace_2074265
  have hstable : (prefixWord ++ tailWord_2074265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074265).length < 2 ^ (prefixWord ++ tailWord_2074265).sum := by decide
  have hdescent : baseEnd_2074265 < baseStart_2074265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074333 : List Nat := [1, 4, 3, 3, 1, 2, 2, 6]
def baseStart_2074333 : Nat := 118140960795 + 2074333 * 2 ^ 59
def prefixEnd_2074333 : Nat := 4983230072969 + 3 ^ 40 * 2074333 * 2
def baseEnd_2074333 : Nat := 78898508628365770096135

theorem tailTrace_2074333 : CollatzResearch.WordTrace tailWord_2074333 prefixEnd_2074333 78898508628365770096135 := by
  unfold tailWord_2074333
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657139994053283716803653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50438093329368855811202435 75657139994053283716803653)
  ·
    refine ⟨14185713748884990696900685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75657139994053283716803653 14185713748884990696900685)
    ·
      refine ⟨5319642655831871511337757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14185713748884990696900685 5319642655831871511337757)
      ·
        refine ⟨1994865995936951816751659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5319642655831871511337757 1994865995936951816751659)
        ·
          refine ⟨2992298993905427725127489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994865995936951816751659 2992298993905427725127489)
          ·
            refine ⟨2244224245429070793845617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992298993905427725127489 2244224245429070793845617)
            ·
              refine ⟨1683168184071803095384213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244224245429070793845617 1683168184071803095384213)
              ·
                refine ⟨78898508628365770096135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1683168184071803095384213 78898508628365770096135)
                ·
                  rfl

theorem cell22_2074333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 6].length) (baseStart_2074333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074333 prefixEnd_2074333 := by exact prefixLift 2074333
  have htrace : WordTrace (prefixWord ++ tailWord_2074333) baseStart_2074333 baseEnd_2074333 := by
    simpa [prefixWord, tailWord_2074333, baseEnd_2074333] using wordTrace_append hprefix tailTrace_2074333
  have hstable : (prefixWord ++ tailWord_2074333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074333).length < 2 ^ (prefixWord ++ tailWord_2074333).sum := by decide
  have hdescent : baseEnd_2074333 < baseStart_2074333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074391 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 1, 4]
def baseStart_2074391 : Nat := 118140960795 + 2074391 * 2 ^ 59
def prefixEnd_2074391 : Nat := 4983230072969 + 3 ^ 40 * 2074391 * 2
def baseEnd_2074391 : Nat := 710106432240599112915037

theorem tailTrace_2074391 : CollatzResearch.WordTrace tailWord_2074391 prefixEnd_2074391 710106432240599112915037 := by
  unfold tailWord_2074391
  simp only [CollatzResearch.WordTrace]
  refine ⟨75659255427843159622415027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50439503618562106414943351 75659255427843159622415027)
  ·
    refine ⟨113488883141764739433622541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75659255427843159622415027 113488883141764739433622541)
    ·
      refine ⟨42558331178161777287608453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113488883141764739433622541 42558331178161777287608453)
      ·
        refine ⟨7979687095905333241426585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42558331178161777287608453 7979687095905333241426585)
        ·
          refine ⟨5984765321928999931069939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979687095905333241426585 5984765321928999931069939)
          ·
            refine ⟨8977147982893499896604909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984765321928999931069939 8977147982893499896604909)
            ·
              refine ⟨3366430493585062461226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8977147982893499896604909 3366430493585062461226841)
              ·
                refine ⟨2524822870188796845920131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366430493585062461226841 2524822870188796845920131)
                ·
                  refine ⟨3787234305283195268880197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524822870188796845920131 3787234305283195268880197)
                  ·
                    refine ⟨710106432240599112915037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787234305283195268880197 710106432240599112915037)
                    ·
                      rfl

theorem cell22_2074391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_2074391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074391 prefixEnd_2074391 := by exact prefixLift 2074391
  have htrace : WordTrace (prefixWord ++ tailWord_2074391) baseStart_2074391 baseEnd_2074391 := by
    simpa [prefixWord, tailWord_2074391, baseEnd_2074391] using wordTrace_append hprefix tailTrace_2074391
  have hstable : (prefixWord ++ tailWord_2074391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074391).length < 2 ^ (prefixWord ++ tailWord_2074391).sum := by decide
  have hdescent : baseEnd_2074391 < baseStart_2074391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074404 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2074404 : Nat := 118140960795 + 2074404 * 2 ^ 59
def prefixEnd_2074404 : Nat := 4983230072969 + 3 ^ 40 * 2074404 * 2
def baseEnd_2074404 : Nat := 710110882406271412339997

theorem tailTrace_2074404 : CollatzResearch.WordTrace tailWord_2074404 prefixEnd_2074404 710110882406271412339997 := by
  unfold tailWord_2074404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829864788398031421319133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50439819717864041895092177 37829864788398031421319133)
  ·
    refine ⟨14186199295649261782994675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37829864788398031421319133 14186199295649261782994675)
    ·
      refine ⟨21279298943473892674492013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186199295649261782994675 21279298943473892674492013)
      ·
        refine ⟨7979737103802709752934505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21279298943473892674492013 7979737103802709752934505)
        ·
          refine ⟨5984802827852032314700879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979737103802709752934505 5984802827852032314700879)
          ·
            refine ⟨8977204241778048472051319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984802827852032314700879 8977204241778048472051319)
            ·
              refine ⟨13465806362667072708076979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977204241778048472051319 13465806362667072708076979)
              ·
                refine ⟨20198709544000609062115469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465806362667072708076979 20198709544000609062115469)
                ·
                  refine ⟨7574516079000228398293301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20198709544000609062115469 7574516079000228398293301)
                  ·
                    refine ⟨710110882406271412339997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7574516079000228398293301 710110882406271412339997)
                    ·
                      rfl

theorem cell22_2074404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2074404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074404 prefixEnd_2074404 := by exact prefixLift 2074404
  have htrace : WordTrace (prefixWord ++ tailWord_2074404) baseStart_2074404 baseEnd_2074404 := by
    simpa [prefixWord, tailWord_2074404, baseEnd_2074404] using wordTrace_append hprefix tailTrace_2074404
  have hstable : (prefixWord ++ tailWord_2074404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074404).length < 2 ^ (prefixWord ++ tailWord_2074404).sum := by decide
  have hdescent : baseEnd_2074404 < baseStart_2074404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074408 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2074408 : Nat := 118140960795 + 2074408 * 2 ^ 59
def prefixEnd_2074408 : Nat := 4983230072969 + 3 ^ 40 * 2074408 * 2
def baseEnd_2074408 : Nat := 710112251688016735239985

theorem tailTrace_2074408 : CollatzResearch.WordTrace tailWord_2074408 prefixEnd_2074408 710112251688016735239985 := by
  unfold tailWord_2074408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829937734390785762891939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50439916979187714350522585 37829937734390785762891939)
  ·
    refine ⟨56744906601586178644337909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37829937734390785762891939 56744906601586178644337909)
    ·
      refine ⟨5319834993898704247906679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56744906601586178644337909 5319834993898704247906679)
      ·
        refine ⟨7979752490848056371860019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319834993898704247906679 7979752490848056371860019)
        ·
          refine ⟨11969628736272084557790029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979752490848056371860019 11969628736272084557790029)
          ·
            refine ⟨4488610776102031709171261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11969628736272084557790029 4488610776102031709171261)
            ·
              refine ⟨1683229041038261890939223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4488610776102031709171261 1683229041038261890939223)
              ·
                refine ⟨2524843561557392836408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683229041038261890939223 2524843561557392836408835)
                ·
                  refine ⟨3787265342336089254613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524843561557392836408835 3787265342336089254613253)
                  ·
                    refine ⟨710112251688016735239985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787265342336089254613253 710112251688016735239985)
                    ·
                      rfl

theorem cell22_2074408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2074408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074408 prefixEnd_2074408 := by exact prefixLift 2074408
  have htrace : WordTrace (prefixWord ++ tailWord_2074408) baseStart_2074408 baseEnd_2074408 := by
    simpa [prefixWord, tailWord_2074408, baseEnd_2074408] using wordTrace_append hprefix tailTrace_2074408
  have hstable : (prefixWord ++ tailWord_2074408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074408).length < 2 ^ (prefixWord ++ tailWord_2074408).sum := by decide
  have hdescent : baseEnd_2074408 < baseStart_2074408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074417 : List Nat := [1, 2, 2, 3, 2, 12]
def baseStart_2074417 : Nat := 118140960795 + 2074417 * 2 ^ 59
def prefixEnd_2074417 : Nat := 4983230072969 + 3 ^ 40 * 2074417 * 2
def baseEnd_2074417 : Nat := 8766855957678317429197

theorem tailTrace_2074417 : CollatzResearch.WordTrace tailWord_2074417 prefixEnd_2074417 8766855957678317429197 := by
  unfold tailWord_2074417
  simp only [CollatzResearch.WordTrace]
  refine ⟨75660203725748966062861505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50440135817165977375241003 75660203725748966062861505)
  ·
    refine ⟨56745152794311724547146129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75660203725748966062861505 56745152794311724547146129)
    ·
      refine ⟨42558864595733793410359597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56745152794311724547146129 42558864595733793410359597)
      ·
        refine ⟨15959574223400172528884849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42558864595733793410359597 15959574223400172528884849)
        ·
          refine ⟨11969680667550129396663637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15959574223400172528884849 11969680667550129396663637)
          ·
            refine ⟨8766855957678317429197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11969680667550129396663637 8766855957678317429197)
            ·
              rfl

theorem cell22_2074417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 12].length) (baseStart_2074417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074417 prefixEnd_2074417 := by exact prefixLift 2074417
  have htrace : WordTrace (prefixWord ++ tailWord_2074417) baseStart_2074417 baseEnd_2074417 := by
    simpa [prefixWord, tailWord_2074417, baseEnd_2074417] using wordTrace_append hprefix tailTrace_2074417
  have hstable : (prefixWord ++ tailWord_2074417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074417).length < 2 ^ (prefixWord ++ tailWord_2074417).sum := by decide
  have hdescent : baseEnd_2074417 < baseStart_2074417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_2074432 : Nat := 118140960795 + 2074432 * 2 ^ 59
def prefixEnd_2074432 : Nat := 4983230072969 + 3 ^ 40 * 2074432 * 2
def baseEnd_2074432 : Nat := 710120467378488672639911

theorem tailTrace_2074432 : CollatzResearch.WordTrace tailWord_2074432 prefixEnd_2074432 710120467378488672639911 := by
  unfold tailWord_2074432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830375410347311812328775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50440500547129749083105033 37830375410347311812328775)
  ·
    refine ⟨56745563115520967718493163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37830375410347311812328775 56745563115520967718493163)
    ·
      refine ⟨85118344673281451577739745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56745563115520967718493163 85118344673281451577739745)
      ·
        refine ⟨63838758504961088683304809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85118344673281451577739745 63838758504961088683304809)
        ·
          refine ⟨47879068878720816512478607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63838758504961088683304809 47879068878720816512478607)
          ·
            refine ⟨71818603318081224768717911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47879068878720816512478607 71818603318081224768717911)
            ·
              refine ⟨107727904977121837153076867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71818603318081224768717911 107727904977121837153076867)
              ·
                refine ⟨161591857465682755729615301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107727904977121837153076867 161591857465682755729615301)
                ·
                  refine ⟨30298473274815516699302869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161591857465682755729615301 30298473274815516699302869)
                  ·
                    refine ⟨710120467378488672639911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30298473274815516699302869 710120467378488672639911)
                    ·
                      rfl

theorem cell22_2074432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_2074432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074432 prefixEnd_2074432 := by exact prefixLift 2074432
  have htrace : WordTrace (prefixWord ++ tailWord_2074432) baseStart_2074432 baseEnd_2074432 := by
    simpa [prefixWord, tailWord_2074432, baseEnd_2074432] using wordTrace_append hprefix tailTrace_2074432
  have hstable : (prefixWord ++ tailWord_2074432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074432).length < 2 ^ (prefixWord ++ tailWord_2074432).sum := by decide
  have hdescent : baseEnd_2074432 < baseStart_2074432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074438 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2074438 : Nat := 118140960795 + 2074438 * 2 ^ 59
def prefixEnd_2074438 : Nat := 4983230072969 + 3 ^ 40 * 2074438 * 2
def baseEnd_2074438 : Nat := 710122521301106656989893

theorem tailTrace_2074438 : CollatzResearch.WordTrace tailWord_2074438 prefixEnd_2074438 710122521301106656989893 := by
  unfold tailWord_2074438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364405301833527707792999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50440646439115257766250645 2364405301833527707792999)
  ·
    refine ⟨3546607952750291561689499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364405301833527707792999 3546607952750291561689499)
    ·
      refine ⟨5319911929125437342534249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546607952750291561689499 5319911929125437342534249)
      ·
        refine ⟨3989933946844078006900687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319911929125437342534249 3989933946844078006900687)
        ·
          refine ⟨5984900920266117010351031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989933946844078006900687 5984900920266117010351031)
          ·
            refine ⟨8977351380399175515526547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984900920266117010351031 8977351380399175515526547)
            ·
              refine ⟨13466027070598763273289821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977351380399175515526547 13466027070598763273289821)
              ·
                refine ⟨5049760151474536227483683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13466027070598763273289821 5049760151474536227483683)
                ·
                  refine ⟨7574640227211804341225525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049760151474536227483683 7574640227211804341225525)
                  ·
                    refine ⟨710122521301106656989893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7574640227211804341225525 710122521301106656989893)
                    ·
                      rfl

theorem cell22_2074438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2074438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074438 prefixEnd_2074438 := by exact prefixLift 2074438
  have htrace : WordTrace (prefixWord ++ tailWord_2074438) baseStart_2074438 baseEnd_2074438 := by
    simpa [prefixWord, tailWord_2074438, baseEnd_2074438] using wordTrace_append hprefix tailTrace_2074438
  have hstable : (prefixWord ++ tailWord_2074438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074438).length < 2 ^ (prefixWord ++ tailWord_2074438).sum := by decide
  have hdescent : baseEnd_2074438 < baseStart_2074438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074496 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_2074496 : Nat := 118140960795 + 2074496 * 2 ^ 59
def prefixEnd_2074496 : Nat := 4983230072969 + 3 ^ 40 * 2074496 * 2
def baseEnd_2074496 : Nat := 236714125295471279679905

theorem tailTrace_2074496 : CollatzResearch.WordTrace tailWord_2074496 prefixEnd_2074496 236714125295471279679905 := by
  unfold tailWord_2074496
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831542546231381277493671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50442056728308508369991561 37831542546231381277493671)
  ·
    refine ⟨56747313819347071916240507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37831542546231381277493671 56747313819347071916240507)
    ·
      refine ⟨85120970729020607874360761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56747313819347071916240507 85120970729020607874360761)
      ·
        refine ⟨63840728046765455905770571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85120970729020607874360761 63840728046765455905770571)
        ·
          refine ⟨95761092070148183858655857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63840728046765455905770571 95761092070148183858655857)
          ·
            refine ⟨71820819052611137893991893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95761092070148183858655857 71820819052611137893991893)
            ·
              refine ⟨1683300446545573544390435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71820819052611137893991893 1683300446545573544390435)
              ·
                refine ⟨2524950669818360316585653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683300446545573544390435 2524950669818360316585653)
                ·
                  refine ⟨236714125295471279679905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2524950669818360316585653 236714125295471279679905)
                  ·
                    rfl

theorem cell22_2074496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_2074496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074496 prefixEnd_2074496 := by exact prefixLift 2074496
  have htrace : WordTrace (prefixWord ++ tailWord_2074496) baseStart_2074496 baseEnd_2074496 := by
    simpa [prefixWord, tailWord_2074496, baseEnd_2074496] using wordTrace_append hprefix tailTrace_2074496
  have hstable : (prefixWord ++ tailWord_2074496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074496).length < 2 ^ (prefixWord ++ tailWord_2074496).sum := by decide
  have hdescent : baseEnd_2074496 < baseStart_2074496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074554 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2074554 : Nat := 118140960795 + 2074554 * 2 ^ 59
def prefixEnd_2074554 : Nat := 4983230072969 + 3 ^ 40 * 2074554 * 2
def baseEnd_2074554 : Nat := 710162230471721021089537

theorem tailTrace_2074554 : CollatzResearch.WordTrace tailWord_2074554 prefixEnd_2074554 710162230471721021089537 := by
  unfold tailWord_2074554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916300131563159615149679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50443467017501758973732477 18916300131563159615149679)
  ·
    refine ⟨28374450197344739422724519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18916300131563159615149679 28374450197344739422724519)
    ·
      refine ⟨42561675296017109134086779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28374450197344739422724519 42561675296017109134086779)
      ·
        refine ⟨63842512944025663701130169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42561675296017109134086779 63842512944025663701130169)
        ·
          refine ⟨47881884708019247775847627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63842512944025663701130169 47881884708019247775847627)
          ·
            refine ⟨71822827062028871663771441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47881884708019247775847627 71822827062028871663771441)
            ·
              refine ⟨53867120296521653747828581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71822827062028871663771441 53867120296521653747828581)
              ·
                refine ⟨10100085055597810077717859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53867120296521653747828581 10100085055597810077717859)
                ·
                  refine ⟨15150127583396715116576789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100085055597810077717859 15150127583396715116576789)
                  ·
                    refine ⟨710162230471721021089537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15150127583396715116576789 710162230471721021089537)
                    ·
                      rfl

theorem cell22_2074554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2074554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074554 prefixEnd_2074554 := by exact prefixLift 2074554
  have htrace : WordTrace (prefixWord ++ tailWord_2074554) baseStart_2074554 baseEnd_2074554 := by
    simpa [prefixWord, tailWord_2074554, baseEnd_2074554] using wordTrace_append hprefix tailTrace_2074554
  have hstable : (prefixWord ++ tailWord_2074554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074554).length < 2 ^ (prefixWord ++ tailWord_2074554).sum := by decide
  have hdescent : baseEnd_2074554 < baseStart_2074554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074571 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_2074571 : Nat := 118140960795 + 2074571 * 2 ^ 59
def prefixEnd_2074571 : Nat := 4983230072969 + 3 ^ 40 * 2074571 * 2
def baseEnd_2074571 : Nat := 710168049919138643414485

theorem tailTrace_2074571 : CollatzResearch.WordTrace tailWord_2074571 prefixEnd_2074571 710168049919138643414485 := by
  unfold tailWord_2074571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75665820567191050363967567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50443880378127366909311711 75665820567191050363967567)
  ·
    refine ⟨113498730850786575545951351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75665820567191050363967567 113498730850786575545951351)
    ·
      refine ⟨170248096276179863318927027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113498730850786575545951351 170248096276179863318927027)
      ·
        refine ⟨255372144414269794978390541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170248096276179863318927027 255372144414269794978390541)
        ·
          refine ⟨95764554155351173116896453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255372144414269794978390541 95764554155351173116896453)
          ·
            refine ⟨17955853904128344959418085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95764554155351173116896453 17955853904128344959418085)
            ·
              refine ⟨3366722607024064679890891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17955853904128344959418085 3366722607024064679890891)
              ·
                refine ⟨5050083910536097019836337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366722607024064679890891 5050083910536097019836337)
                ·
                  refine ⟨3787562932902072764877253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5050083910536097019836337 3787562932902072764877253)
                  ·
                    refine ⟨710168049919138643414485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787562932902072764877253 710168049919138643414485)
                    ·
                      rfl

theorem cell22_2074571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_2074571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074571 prefixEnd_2074571 := by exact prefixLift 2074571
  have htrace : WordTrace (prefixWord ++ tailWord_2074571) baseStart_2074571 baseEnd_2074571 := by
    simpa [prefixWord, tailWord_2074571, baseEnd_2074571] using wordTrace_append hprefix tailTrace_2074571
  have hstable : (prefixWord ++ tailWord_2074571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074571).length < 2 ^ (prefixWord ++ tailWord_2074571).sum := by decide
  have hdescent : baseEnd_2074571 < baseStart_2074571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074586 : List Nat := [3, 1, 1, 2, 6, 9]
def baseStart_2074586 : Nat := 118140960795 + 2074586 * 2 ^ 59
def prefixEnd_2074586 : Nat := 4983230072969 + 3 ^ 40 * 2074586 * 2
def baseEnd_2074586 : Nat := 8767570181798563015919

theorem tailTrace_2074586 : CollatzResearch.WordTrace tailWord_2074586 prefixEnd_2074586 8767570181798563015919 := by
  unfold tailWord_2074586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916591915534176981440903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50444245108091138617175741 18916591915534176981440903)
  ·
    refine ⟨28374887873301265472161355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18916591915534176981440903 28374887873301265472161355)
    ·
      refine ⟨42562331809951898208242033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28374887873301265472161355 42562331809951898208242033)
      ·
        refine ⟨31921748857463923656181525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42562331809951898208242033 31921748857463923656181525)
        ·
          refine ⟨1496331977693621421383509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31921748857463923656181525 1496331977693621421383509)
          ·
            refine ⟨8767570181798563015919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1496331977693621421383509 8767570181798563015919)
            ·
              rfl

theorem cell22_2074586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 9].length) (baseStart_2074586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074586 prefixEnd_2074586 := by exact prefixLift 2074586
  have htrace : WordTrace (prefixWord ++ tailWord_2074586) baseStart_2074586 baseEnd_2074586 := by
    simpa [prefixWord, tailWord_2074586, baseEnd_2074586] using wordTrace_append hprefix tailTrace_2074586
  have hstable : (prefixWord ++ tailWord_2074586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074586).length < 2 ^ (prefixWord ++ tailWord_2074586).sum := by decide
  have hdescent : baseEnd_2074586 < baseStart_2074586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074635 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 1, 3]
def baseStart_2074635 : Nat := 118140960795 + 2074635 * 2 ^ 59
def prefixEnd_2074635 : Nat := 4983230072969 + 3 ^ 40 * 2074635 * 2
def baseEnd_2074635 : Nat := 710189958427063809814289

theorem tailTrace_2074635 : CollatzResearch.WordTrace tailWord_2074635 prefixEnd_2074635 710189958427063809814289 := by
  unfold tailWord_2074635
  simp only [CollatzResearch.WordTrace]
  refine ⟨75668154838959189294297359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50445436559306126196198239 75668154838959189294297359)
  ·
    refine ⟨113502232258438783941446039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75668154838959189294297359 113502232258438783941446039)
    ·
      refine ⟨170253348387658175912169059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113502232258438783941446039 170253348387658175912169059)
      ·
        refine ⟨255380022581487263868253589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170253348387658175912169059 255380022581487263868253589)
        ·
          refine ⟨11970938558507215493824387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255380022581487263868253589 11970938558507215493824387)
          ·
            refine ⟨17956407837760823240736581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970938558507215493824387 17956407837760823240736581)
            ·
              refine ⟨3366826469580154357638109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17956407837760823240736581 3366826469580154357638109)
              ·
                refine ⟨1262559926092557884114291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3366826469580154357638109 1262559926092557884114291)
                ·
                  refine ⟨1893839889138836826171437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262559926092557884114291 1893839889138836826171437)
                  ·
                    refine ⟨710189958427063809814289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893839889138836826171437 710189958427063809814289)
                    ·
                      rfl

theorem cell22_2074635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 3].length) (baseStart_2074635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074635 prefixEnd_2074635 := by exact prefixLift 2074635
  have htrace : WordTrace (prefixWord ++ tailWord_2074635) baseStart_2074635 baseEnd_2074635 := by
    simpa [prefixWord, tailWord_2074635, baseEnd_2074635] using wordTrace_append hprefix tailTrace_2074635
  have hstable : (prefixWord ++ tailWord_2074635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074635).length < 2 ^ (prefixWord ++ tailWord_2074635).sum := by decide
  have hdescent : baseEnd_2074635 < baseStart_2074635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074686 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2074686 : Nat := 118140960795 + 2074686 * 2 ^ 59
def prefixEnd_2074686 : Nat := 4983230072969 + 3 ^ 40 * 2074686 * 2
def baseEnd_2074686 : Nat := 710207416769316676789133

theorem tailTrace_2074686 : CollatzResearch.WordTrace tailWord_2074686 prefixEnd_2074686 710207416769316676789133 := by
  unfold tailWord_2074686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458751870221803125550489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50446676641182950002935941 9458751870221803125550489)
  ·
    refine ⟨7094063902666352344162867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9458751870221803125550489 7094063902666352344162867)
    ·
      refine ⟨10641095853999528516244301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094063902666352344162867 10641095853999528516244301)
      ·
        refine ⟨3990410945249823193591613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10641095853999528516244301 3990410945249823193591613)
        ·
          refine ⟨1496404104468683697596855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3990410945249823193591613 1496404104468683697596855)
          ·
            refine ⟨2244606156703025546395283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496404104468683697596855 2244606156703025546395283)
            ·
              refine ⟨3366909235054538319592925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244606156703025546395283 3366909235054538319592925)
              ·
                refine ⟨1262590963145451869847347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3366909235054538319592925 1262590963145451869847347)
                ·
                  refine ⟨1893886444718177804771021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262590963145451869847347 1893886444718177804771021)
                  ·
                    refine ⟨710207416769316676789133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893886444718177804771021 710207416769316676789133)
                    ·
                      rfl

theorem cell22_2074686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2074686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074686 prefixEnd_2074686 := by exact prefixLift 2074686
  have htrace : WordTrace (prefixWord ++ tailWord_2074686) baseStart_2074686 baseEnd_2074686 := by
    simpa [prefixWord, tailWord_2074686, baseEnd_2074686] using wordTrace_append hprefix tailTrace_2074686
  have hstable : (prefixWord ++ tailWord_2074686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074686).length < 2 ^ (prefixWord ++ tailWord_2074686).sum := by decide
  have hdescent : baseEnd_2074686 < baseStart_2074686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074725 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_2074725 : Nat := 118140960795 + 2074725 * 2 ^ 59
def prefixEnd_2074725 : Nat := 4983230072969 + 3 ^ 40 * 2074725 * 2
def baseEnd_2074725 : Nat := 710220767266333575064013

theorem tailTrace_2074725 : CollatzResearch.WordTrace tailWord_2074725 prefixEnd_2074725 710220767266333575064013 := by
  unfold tailWord_2074725
  simp only [CollatzResearch.WordTrace]
  refine ⟨75671437408633134665073629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50447624939088756443382419 75671437408633134665073629)
  ·
    refine ⟨28376789028237425499402611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75671437408633134665073629 28376789028237425499402611)
    ·
      refine ⟨42565183542356138249103917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28376789028237425499402611 42565183542356138249103917)
      ·
        refine ⟨15961943828383551843413969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42565183542356138249103917 15961943828383551843413969)
        ·
          refine ⟨11971457871287663882560477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15961943828383551843413969 11971457871287663882560477)
          ·
            refine ⟨4489296701732873955960179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11971457871287663882560477 4489296701732873955960179)
            ·
              refine ⟨6733945052599310933940269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489296701732873955960179 6733945052599310933940269)
              ·
                refine ⟨2525229394724741600227601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733945052599310933940269 2525229394724741600227601)
                ·
                  refine ⟨1893922046043556200170701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2525229394724741600227601 1893922046043556200170701)
                  ·
                    refine ⟨710220767266333575064013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893922046043556200170701 710220767266333575064013)
                    ·
                      rfl

theorem cell22_2074725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_2074725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074725 prefixEnd_2074725 := by exact prefixLift 2074725
  have htrace : WordTrace (prefixWord ++ tailWord_2074725) baseStart_2074725 baseEnd_2074725 := by
    simpa [prefixWord, tailWord_2074725, baseEnd_2074725] using wordTrace_append hprefix tailTrace_2074725
  have hstable : (prefixWord ++ tailWord_2074725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074725).length < 2 ^ (prefixWord ++ tailWord_2074725).sum := by decide
  have hdescent : baseEnd_2074725 < baseStart_2074725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074770 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2074770 : Nat := 118140960795 + 2074770 * 2 ^ 59
def prefixEnd_2074770 : Nat := 4983230072969 + 3 ^ 40 * 2074770 * 2
def baseEnd_2074770 : Nat := 710236171685968457688875

theorem tailTrace_2074770 : CollatzResearch.WordTrace tailWord_2074770 prefixEnd_2074770 710236171685968457688875 := by
  unfold tailWord_2074770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918269673367526837615441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50448719128980071566974509 18918269673367526837615441)
  ·
    refine ⟨14188702255025645128211581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18918269673367526837615441 14188702255025645128211581)
    ·
      refine ⟨5320763345634616923079343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14188702255025645128211581 5320763345634616923079343)
      ·
        refine ⟨7981145018451925384619015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320763345634616923079343 7981145018451925384619015)
        ·
          refine ⟨11971717527677888076928523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981145018451925384619015 11971717527677888076928523)
          ·
            refine ⟨17957576291516832115392785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11971717527677888076928523 17957576291516832115392785)
            ·
              refine ⟨13468182218637624086544589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17957576291516832115392785 13468182218637624086544589)
              ·
                refine ⟨5050568331989109032454221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13468182218637624086544589 5050568331989109032454221)
                ·
                  refine ⟨1893963124495915887170333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5050568331989109032454221 1893963124495915887170333)
                  ·
                    refine ⟨710236171685968457688875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1893963124495915887170333 710236171685968457688875)
                    ·
                      rfl

theorem cell22_2074770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2074770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074770 prefixEnd_2074770 := by exact prefixLift 2074770
  have htrace : WordTrace (prefixWord ++ tailWord_2074770) baseStart_2074770 baseEnd_2074770 := by
    simpa [prefixWord, tailWord_2074770, baseEnd_2074770] using wordTrace_append hprefix tailTrace_2074770
  have hstable : (prefixWord ++ tailWord_2074770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074770).length < 2 ^ (prefixWord ++ tailWord_2074770).sum := by decide
  have hdescent : baseEnd_2074770 < baseStart_2074770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074772 : List Nat := [2, 4, 2, 3, 1, 2, 1, 7]
def baseStart_2074772 : Nat := 118140960795 + 2074772 * 2 ^ 59
def prefixEnd_2074772 : Nat := 4983230072969 + 3 ^ 40 * 2074772 * 2
def baseEnd_2074772 : Nat := 78915206258537902126541

theorem tailTrace_2074772 : CollatzResearch.WordTrace tailWord_2074772 prefixEnd_2074772 78915206258537902126541 := by
  unfold tailWord_2074772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37836575819731430846017285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50448767759641907794689713 37836575819731430846017285)
  ·
    refine ⟨7094357966199643283628241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37836575819731430846017285 7094357966199643283628241)
    ·
      refine ⟨5320768474649732462721181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7094357966199643283628241 5320768474649732462721181)
      ·
        refine ⟨1995288177993649673520443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5320768474649732462721181 1995288177993649673520443)
        ·
          refine ⟨2992932266990474510280665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995288177993649673520443 2992932266990474510280665)
          ·
            refine ⟨2244699200242855882710499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992932266990474510280665 2244699200242855882710499)
            ·
              refine ⟨3367048800364283824065749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244699200242855882710499 3367048800364283824065749)
              ·
                refine ⟨78915206258537902126541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3367048800364283824065749 78915206258537902126541)
                ·
                  rfl

theorem cell22_2074772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_2074772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074772 prefixEnd_2074772 := by exact prefixLift 2074772
  have htrace : WordTrace (prefixWord ++ tailWord_2074772) baseStart_2074772 baseEnd_2074772 := by
    simpa [prefixWord, tailWord_2074772, baseEnd_2074772] using wordTrace_append hprefix tailTrace_2074772
  have hstable : (prefixWord ++ tailWord_2074772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074772).length < 2 ^ (prefixWord ++ tailWord_2074772).sum := by decide
  have hdescent : baseEnd_2074772 < baseStart_2074772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074811 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 8]
def baseStart_2074811 : Nat := 118140960795 + 2074811 * 2 ^ 59
def prefixEnd_2074811 : Nat := 4983230072969 + 3 ^ 40 * 2074811 * 2
def baseEnd_2074811 : Nat := 236750068941286005804583

theorem tailTrace_2074811 : CollatzResearch.WordTrace tailWord_2074811 prefixEnd_2074811 236750068941286005804583 := by
  unfold tailWord_2074811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75674574086321571352704287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50449716057547714235136191 75674574086321571352704287)
  ·
    refine ⟨113511861129482357029056431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75674574086321571352704287 113511861129482357029056431)
    ·
      refine ⟨170267791694223535543584647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113511861129482357029056431 170267791694223535543584647)
      ·
        refine ⟨255401687541335303315376971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170267791694223535543584647 255401687541335303315376971)
        ·
          refine ⟨383102531312002954973065457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255401687541335303315376971 383102531312002954973065457)
          ·
            refine ⟨287326898484002216229799093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383102531312002954973065457 287326898484002216229799093)
            ·
              refine ⟨26936896732875207771543665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287326898484002216229799093 26936896732875207771543665)
              ·
                refine ⟨20202672549656405828657749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26936896732875207771543665 20202672549656405828657749)
                ·
                  refine ⟨236750068941286005804583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20202672549656405828657749 236750068941286005804583)
                  ·
                    rfl

theorem cell22_2074811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_2074811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074811 prefixEnd_2074811 := by exact prefixLift 2074811
  have htrace : WordTrace (prefixWord ++ tailWord_2074811) baseStart_2074811 baseEnd_2074811 := by
    simpa [prefixWord, tailWord_2074811, baseEnd_2074811] using wordTrace_append hprefix tailTrace_2074811
  have hstable : (prefixWord ++ tailWord_2074811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074811).length < 2 ^ (prefixWord ++ tailWord_2074811).sum := by decide
  have hdescent : baseEnd_2074811 < baseStart_2074811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 6, 3]
def baseStart_2074843 : Nat := 118140960795 + 2074843 * 2 ^ 59
def prefixEnd_2074843 : Nat := 4983230072969 + 3 ^ 40 * 2074843 * 2
def baseEnd_2074843 : Nat := 710261161077820600613651

theorem tailTrace_2074843 : CollatzResearch.WordTrace tailWord_2074843 prefixEnd_2074843 710261161077820600613651 := by
  unfold tailWord_2074843
  simp only [CollatzResearch.WordTrace]
  refine ⟨75675741222205640817869183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50450494148137093878579455 75675741222205640817869183)
  ·
    refine ⟨113513611833308461226803775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75675741222205640817869183 113513611833308461226803775)
    ·
      refine ⟨170270417749962691840205663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113513611833308461226803775 170270417749962691840205663)
      ·
        refine ⟨255405626624944037760308495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170270417749962691840205663 255405626624944037760308495)
        ·
          refine ⟨383108439937416056640462743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255405626624944037760308495 383108439937416056640462743)
          ·
            refine ⟨574662659906124084960694115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383108439937416056640462743 574662659906124084960694115)
            ·
              refine ⟨861993989859186127441041173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574662659906124084960694115 861993989859186127441041173)
              ·
                refine ⟨40405968274649349723798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 861993989859186127441041173 40405968274649349723798805)
                ·
                  refine ⟨1894029762874188268303069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40405968274649349723798805 1894029762874188268303069)
                  ·
                    refine ⟨710261161077820600613651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894029762874188268303069 710261161077820600613651)
                    ·
                      rfl

theorem cell22_2074843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].length) (baseStart_2074843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074843 prefixEnd_2074843 := by exact prefixLift 2074843
  have htrace : WordTrace (prefixWord ++ tailWord_2074843) baseStart_2074843 baseEnd_2074843 := by
    simpa [prefixWord, tailWord_2074843, baseEnd_2074843] using wordTrace_append hprefix tailTrace_2074843
  have hstable : (prefixWord ++ tailWord_2074843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074843).length < 2 ^ (prefixWord ++ tailWord_2074843).sum := by decide
  have hdescent : baseEnd_2074843 < baseStart_2074843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074845 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2074845 : Nat := 118140960795 + 2074845 * 2 ^ 59
def prefixEnd_2074845 : Nat := 4983230072969 + 3 ^ 40 * 2074845 * 2
def baseEnd_2074845 : Nat := 236753948572897754021215

theorem tailTrace_2074845 : CollatzResearch.WordTrace tailWord_2074845 prefixEnd_2074845 236753948572897754021215 := by
  unfold tailWord_2074845
  simp only [CollatzResearch.WordTrace]
  refine ⟨75675814168198395159441989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50450542778798930106294659 75675814168198395159441989)
  ·
    refine ⟨14189215156537199092395373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75675814168198395159441989 14189215156537199092395373)
    ·
      refine ⟨5320955683701449659648265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14189215156537199092395373 5320955683701449659648265)
      ·
        refine ⟨3990716762776087244736199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5320955683701449659648265 3990716762776087244736199)
        ·
          refine ⟨5986075144164130867104299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990716762776087244736199 5986075144164130867104299)
          ·
            refine ⟨8979112716246196300656449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986075144164130867104299 8979112716246196300656449)
            ·
              refine ⟨6734334537184647225492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979112716246196300656449 6734334537184647225492337)
              ·
                refine ⟨5050750902888485419119253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734334537184647225492337 5050750902888485419119253)
                ·
                  refine ⟨236753948572897754021215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5050750902888485419119253 236753948572897754021215)
                  ·
                    rfl

theorem cell22_2074845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2074845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074845 prefixEnd_2074845 := by exact prefixLift 2074845
  have htrace : WordTrace (prefixWord ++ tailWord_2074845) baseStart_2074845 baseEnd_2074845 := by
    simpa [prefixWord, tailWord_2074845, baseEnd_2074845] using wordTrace_append hprefix tailTrace_2074845
  have hstable : (prefixWord ++ tailWord_2074845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074845).length < 2 ^ (prefixWord ++ tailWord_2074845).sum := by decide
  have hdescent : baseEnd_2074845 < baseStart_2074845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074858 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2074858 : Nat := 118140960795 + 2074858 * 2 ^ 59
def prefixEnd_2074858 : Nat := 4983230072969 + 3 ^ 40 * 2074858 * 2
def baseEnd_2074858 : Nat := 710266295884365561488605

theorem tailTrace_2074858 : CollatzResearch.WordTrace tailWord_2074858 prefixEnd_2074858 710266295884365561488605 := by
  unfold tailWord_2074858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18919072079287824594916307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50450858878100865586443485 18919072079287824594916307)
  ·
    refine ⟨28378608118931736892374461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18919072079287824594916307 28378608118931736892374461)
    ·
      refine ⟨10641978044599401334640423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28378608118931736892374461 10641978044599401334640423)
      ·
        refine ⟨15962967066899102001960635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641978044599401334640423 15962967066899102001960635)
        ·
          refine ⟨23944450600348653002940953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962967066899102001960635 23944450600348653002940953)
          ·
            refine ⟨17958337950261489752205715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23944450600348653002940953 17958337950261489752205715)
            ·
              refine ⟨26937506925392234628308573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17958337950261489752205715 26937506925392234628308573)
              ·
                refine ⟨10101565097022087985615715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26937506925392234628308573 10101565097022087985615715)
                ·
                  refine ⟨15152347645533131978423573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101565097022087985615715 15152347645533131978423573)
                  ·
                    refine ⟨710266295884365561488605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15152347645533131978423573 710266295884365561488605)
                    ·
                      rfl

theorem cell22_2074858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2074858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074858 prefixEnd_2074858 := by exact prefixLift 2074858
  have htrace : WordTrace (prefixWord ++ tailWord_2074858) baseStart_2074858 baseEnd_2074858 := by
    simpa [prefixWord, tailWord_2074858, baseEnd_2074858] using wordTrace_append hprefix tailTrace_2074858
  have hstable : (prefixWord ++ tailWord_2074858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074858).length < 2 ^ (prefixWord ++ tailWord_2074858).sum := by decide
  have hdescent : baseEnd_2074858 < baseStart_2074858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074995 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 4, 3]
def baseStart_2074995 : Nat := 118140960795 + 2074995 * 2 ^ 59
def prefixEnd_2074995 : Nat := 4983230072969 + 3 ^ 40 * 2074995 * 2
def baseEnd_2074995 : Nat := 710313193784142870813185

theorem tailTrace_2074995 : CollatzResearch.WordTrace tailWord_2074995 prefixEnd_2074995 710313193784142870813185 := by
  unfold tailWord_2074995
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681285117654970777402439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50454190078436647184934959 75681285117654970777402439)
  ·
    refine ⟨113521927676482456166103659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75681285117654970777402439 113521927676482456166103659)
    ·
      refine ⟨170282891514723684249155489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113521927676482456166103659 170282891514723684249155489)
      ·
        refine ⟨127712168636042763186866617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170282891514723684249155489 127712168636042763186866617)
        ·
          refine ⟨95784126477032072390149963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127712168636042763186866617 95784126477032072390149963)
          ·
            refine ⟨143676189715548108585224945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95784126477032072390149963 143676189715548108585224945)
            ·
              refine ⟨107757142286661081438918709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143676189715548108585224945 107757142286661081438918709)
              ·
                refine ⟨10102232089374476384898629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107757142286661081438918709 10102232089374476384898629)
                ·
                  refine ⟨1894168516757714322168493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10102232089374476384898629 1894168516757714322168493)
                  ·
                    refine ⟨710313193784142870813185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894168516757714322168493 710313193784142870813185)
                    ·
                      rfl

theorem cell22_2074995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].length) (baseStart_2074995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074995 prefixEnd_2074995 := by exact prefixLift 2074995
  have htrace : WordTrace (prefixWord ++ tailWord_2074995) baseStart_2074995 baseEnd_2074995 := by
    simpa [prefixWord, tailWord_2074995, baseEnd_2074995] using wordTrace_append hprefix tailTrace_2074995
  have hstable : (prefixWord ++ tailWord_2074995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074995).length < 2 ^ (prefixWord ++ tailWord_2074995).sum := by decide
  have hdescent : baseEnd_2074995 < baseStart_2074995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074997 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 6]
def baseStart_2074997 : Nat := 118140960795 + 2074997 * 2 ^ 59
def prefixEnd_2074997 : Nat := 4983230072969 + 3 ^ 40 * 2074997 * 2
def baseEnd_2074997 : Nat := 236771292808338510754393

theorem tailTrace_2074997 : CollatzResearch.WordTrace tailWord_2074997 prefixEnd_2074997 236771292808338510754393 := by
  unfold tailWord_2074997
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681358063647725118975245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50454238709098483412650163 75681358063647725118975245)
  ·
    refine ⟨28380509273867896919615717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75681358063647725118975245 28380509273867896919615717)
    ·
      refine ⟨5321345488850230672427947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28380509273867896919615717 5321345488850230672427947)
      ·
        refine ⟨7982018233275346008641921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321345488850230672427947 7982018233275346008641921)
        ·
          refine ⟨5986513674956509506481441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7982018233275346008641921 5986513674956509506481441)
          ·
            refine ⟨4489885256217382129861081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986513674956509506481441 4489885256217382129861081)
            ·
              refine ⟨3367413942163036597395811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489885256217382129861081 3367413942163036597395811)
              ·
                refine ⟨5051120913244554896093717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367413942163036597395811 5051120913244554896093717)
                ·
                  refine ⟨236771292808338510754393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5051120913244554896093717 236771292808338510754393)
                  ·
                    rfl

theorem cell22_2074997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_2074997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2074997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2074997 prefixEnd_2074997 := by exact prefixLift 2074997
  have htrace : WordTrace (prefixWord ++ tailWord_2074997) baseStart_2074997 baseEnd_2074997 := by
    simpa [prefixWord, tailWord_2074997, baseEnd_2074997] using wordTrace_append hprefix tailTrace_2074997
  have hstable : (prefixWord ++ tailWord_2074997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074997).length < 2 ^ (prefixWord ++ tailWord_2074997).sum := by decide
  have hdescent : baseEnd_2074997 < baseStart_2074997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075115 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 6]
def baseStart_2075115 : Nat := 118140960795 + 2075115 * 2 ^ 59
def prefixEnd_2075115 : Nat := 4983230072969 + 3 ^ 40 * 2075115 * 2
def baseEnd_2075115 : Nat := 236784757412167519270939

theorem tailTrace_2075115 : CollatzResearch.WordTrace tailWord_2075115 prefixEnd_2075115 236784757412167519270939 := by
  unfold tailWord_2075115
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685661877220231271770799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457107918146820847847199 75685661877220231271770799)
  ·
    refine ⟨113528492815830346907656199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75685661877220231271770799 113528492815830346907656199)
    ·
      refine ⟨170292739223745520361484299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113528492815830346907656199 170292739223745520361484299)
      ·
        refine ⟨255439108835618280542226449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170292739223745520361484299 255439108835618280542226449)
        ·
          refine ⟨191579331626713710406669837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255439108835618280542226449 191579331626713710406669837)
          ·
            refine ⟨71842249360017641402501189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191579331626713710406669837 71842249360017641402501189)
            ·
              refine ⟨13470421755003307762968973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71842249360017641402501189 13470421755003307762968973)
              ·
                refine ⟨5051408158126240411113365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13470421755003307762968973 5051408158126240411113365)
                ·
                  refine ⟨236784757412167519270939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5051408158126240411113365 236784757412167519270939)
                  ·
                    rfl

theorem cell22_2075115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_2075115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075115 prefixEnd_2075115 := by exact prefixLift 2075115
  have htrace : WordTrace (prefixWord ++ tailWord_2075115) baseStart_2075115 baseEnd_2075115 := by
    simpa [prefixWord, tailWord_2075115, baseEnd_2075115] using wordTrace_append hprefix tailTrace_2075115
  have hstable : (prefixWord ++ tailWord_2075115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075115).length < 2 ^ (prefixWord ++ tailWord_2075115).sum := by decide
  have hdescent : baseEnd_2075115 < baseStart_2075115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075142 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2075142 : Nat := 118140960795 + 2075142 * 2 ^ 59
def prefixEnd_2075142 : Nat := 4983230072969 + 3 ^ 40 * 2075142 * 2
def baseEnd_2075142 : Nat := 710363514888283487387735

theorem tailTrace_2075142 : CollatzResearch.WordTrace tailWord_2075142 prefixEnd_2075142 710363514888283487387735 := by
  unfold tailWord_2075142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365207707753825465093865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50457764432081609922002453 2365207707753825465093865)
  ·
    refine ⟨1773905780815369098820399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2365207707753825465093865 1773905780815369098820399)
    ·
      refine ⟨2660858671223053648230599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773905780815369098820399 2660858671223053648230599)
      ·
        refine ⟨3991288006834580472345899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660858671223053648230599 3991288006834580472345899)
        ·
          refine ⟨5986932010251870708518849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991288006834580472345899 5986932010251870708518849)
          ·
            refine ⟨4490199007688903031389137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986932010251870708518849 4490199007688903031389137)
            ·
              refine ⟨3367649255766677273541853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490199007688903031389137 3367649255766677273541853)
              ·
                refine ⟨1262868470912503977578195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3367649255766677273541853 1262868470912503977578195)
                ·
                  refine ⟨1894302706368755966367293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262868470912503977578195 1894302706368755966367293)
                  ·
                    refine ⟨710363514888283487387735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894302706368755966367293 710363514888283487387735)
                    ·
                      rfl

theorem cell22_2075142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2075142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075142 prefixEnd_2075142 := by exact prefixLift 2075142
  have htrace : WordTrace (prefixWord ++ tailWord_2075142) baseStart_2075142 baseEnd_2075142 := by
    simpa [prefixWord, tailWord_2075142, baseEnd_2075142] using wordTrace_append hprefix tailTrace_2075142
  have hstable : (prefixWord ++ tailWord_2075142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075142).length < 2 ^ (prefixWord ++ tailWord_2075142).sum := by decide
  have hdescent : baseEnd_2075142 < baseStart_2075142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075147 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_2075147 : Nat := 118140960795 + 2075147 * 2 ^ 59
def prefixEnd_2075147 : Nat := 4983230072969 + 3 ^ 40 * 2075147 * 2
def baseEnd_2075147 : Nat := 710365226490465141012719

theorem tailTrace_2075147 : CollatzResearch.WordTrace tailWord_2075147 prefixEnd_2075147 710365226490465141012719 := by
  unfold tailWord_2075147
  simp only [CollatzResearch.WordTrace]
  refine ⟨75686829013104300736935695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457886008736200491290463 75686829013104300736935695)
  ·
    refine ⟨113530243519656451105403543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75686829013104300736935695 113530243519656451105403543)
    ·
      refine ⟨170295365279484676658105315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113530243519656451105403543 170295365279484676658105315)
      ·
        refine ⟨255443047919227014987157973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170295365279484676658105315 255443047919227014987157973)
        ·
          refine ⟨5986946435606883163761515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 255443047919227014987157973 5986946435606883163761515)
          ·
            refine ⟨8980419653410324745642273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986946435606883163761515 8980419653410324745642273)
            ·
              refine ⟨6735314740057743559231705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8980419653410324745642273 6735314740057743559231705)
              ·
                refine ⟨5051486055043307669423779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6735314740057743559231705 5051486055043307669423779)
                ·
                  refine ⟨7577229082564961504135669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051486055043307669423779 7577229082564961504135669)
                  ·
                    refine ⟨710365226490465141012719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7577229082564961504135669 710365226490465141012719)
                    ·
                      rfl

theorem cell22_2075147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_2075147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075147 prefixEnd_2075147 := by exact prefixLift 2075147
  have htrace : WordTrace (prefixWord ++ tailWord_2075147) baseStart_2075147 baseEnd_2075147 := by
    simpa [prefixWord, tailWord_2075147, baseEnd_2075147] using wordTrace_append hprefix tailTrace_2075147
  have hstable : (prefixWord ++ tailWord_2075147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075147).length < 2 ^ (prefixWord ++ tailWord_2075147).sum := by decide
  have hdescent : baseEnd_2075147 < baseStart_2075147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075162 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_2075162 : Nat := 118140960795 + 2075162 * 2 ^ 59
def prefixEnd_2075162 : Nat := 4983230072969 + 3 ^ 40 * 2075162 * 2
def baseEnd_2075162 : Nat := 710370361297010101887673

theorem tailTrace_2075162 : CollatzResearch.WordTrace tailWord_2075162 prefixEnd_2075162 710370361297010101887673 := by
  unfold tailWord_2075162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921844027012489574682935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50458250738699972199154493 18921844027012489574682935)
  ·
    refine ⟨28382766040518734362024403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18921844027012489574682935 28382766040518734362024403)
    ·
      refine ⟨42574149060778101543036605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28382766040518734362024403 42574149060778101543036605)
      ·
        refine ⟨15965305897791788078638727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42574149060778101543036605 15965305897791788078638727)
        ·
          refine ⟨23947958846687682117958091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15965305897791788078638727 23947958846687682117958091)
          ·
            refine ⟨35921938270031523176937137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23947958846687682117958091 35921938270031523176937137)
            ·
              refine ⟨26941453702523642382702853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35921938270031523176937137 26941453702523642382702853)
              ·
                refine ⟨5051522569223182946756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26941453702523642382702853 5051522569223182946756785)
                ·
                  refine ⟨3788641926917387210067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5051522569223182946756785 3788641926917387210067589)
                  ·
                    refine ⟨710370361297010101887673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788641926917387210067589 710370361297010101887673)
                    ·
                      rfl

theorem cell22_2075162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_2075162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075162 prefixEnd_2075162 := by exact prefixLift 2075162
  have htrace : WordTrace (prefixWord ++ tailWord_2075162) baseStart_2075162 baseEnd_2075162 := by
    simpa [prefixWord, tailWord_2075162, baseEnd_2075162] using wordTrace_append hprefix tailTrace_2075162
  have hstable : (prefixWord ++ tailWord_2075162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075162).length < 2 ^ (prefixWord ++ tailWord_2075162).sum := by decide
  have hdescent : baseEnd_2075162 < baseStart_2075162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075164 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2075164 : Nat := 118140960795 + 2075164 * 2 ^ 59
def prefixEnd_2075164 : Nat := 4983230072969 + 3 ^ 40 * 2075164 * 2
def baseEnd_2075164 : Nat := 710371045937882763337667

theorem tailTrace_2075164 : CollatzResearch.WordTrace tailWord_2075164 prefixEnd_2075164 710371045937882763337667 := by
  unfold tailWord_2075164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37843724527021356320152273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50458299369361808426869697 37843724527021356320152273)
  ·
    refine ⟨28382793395266017240114205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37843724527021356320152273 28382793395266017240114205)
    ·
      refine ⟨10643547523224756465042827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28382793395266017240114205 10643547523224756465042827)
      ·
        refine ⟨15965321284837134697564241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643547523224756465042827 15965321284837134697564241)
        ·
          refine ⟨11973990963627851023173181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15965321284837134697564241 11973990963627851023173181)
          ·
            refine ⟨4490246611360444133689943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11973990963627851023173181 4490246611360444133689943)
            ·
              refine ⟨6735369917040666200534915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490246611360444133689943 6735369917040666200534915)
              ·
                refine ⟨10103054875560999300802373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735369917040666200534915 10103054875560999300802373)
                ·
                  refine ⟨1894322789167687368900445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10103054875560999300802373 1894322789167687368900445)
                  ·
                    refine ⟨710371045937882763337667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894322789167687368900445 710371045937882763337667)
                    ·
                      rfl

theorem cell22_2075164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2075164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075164 prefixEnd_2075164 := by exact prefixLift 2075164
  have htrace : WordTrace (prefixWord ++ tailWord_2075164) baseStart_2075164 baseEnd_2075164 := by
    simpa [prefixWord, tailWord_2075164, baseEnd_2075164] using wordTrace_append hprefix tailTrace_2075164
  have hstable : (prefixWord ++ tailWord_2075164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075164).length < 2 ^ (prefixWord ++ tailWord_2075164).sum := by decide
  have hdescent : baseEnd_2075164 < baseStart_2075164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075194 : List Nat := [3, 1, 1, 1, 3, 5, 2, 6]
def baseStart_2075194 : Nat := 118140960795 + 2075194 * 2 ^ 59
def prefixEnd_2075194 : Nat := 4983230072969 + 3 ^ 40 * 2075194 * 2
def baseEnd_2075194 : Nat := 78931257283441409454175

theorem tailTrace_2075194 : CollatzResearch.WordTrace tailWord_2075194 prefixEnd_2075194 78931257283441409454175 := by
  unfold tailWord_2075194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922135810983506940974159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50459028829289351842597757 18922135810983506940974159)
  ·
    refine ⟨28383203716475260411461239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922135810983506940974159 28383203716475260411461239)
    ·
      refine ⟨42574805574712890617191859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28383203716475260411461239 42574805574712890617191859)
      ·
        refine ⟨63862208362069335925787789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42574805574712890617191859 63862208362069335925787789)
        ·
          refine ⟨23948328135776000972170421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63862208362069335925787789 23948328135776000972170421)
          ·
            refine ⟨2245155762729000091140977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23948328135776000972170421 2245155762729000091140977)
            ·
              refine ⟨1683866822046750068355733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245155762729000091140977 1683866822046750068355733)
              ·
                refine ⟨78931257283441409454175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1683866822046750068355733 78931257283441409454175)
                ·
                  rfl

theorem cell22_2075194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_2075194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075194 prefixEnd_2075194 := by exact prefixLift 2075194
  have htrace : WordTrace (prefixWord ++ tailWord_2075194) baseStart_2075194 baseEnd_2075194 := by
    simpa [prefixWord, tailWord_2075194, baseEnd_2075194] using wordTrace_append hprefix tailTrace_2075194
  have hstable : (prefixWord ++ tailWord_2075194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075194).length < 2 ^ (prefixWord ++ tailWord_2075194).sum := by decide
  have hdescent : baseEnd_2075194 < baseStart_2075194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075361 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2075361 : Nat := 118140960795 + 2075361 * 2 ^ 59
def prefixEnd_2075361 : Nat := 4983230072969 + 3 ^ 40 * 2075361 * 2
def baseEnd_2075361 : Nat := 710438483063839916162063

theorem tailTrace_2075361 : CollatzResearch.WordTrace tailWord_2075361 prefixEnd_2075361 710438483063839916162063 := by
  unfold tailWord_2075361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75694634234329015285225937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50463089489552676856817291 75694634234329015285225937)
  ·
    refine ⟨56770975675746761463919453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75694634234329015285225937 56770975675746761463919453)
    ·
      refine ⟨21289115878405035548969795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56770975675746761463919453 21289115878405035548969795)
      ·
        refine ⟨31933673817607553323454693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21289115878405035548969795 31933673817607553323454693)
        ·
          refine ⟨5987563840801416248147755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31933673817607553323454693 5987563840801416248147755)
          ·
            refine ⟨8981345761202124372221633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987563840801416248147755 8981345761202124372221633)
            ·
              refine ⟨6736009320901593279166225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981345761202124372221633 6736009320901593279166225)
              ·
                refine ⟨5052006990676194959374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736009320901593279166225 5052006990676194959374669)
                ·
                  refine ⟨1894502621503573109765501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5052006990676194959374669 1894502621503573109765501)
                  ·
                    refine ⟨710438483063839916162063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894502621503573109765501 710438483063839916162063)
                    ·
                      rfl

theorem cell22_2075361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2075361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075361 prefixEnd_2075361 := by exact prefixLift 2075361
  have htrace : WordTrace (prefixWord ++ tailWord_2075361) baseStart_2075361 baseEnd_2075361 := by
    simpa [prefixWord, tailWord_2075361, baseEnd_2075361] using wordTrace_append hprefix tailTrace_2075361
  have hstable : (prefixWord ++ tailWord_2075361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075361).length < 2 ^ (prefixWord ++ tailWord_2075361).sum := by decide
  have hdescent : baseEnd_2075361 < baseStart_2075361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075374 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2075374 : Nat := 118140960795 + 2075374 * 2 ^ 59
def prefixEnd_2075374 : Nat := 4983230072969 + 3 ^ 40 * 2075374 * 2
def baseEnd_2075374 : Nat := 236814311076504071862341

theorem tailTrace_2075374 : CollatzResearch.WordTrace tailWord_2075374 prefixEnd_2075374 236814311076504071862341 := by
  unfold tailWord_2075374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461888547910239813181147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50463405588854612336966117 9461888547910239813181147)
  ·
    refine ⟨14192832821865359719771721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461888547910239813181147 14192832821865359719771721)
    ·
      refine ⟨10644624616399019789828791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14192832821865359719771721 10644624616399019789828791)
      ·
        refine ⟨15966936924598529684743187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644624616399019789828791 15966936924598529684743187)
        ·
          refine ⟨23950405386897794527114781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15966936924598529684743187 23950405386897794527114781)
          ·
            refine ⟨8981402020086672947668043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23950405386897794527114781 8981402020086672947668043)
            ·
              refine ⟨13472103030130009421502065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981402020086672947668043 13472103030130009421502065)
              ·
                refine ⟨10104077272597507066126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13472103030130009421502065 10104077272597507066126549)
                ·
                  refine ⟨236814311076504071862341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10104077272597507066126549 236814311076504071862341)
                  ·
                    rfl

theorem cell22_2075374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2075374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075374 prefixEnd_2075374 := by exact prefixLift 2075374
  have htrace : WordTrace (prefixWord ++ tailWord_2075374) baseStart_2075374 baseEnd_2075374 := by
    simpa [prefixWord, tailWord_2075374, baseEnd_2075374] using wordTrace_append hprefix tailTrace_2075374
  have hstable : (prefixWord ++ tailWord_2075374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075374).length < 2 ^ (prefixWord ++ tailWord_2075374).sum := by decide
  have hdescent : baseEnd_2075374 < baseStart_2075374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075380 : List Nat := [2, 6, 1, 1, 3, 1, 8]
def baseStart_2075380 : Nat := 118140960795 + 2075380 * 2 ^ 59
def prefixEnd_2075380 : Nat := 4983230072969 + 3 ^ 40 * 2075380 * 2
def baseEnd_2075380 : Nat := 26312777301930748145815

theorem tailTrace_2075380 : CollatzResearch.WordTrace tailWord_2075380 prefixEnd_2075380 26312777301930748145815 := by
  unfold tailWord_2075380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847663610630090765083797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50463551480840121020111729 37847663610630090765083797)
  ·
    refine ⟨1774109231748285504613303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37847663610630090765083797 1774109231748285504613303)
    ·
      refine ⟨2661163847622428256919955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774109231748285504613303 2661163847622428256919955)
      ·
        refine ⟨3991745771433642385379933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661163847622428256919955 3991745771433642385379933)
        ·
          refine ⟨1496904664287615894517475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991745771433642385379933 1496904664287615894517475)
          ·
            refine ⟨2245356996431423841776213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496904664287615894517475 2245356996431423841776213)
            ·
              refine ⟨26312777301930748145815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2245356996431423841776213 26312777301930748145815)
              ·
                rfl

theorem cell22_2075380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 8].length) (baseStart_2075380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075380 prefixEnd_2075380 := by exact prefixLift 2075380
  have htrace : WordTrace (prefixWord ++ tailWord_2075380) baseStart_2075380 baseEnd_2075380 := by
    simpa [prefixWord, tailWord_2075380, baseEnd_2075380] using wordTrace_append hprefix tailTrace_2075380
  have hstable : (prefixWord ++ tailWord_2075380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075380).length < 2 ^ (prefixWord ++ tailWord_2075380).sum := by decide
  have hdescent : baseEnd_2075380 < baseStart_2075380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075387 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_2075387 : Nat := 118140960795 + 2075387 * 2 ^ 59
def prefixEnd_2075387 : Nat := 4983230072969 + 3 ^ 40 * 2075387 * 2
def baseEnd_2075387 : Nat := 710447383395184515011983

theorem tailTrace_2075387 : CollatzResearch.WordTrace tailWord_2075387 prefixEnd_2075387 710447383395184515011983 := by
  unfold tailWord_2075387
  simp only [CollatzResearch.WordTrace]
  refine ⟨75695582532234821725672415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50463721688156547817114943 75695582532234821725672415)
  ·
    refine ⟨113543373798352232588508623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75695582532234821725672415 113543373798352232588508623)
    ·
      refine ⟨170315060697528348882762935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113543373798352232588508623 170315060697528348882762935)
      ·
        refine ⟨255472591046292523324144403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170315060697528348882762935 255472591046292523324144403)
        ·
          refine ⟨383208886569438784986216605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255472591046292523324144403 383208886569438784986216605)
          ·
            refine ⟨143703332463539544369831227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383208886569438784986216605 143703332463539544369831227)
            ·
              refine ⟨215554998695309316554746841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143703332463539544369831227 215554998695309316554746841)
              ·
                refine ⟨161666249021481987416060131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215554998695309316554746841 161666249021481987416060131)
                ·
                  refine ⟨242499373532222981124090197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161666249021481987416060131 242499373532222981124090197)
                  ·
                    refine ⟨710447383395184515011983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 242499373532222981124090197 710447383395184515011983)
                    ·
                      rfl

theorem cell22_2075387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_2075387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075387 prefixEnd_2075387 := by exact prefixLift 2075387
  have htrace : WordTrace (prefixWord ++ tailWord_2075387) baseStart_2075387 baseEnd_2075387 := by
    simpa [prefixWord, tailWord_2075387, baseEnd_2075387] using wordTrace_append hprefix tailTrace_2075387
  have hstable : (prefixWord ++ tailWord_2075387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075387).length < 2 ^ (prefixWord ++ tailWord_2075387).sum := by decide
  have hdescent : baseEnd_2075387 < baseStart_2075387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075404 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_2075404 : Nat := 118140960795 + 2075404 * 2 ^ 59
def prefixEnd_2075404 : Nat := 4983230072969 + 3 ^ 40 * 2075404 * 2
def baseEnd_2075404 : Nat := 710453202842602137336931

theorem tailTrace_2075404 : CollatzResearch.WordTrace tailWord_2075404 prefixEnd_2075404 710453202842602137336931 := by
  unfold tailWord_2075404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848101286586616814520633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50464135048782155752694177 37848101286586616814520633)
  ·
    refine ⟨28386075964939962610890475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37848101286586616814520633 28386075964939962610890475)
    ·
      refine ⟨42579113947409943916335713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28386075964939962610890475 42579113947409943916335713)
      ·
        refine ⟨31934335460557457937251785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42579113947409943916335713 31934335460557457937251785)
        ·
          refine ⟨23950751595418093452938839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31934335460557457937251785 23950751595418093452938839)
          ·
            refine ⟨35926127393127140179408259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950751595418093452938839 35926127393127140179408259)
            ·
              refine ⟨53889191089690710269112389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35926127393127140179408259 53889191089690710269112389)
              ·
                refine ⟨10104223329317008175458573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53889191089690710269112389 10104223329317008175458573)
                ·
                  refine ⟨3789083748493878065796965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104223329317008175458573 3789083748493878065796965)
                  ·
                    refine ⟨710453202842602137336931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789083748493878065796965 710453202842602137336931)
                    ·
                      rfl

theorem cell22_2075404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_2075404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075404 prefixEnd_2075404 := by exact prefixLift 2075404
  have htrace : WordTrace (prefixWord ++ tailWord_2075404) baseStart_2075404 baseEnd_2075404 := by
    simpa [prefixWord, tailWord_2075404, baseEnd_2075404] using wordTrace_append hprefix tailTrace_2075404
  have hstable : (prefixWord ++ tailWord_2075404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075404).length < 2 ^ (prefixWord ++ tailWord_2075404).sum := by decide
  have hdescent : baseEnd_2075404 < baseStart_2075404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075436 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_2075436 : Nat := 118140960795 + 2075436 * 2 ^ 59
def prefixEnd_2075436 : Nat := 4983230072969 + 3 ^ 40 * 2075436 * 2
def baseEnd_2075436 : Nat := 236821385698854906845611

theorem tailTrace_2075436 : CollatzResearch.WordTrace tailWord_2075436 prefixEnd_2075436 236821385698854906845611 := by
  unfold tailWord_2075436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848684854528651547103081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50464913139371535396137441 37848684854528651547103081)
  ·
    refine ⟨28386513640896488660327311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37848684854528651547103081 28386513640896488660327311)
    ·
      refine ⟨42579770461344732990490967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28386513640896488660327311 42579770461344732990490967)
      ·
        refine ⟨63869655692017099485736451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42579770461344732990490967 63869655692017099485736451)
        ·
          refine ⟨95804483538025649228604677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63869655692017099485736451 95804483538025649228604677)
          ·
            refine ⟨17963340663379809230363377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95804483538025649228604677 17963340663379809230363377)
            ·
              refine ⟨13472505497534856922772533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17963340663379809230363377 13472505497534856922772533)
              ·
                refine ⟨1263047390393892836509925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13472505497534856922772533 1263047390393892836509925)
                ·
                  refine ⟨236821385698854906845611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263047390393892836509925 236821385698854906845611)
                  ·
                    rfl

theorem cell22_2075436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_2075436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075436 prefixEnd_2075436 := by exact prefixLift 2075436
  have htrace : WordTrace (prefixWord ++ tailWord_2075436) baseStart_2075436 baseEnd_2075436 := by
    simpa [prefixWord, tailWord_2075436, baseEnd_2075436] using wordTrace_append hprefix tailTrace_2075436
  have hstable : (prefixWord ++ tailWord_2075436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075436).length < 2 ^ (prefixWord ++ tailWord_2075436).sum := by decide
  have hdescent : baseEnd_2075436 < baseStart_2075436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075446 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2075446 : Nat := 118140960795 + 2075446 * 2 ^ 59
def prefixEnd_2075446 : Nat := 4983230072969 + 3 ^ 40 * 2075446 * 2
def baseEnd_2075446 : Nat := 710467580300928027786803

theorem tailTrace_2075446 : CollatzResearch.WordTrace tailWord_2075446 prefixEnd_2075446 710467580300928027786803 := by
  unfold tailWord_2075446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731108402438817175129387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50465156292680716534713461 4731108402438817175129387)
  ·
    refine ⟨7096662603658225762694081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4731108402438817175129387 7096662603658225762694081)
    ·
      refine ⟨5322496952743669322020561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7096662603658225762694081 5322496952743669322020561)
      ·
        refine ⟨3991872714557751991515421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322496952743669322020561 3991872714557751991515421)
        ·
          refine ⟨1496952267959156996818283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991872714557751991515421 1496952267959156996818283)
          ·
            refine ⟨2245428401938735495227425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496952267959156996818283 2245428401938735495227425)
            ·
              refine ⟨1684071301454051621420569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245428401938735495227425 1684071301454051621420569)
              ·
                refine ⟨1263053476090538716065427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684071301454051621420569 1263053476090538716065427)
                ·
                  refine ⟨1894580214135808074098141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263053476090538716065427 1894580214135808074098141)
                  ·
                    refine ⟨710467580300928027786803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894580214135808074098141 710467580300928027786803)
                    ·
                      rfl

theorem cell22_2075446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2075446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075446 prefixEnd_2075446 := by exact prefixLift 2075446
  have htrace : WordTrace (prefixWord ++ tailWord_2075446) baseStart_2075446 baseEnd_2075446 := by
    simpa [prefixWord, tailWord_2075446, baseEnd_2075446] using wordTrace_append hprefix tailTrace_2075446
  have hstable : (prefixWord ++ tailWord_2075446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075446).length < 2 ^ (prefixWord ++ tailWord_2075446).sum := by decide
  have hdescent : baseEnd_2075446 < baseStart_2075446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075468 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_2075468 : Nat := 118140960795 + 2075468 * 2 ^ 59
def prefixEnd_2075468 : Nat := 4983230072969 + 3 ^ 40 * 2075468 * 2
def baseEnd_2075468 : Nat := 710475111350527303736735

theorem tailTrace_2075468 : CollatzResearch.WordTrace tailWord_2075468 prefixEnd_2075468 710475111350527303736735 := by
  unfold tailWord_2075468
  simp only [CollatzResearch.WordTrace]
  refine ⟨37849268422470686279685529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50465691229960915039580705 37849268422470686279685529)
  ·
    refine ⟨28386951316853014709764147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37849268422470686279685529 28386951316853014709764147)
    ·
      refine ⟨42580426975279522064646221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28386951316853014709764147 42580426975279522064646221)
      ·
        refine ⟨15967660115729820774242333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42580426975279522064646221 15967660115729820774242333)
        ·
          refine ⟨5987872543398682790340875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15967660115729820774242333 5987872543398682790340875)
          ·
            refine ⟨8981808815098024185511313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987872543398682790340875 8981808815098024185511313)
            ·
              refine ⟨6736356611323518139133485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981808815098024185511313 6736356611323518139133485)
              ·
                refine ⟨2526133729246319302175057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6736356611323518139133485 2526133729246319302175057)
                ·
                  refine ⟨1894600296934739476631293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526133729246319302175057 1894600296934739476631293)
                  ·
                    refine ⟨710475111350527303736735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894600296934739476631293 710475111350527303736735)
                    ·
                      rfl

theorem cell22_2075468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_2075468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075468 prefixEnd_2075468 := by exact prefixLift 2075468
  have htrace : WordTrace (prefixWord ++ tailWord_2075468) baseStart_2075468 baseEnd_2075468 := by
    simpa [prefixWord, tailWord_2075468, baseEnd_2075468] using wordTrace_append hprefix tailTrace_2075468
  have hstable : (prefixWord ++ tailWord_2075468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075468).length < 2 ^ (prefixWord ++ tailWord_2075468).sum := by decide
  have hdescent : baseEnd_2075468 < baseStart_2075468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075481 : List Nat := [1, 2, 1, 2, 2, 5, 3, 6]
def baseStart_2075481 : Nat := 118140960795 + 2075481 * 2 ^ 59
def prefixEnd_2075481 : Nat := 4983230072969 + 3 ^ 40 * 2075481 * 2
def baseEnd_2075481 : Nat := 78942173501799955906855

theorem tailTrace_2075481 : CollatzResearch.WordTrace tailWord_2075481 prefixEnd_2075481 78942173501799955906855 := by
  unfold tailWord_2075481
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699010993894275779594297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466007329262850519729531 75699010993894275779594297)
  ·
    refine ⟨56774258245420706834695723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75699010993894275779594297 56774258245420706834695723)
    ·
      refine ⟨85161387368131060252043585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56774258245420706834695723 85161387368131060252043585)
      ·
        refine ⟨63871040526098295189032689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85161387368131060252043585 63871040526098295189032689)
        ·
          refine ⟨47903280394573721391774517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63871040526098295189032689 47903280394573721391774517)
          ·
            refine ⟨4490932536991286380478861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47903280394573721391774517 4490932536991286380478861)
            ·
              refine ⟨1684099701371732392679573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4490932536991286380478861 1684099701371732392679573)
              ·
                refine ⟨78942173501799955906855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1684099701371732392679573 78942173501799955906855)
                ·
                  rfl

theorem cell22_2075481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 6].length) (baseStart_2075481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075481 prefixEnd_2075481 := by exact prefixLift 2075481
  have htrace : WordTrace (prefixWord ++ tailWord_2075481) baseStart_2075481 baseEnd_2075481 := by
    simpa [prefixWord, tailWord_2075481, baseEnd_2075481] using wordTrace_append hprefix tailTrace_2075481
  have hstable : (prefixWord ++ tailWord_2075481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075481).length < 2 ^ (prefixWord ++ tailWord_2075481).sum := by decide
  have hdescent : baseEnd_2075481 < baseStart_2075481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075502 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2075502 : Nat := 118140960795 + 2075502 * 2 ^ 59
def prefixEnd_2075502 : Nat := 4983230072969 + 3 ^ 40 * 2075502 * 2
def baseEnd_2075502 : Nat := 710486750245362548386631

theorem tailTrace_2075502 : CollatzResearch.WordTrace tailWord_2075502 prefixEnd_2075502 710486750245362548386631 := by
  unfold tailWord_2075502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462472115852274545763595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50466517951212130910739173 9462472115852274545763595)
  ·
    refine ⟨14193708173778411818645393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9462472115852274545763595 14193708173778411818645393)
    ·
      refine ⟨10645281130333808863984045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14193708173778411818645393 10645281130333808863984045)
      ·
        refine ⟨3991980423875178323994017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10645281130333808863984045 3991980423875178323994017)
        ·
          refine ⟨2993985317906383742995513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3991980423875178323994017 2993985317906383742995513)
          ·
            refine ⟨2245488988429787807246635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993985317906383742995513 2245488988429787807246635)
            ·
              refine ⟨3368233482644681710869953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245488988429787807246635 3368233482644681710869953)
              ·
                refine ⟨2526175111983511283152465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368233482644681710869953 2526175111983511283152465)
                ·
                  refine ⟨1894631333987633462364349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526175111983511283152465 1894631333987633462364349)
                  ·
                    refine ⟨710486750245362548386631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894631333987633462364349 710486750245362548386631)
                    ·
                      rfl

theorem cell22_2075502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2075502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075502 prefixEnd_2075502 := by exact prefixLift 2075502
  have htrace : WordTrace (prefixWord ++ tailWord_2075502) baseStart_2075502 baseEnd_2075502 := by
    simpa [prefixWord, tailWord_2075502, baseEnd_2075502] using wordTrace_append hprefix tailTrace_2075502
  have hstable : (prefixWord ++ tailWord_2075502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075502).length < 2 ^ (prefixWord ++ tailWord_2075502).sum := by decide
  have hdescent : baseEnd_2075502 < baseStart_2075502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075513 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_2075513 : Nat := 118140960795 + 2075513 * 2 ^ 59
def prefixEnd_2075513 : Nat := 4983230072969 + 3 ^ 40 * 2075513 * 2
def baseEnd_2075513 : Nat := 710490515770162186361597

theorem tailTrace_2075513 : CollatzResearch.WordTrace tailWord_2075513 prefixEnd_2075513 710490515770162186361597 := by
  unfold tailWord_2075513
  simp only [CollatzResearch.WordTrace]
  refine ⟨75700178129778345244759193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466785419852230163172795 75700178129778345244759193)
  ·
    refine ⟨56775133597333758933569395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75700178129778345244759193 56775133597333758933569395)
    ·
      refine ⟨85162700396000638400354093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56775133597333758933569395 85162700396000638400354093)
      ·
        refine ⟨31936012648500239400132785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85162700396000638400354093 31936012648500239400132785)
        ·
          refine ⟨23952009486375179550099589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31936012648500239400132785 23952009486375179550099589)
          ·
            refine ⟨4491001778695346165643673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23952009486375179550099589 4491001778695346165643673)
            ·
              refine ⟨3368251334021509624232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491001778695346165643673 3368251334021509624232755)
              ·
                refine ⟨5052377001032264436349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368251334021509624232755 5052377001032264436349133)
                ·
                  refine ⟨1894641375387099163630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5052377001032264436349133 1894641375387099163630925)
                  ·
                    refine ⟨710490515770162186361597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894641375387099163630925 710490515770162186361597)
                    ·
                      rfl

theorem cell22_2075513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_2075513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075513 prefixEnd_2075513 := by exact prefixLift 2075513
  have htrace : WordTrace (prefixWord ++ tailWord_2075513) baseStart_2075513 baseEnd_2075513 := by
    simpa [prefixWord, tailWord_2075513, baseEnd_2075513] using wordTrace_append hprefix tailTrace_2075513
  have hstable : (prefixWord ++ tailWord_2075513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075513).length < 2 ^ (prefixWord ++ tailWord_2075513).sum := by decide
  have hdescent : baseEnd_2075513 < baseStart_2075513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075633 : List Nat := [1, 2, 2, 2, 4, 3, 1, 7]
def baseStart_2075633 : Nat := 118140960795 + 2075633 * 2 ^ 59
def prefixEnd_2075633 : Nat := 4983230072969 + 3 ^ 40 * 2075633 * 2
def baseEnd_2075633 : Nat := 78947954913613541484581

theorem tailTrace_2075633 : CollatzResearch.WordTrace tailWord_2075633 prefixEnd_2075633 78947954913613541484581 := by
  unfold tailWord_2075633
  simp only [CollatzResearch.WordTrace]
  refine ⟨75704554889343605739127553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50469703259562403826085035 75704554889343605739127553)
  ·
    refine ⟨56778416167007704304345665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75704554889343605739127553 56778416167007704304345665)
    ·
      refine ⟨42583812125255778228259249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56778416167007704304345665 42583812125255778228259249)
      ·
        refine ⟨31937859093941833671194437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42583812125255778228259249 31937859093941833671194437)
        ·
          refine ⟨5988348580114093813348957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31937859093941833671194437 5988348580114093813348957)
          ·
            refine ⟨2245630717542785180005859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5988348580114093813348957 2245630717542785180005859)
            ·
              refine ⟨3368446076314177770008789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245630717542785180005859 3368446076314177770008789)
              ·
                refine ⟨78947954913613541484581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3368446076314177770008789 78947954913613541484581)
                ·
                  rfl

theorem cell22_2075633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 7].length) (baseStart_2075633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075633 prefixEnd_2075633 := by exact prefixLift 2075633
  have htrace : WordTrace (prefixWord ++ tailWord_2075633) baseStart_2075633 baseEnd_2075633 := by
    simpa [prefixWord, tailWord_2075633, baseEnd_2075633] using wordTrace_append hprefix tailTrace_2075633
  have hstable : (prefixWord ++ tailWord_2075633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075633).length < 2 ^ (prefixWord ++ tailWord_2075633).sum := by decide
  have hdescent : baseEnd_2075633 < baseStart_2075633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075637 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2075637 : Nat := 118140960795 + 2075637 * 2 ^ 59
def prefixEnd_2075637 : Nat := 4983230072969 + 3 ^ 40 * 2075637 * 2
def baseEnd_2075637 : Nat := 710532963504267196261217

theorem tailTrace_2075637 : CollatzResearch.WordTrace tailWord_2075637 prefixEnd_2075637 710532963504267196261217 := by
  unfold tailWord_2075637
  simp only [CollatzResearch.WordTrace]
  refine ⟨75704700781329114422273165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50469800520886076281515443 75704700781329114422273165)
  ·
    refine ⟨28389262792998417908352437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75704700781329114422273165 28389262792998417908352437)
    ·
      refine ⟨2661493386843601678908041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28389262792998417908352437 2661493386843601678908041)
      ·
        refine ⟨1996120040132701259181031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661493386843601678908041 1996120040132701259181031)
        ·
          refine ⟨2994180060199051888771547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996120040132701259181031 2994180060199051888771547)
          ·
            refine ⟨4491270090298577833157321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994180060199051888771547 4491270090298577833157321)
            ·
              refine ⟨3368452567723933374867991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491270090298577833157321 3368452567723933374867991)
              ·
                refine ⟨5052678851585900062301987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368452567723933374867991 5052678851585900062301987)
                ·
                  refine ⟨7579018277378850093452981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052678851585900062301987 7579018277378850093452981)
                  ·
                    refine ⟨710532963504267196261217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7579018277378850093452981 710532963504267196261217)
                    ·
                      rfl

theorem cell22_2075637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2075637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075637 prefixEnd_2075637 := by exact prefixLift 2075637
  have htrace : WordTrace (prefixWord ++ tailWord_2075637) baseStart_2075637 baseEnd_2075637 := by
    simpa [prefixWord, tailWord_2075637, baseEnd_2075637] using wordTrace_append hprefix tailTrace_2075637
  have hstable : (prefixWord ++ tailWord_2075637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075637).length < 2 ^ (prefixWord ++ tailWord_2075637).sum := by decide
  have hdescent : baseEnd_2075637 < baseStart_2075637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075682 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2075682 : Nat := 118140960795 + 2075682 * 2 ^ 59
def prefixEnd_2075682 : Nat := 4983230072969 + 3 ^ 40 * 2075682 * 2
def baseEnd_2075682 : Nat := 710548367923902078886079

theorem tailTrace_2075682 : CollatzResearch.WordTrace tailWord_2075682 prefixEnd_2075682 710548367923902078886079 := by
  unfold tailWord_2075682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926585516541521776915325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50470894710777391405107533 18926585516541521776915325)
  ·
    refine ⟨7097469568703070666343247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18926585516541521776915325 7097469568703070666343247)
    ·
      refine ⟨10646204353054605999514871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097469568703070666343247 10646204353054605999514871)
      ·
        refine ⟨15969306529581908999272307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10646204353054605999514871 15969306529581908999272307)
        ·
          refine ⟨23953959794372863498908461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969306529581908999272307 23953959794372863498908461)
          ·
            refine ⟨8982734922889823812090673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23953959794372863498908461 8982734922889823812090673)
            ·
              refine ⟨6737051192167367859068005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982734922889823812090673 6737051192167367859068005)
              ·
                refine ⟨1263197098531381473575251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6737051192167367859068005 1263197098531381473575251)
                ·
                  refine ⟨1894795647797072210362877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263197098531381473575251 1894795647797072210362877)
                  ·
                    refine ⟨710548367923902078886079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894795647797072210362877 710548367923902078886079)
                    ·
                      rfl

theorem cell22_2075682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2075682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075682 prefixEnd_2075682 := by exact prefixLift 2075682
  have htrace : WordTrace (prefixWord ++ tailWord_2075682) baseStart_2075682 baseEnd_2075682 := by
    simpa [prefixWord, tailWord_2075682, baseEnd_2075682] using wordTrace_append hprefix tailTrace_2075682
  have hstable : (prefixWord ++ tailWord_2075682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075682).length < 2 ^ (prefixWord ++ tailWord_2075682).sum := by decide
  have hdescent : baseEnd_2075682 < baseStart_2075682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075843 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_2075843 : Nat := 118140960795 + 2075843 * 2 ^ 59
def prefixEnd_2075843 : Nat := 4983230072969 + 3 ^ 40 * 2075843 * 2
def baseEnd_2075843 : Nat := 710603481514151325610585

theorem tailTrace_2075843 : CollatzResearch.WordTrace tailWord_2075843 prefixEnd_2075843 710603481514151325610585 := by
  unfold tailWord_2075843
  simp only [CollatzResearch.WordTrace]
  refine ⟨75712214218582811604272183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50474809479055207736181455 75712214218582811604272183)
  ·
    refine ⟨113568321327874217406408275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75712214218582811604272183 113568321327874217406408275)
    ·
      refine ⟨170352481991811326109612413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113568321327874217406408275 170352481991811326109612413)
      ·
        refine ⟨63882180746929247291104655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170352481991811326109612413 63882180746929247291104655)
        ·
          refine ⟨95823271120393870936656983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63882180746929247291104655 95823271120393870936656983)
          ·
            refine ⟨143734906680590806404985475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95823271120393870936656983 143734906680590806404985475)
            ·
              refine ⟨215602360020886209607478213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143734906680590806404985475 215602360020886209607478213)
              ·
                refine ⟨40425442503916164301402165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215602360020886209607478213 40425442503916164301402165)
                ·
                  refine ⟨3789885234742140403256453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40425442503916164301402165 3789885234742140403256453)
                  ·
                    refine ⟨710603481514151325610585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789885234742140403256453 710603481514151325610585)
                    ·
                      rfl

theorem cell22_2075843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_2075843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075843 prefixEnd_2075843 := by exact prefixLift 2075843
  have htrace : WordTrace (prefixWord ++ tailWord_2075843) baseStart_2075843 baseEnd_2075843 := by
    simpa [prefixWord, tailWord_2075843, baseEnd_2075843] using wordTrace_append hprefix tailTrace_2075843
  have hstable : (prefixWord ++ tailWord_2075843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075843).length < 2 ^ (prefixWord ++ tailWord_2075843).sum := by decide
  have hdescent : baseEnd_2075843 < baseStart_2075843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075903 : List Nat := [1, 1, 2, 2, 1, 5, 10]
def baseStart_2075903 : Nat := 118140960795 + 2075903 * 2 ^ 59
def prefixEnd_2075903 : Nat := 4983230072969 + 3 ^ 40 * 2075903 * 2
def baseEnd_2075903 : Nat := 26319408175567821078163

theorem tailTrace_2075903 : CollatzResearch.WordTrace tailWord_2075903 prefixEnd_2075903 26319408175567821078163 := by
  unfold tailWord_2075903
  simp only [CollatzResearch.WordTrace]
  refine ⟨75714402598365441851456363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50476268398910294567637575 75714402598365441851456363)
  ·
    refine ⟨113571603897548162777184545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75714402598365441851456363 113571603897548162777184545)
    ·
      refine ⟨85178702923161122082888409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113571603897548162777184545 85178702923161122082888409)
      ·
        refine ⟨63884027192370841562166307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85178702923161122082888409 63884027192370841562166307)
        ·
          refine ⟨95826040788556262343249461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63884027192370841562166307 95826040788556262343249461)
          ·
            refine ⟨8983691323927149594679637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95826040788556262343249461 8983691323927149594679637)
            ·
              refine ⟨26319408175567821078163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8983691323927149594679637 26319408175567821078163)
              ·
                rfl

theorem cell22_2075903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 10].length) (baseStart_2075903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075903 prefixEnd_2075903 := by exact prefixLift 2075903
  have htrace : WordTrace (prefixWord ++ tailWord_2075903) baseStart_2075903 baseEnd_2075903 := by
    simpa [prefixWord, tailWord_2075903, baseEnd_2075903] using wordTrace_append hprefix tailTrace_2075903
  have hstable : (prefixWord ++ tailWord_2075903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075903).length < 2 ^ (prefixWord ++ tailWord_2075903).sum := by decide
  have hdescent : baseEnd_2075903 < baseStart_2075903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075905 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2075905 : Nat := 118140960795 + 2075905 * 2 ^ 59
def prefixEnd_2075905 : Nat := 4983230072969 + 3 ^ 40 * 2075905 * 2
def baseEnd_2075905 : Nat := 710624705381203830560395

theorem tailTrace_2075905 : CollatzResearch.WordTrace tailWord_2075905 prefixEnd_2075905 710624705381203830560395 := by
  unfold tailWord_2075905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75714475544358196193029169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50476317029572130795352779 75714475544358196193029169)
  ·
    refine ⟨56785856658268647144771877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75714475544358196193029169 56785856658268647144771877)
    ·
      refine ⟨10647348123425371339644727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56785856658268647144771877 10647348123425371339644727)
      ·
        refine ⟨15971022185138057009467091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647348123425371339644727 15971022185138057009467091)
        ·
          refine ⟨23956533277707085514200637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971022185138057009467091 23956533277707085514200637)
          ·
            refine ⟨8983699979140157067825239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23956533277707085514200637 8983699979140157067825239)
            ·
              refine ⟨13475549968710235601737859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983699979140157067825239 13475549968710235601737859)
              ·
                refine ⟨20213324953065353402606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475549968710235601737859 20213324953065353402606789)
                ·
                  refine ⟨3789998428699753762988773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20213324953065353402606789 3789998428699753762988773)
                  ·
                    refine ⟨710624705381203830560395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789998428699753762988773 710624705381203830560395)
                    ·
                      rfl

theorem cell22_2075905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2075905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075905 prefixEnd_2075905 := by exact prefixLift 2075905
  have htrace : WordTrace (prefixWord ++ tailWord_2075905) baseStart_2075905 baseEnd_2075905 := by
    simpa [prefixWord, tailWord_2075905, baseEnd_2075905] using wordTrace_append hprefix tailTrace_2075905
  have hstable : (prefixWord ++ tailWord_2075905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075905).length < 2 ^ (prefixWord ++ tailWord_2075905).sum := by decide
  have hdescent : baseEnd_2075905 < baseStart_2075905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075958 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2075958 : Nat := 118140960795 + 2075958 * 2 ^ 59
def prefixEnd_2075958 : Nat := 4983230072969 + 3 ^ 40 * 2075958 * 2
def baseEnd_2075958 : Nat := 710642848364329358985233

theorem tailTrace_2075958 : CollatzResearch.WordTrace tailWord_2075958 prefixEnd_2075958 710642848364329358985233 := by
  unfold tailWord_2075958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732275538322886640294283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50477605742110790829805685 4732275538322886640294283)
  ·
    refine ⟨7098413307484329960441425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732275538322886640294283 7098413307484329960441425)
    ·
      refine ⟨5323809980613247470331069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7098413307484329960441425 5323809980613247470331069)
      ·
        refine ⟨1996428742729967801374151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5323809980613247470331069 1996428742729967801374151)
        ·
          refine ⟨2994643114094951702061227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996428742729967801374151 2994643114094951702061227)
          ·
            refine ⟨4491964671142427553091841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994643114094951702061227 4491964671142427553091841)
            ·
              refine ⟨3368973503356820664818881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491964671142427553091841 3368973503356820664818881)
              ·
                refine ⟨2526730127517615498614161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368973503356820664818881 2526730127517615498614161)
                ·
                  refine ⟨1895047595638211623960621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526730127517615498614161 1895047595638211623960621)
                  ·
                    refine ⟨710642848364329358985233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1895047595638211623960621 710642848364329358985233)
                    ·
                      rfl

theorem cell22_2075958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2075958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075958 prefixEnd_2075958 := by exact prefixLift 2075958
  have htrace : WordTrace (prefixWord ++ tailWord_2075958) baseStart_2075958 baseEnd_2075958 := by
    simpa [prefixWord, tailWord_2075958, baseEnd_2075958] using wordTrace_append hprefix tailTrace_2075958
  have hstable : (prefixWord ++ tailWord_2075958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075958).length < 2 ^ (prefixWord ++ tailWord_2075958).sum := by decide
  have hdescent : baseEnd_2075958 < baseStart_2075958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075980 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_2075980 : Nat := 118140960795 + 2075980 * 2 ^ 59
def prefixEnd_2075980 : Nat := 4983230072969 + 3 ^ 40 * 2075980 * 2
def baseEnd_2075980 : Nat := 710650379413928634935165

theorem tailTrace_2075980 : CollatzResearch.WordTrace tailWord_2075980 prefixEnd_2075980 710650379413928634935165 := by
  unfold tailWord_2075980
  simp only [CollatzResearch.WordTrace]
  refine ⟨37858605509543242001004697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50478140679390989334672929 37858605509543242001004697)
  ·
    refine ⟨28393954132157431500753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37858605509543242001004697 28393954132157431500753523)
    ·
      refine ⟨42590931198236147251130285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28393954132157431500753523 42590931198236147251130285)
      ·
        refine ⟨15971599199338555219173857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42590931198236147251130285 15971599199338555219173857)
        ·
          refine ⟨11978699399503916414380393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971599199338555219173857 11978699399503916414380393)
          ·
            refine ⟨8984024549627937310785295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11978699399503916414380393 8984024549627937310785295)
            ·
              refine ⟨13476036824441905966177943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984024549627937310785295 13476036824441905966177943)
              ·
                refine ⟨20214055236662858949266915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13476036824441905966177943 20214055236662858949266915)
                ·
                  refine ⟨30321082854994288423900373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20214055236662858949266915 30321082854994288423900373)
                  ·
                    refine ⟨710650379413928634935165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30321082854994288423900373 710650379413928634935165)
                    ·
                      rfl

theorem cell22_2075980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_2075980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075980 prefixEnd_2075980 := by exact prefixLift 2075980
  have htrace : WordTrace (prefixWord ++ tailWord_2075980) baseStart_2075980 baseEnd_2075980 := by
    simpa [prefixWord, tailWord_2075980, baseEnd_2075980] using wordTrace_append hprefix tailTrace_2075980
  have hstable : (prefixWord ++ tailWord_2075980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075980).length < 2 ^ (prefixWord ++ tailWord_2075980).sum := by decide
  have hdescent : baseEnd_2075980 < baseStart_2075980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075990 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2075990 : Nat := 118140960795 + 2075990 * 2 ^ 59
def prefixEnd_2075990 : Nat := 4983230072969 + 3 ^ 40 * 2075990 * 2
def baseEnd_2075990 : Nat := 710653802618291942185135

theorem tailTrace_2075990 : CollatzResearch.WordTrace tailWord_2075990 prefixEnd_2075990 710653802618291942185135 := by
  unfold tailWord_2075990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732348484315640981867089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50478383832700170473248949 4732348484315640981867089)
  ·
    refine ⟨3549261363236730736400317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732348484315640981867089 3549261363236730736400317)
    ·
      refine ⟨1330973011213774026150119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3549261363236730736400317 1330973011213774026150119)
      ·
        refine ⟨1996459516820661039225179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330973011213774026150119 1996459516820661039225179)
        ·
          refine ⟨2994689275230991558837769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996459516820661039225179 2994689275230991558837769)
          ·
            refine ⟨2246016956423243669128327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994689275230991558837769 2246016956423243669128327)
            ·
              refine ⟨3369025434634865503692491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246016956423243669128327 3369025434634865503692491)
              ·
                refine ⟨5053538151952298255538737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369025434634865503692491 5053538151952298255538737)
                ·
                  refine ⟨3790153613964223691654053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053538151952298255538737 3790153613964223691654053)
                  ·
                    refine ⟨710653802618291942185135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790153613964223691654053 710653802618291942185135)
                    ·
                      rfl

theorem cell22_2075990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2075990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2075990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2075990 prefixEnd_2075990 := by exact prefixLift 2075990
  have htrace : WordTrace (prefixWord ++ tailWord_2075990) baseStart_2075990 baseEnd_2075990 := by
    simpa [prefixWord, tailWord_2075990, baseEnd_2075990] using wordTrace_append hprefix tailTrace_2075990
  have hstable : (prefixWord ++ tailWord_2075990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075990).length < 2 ^ (prefixWord ++ tailWord_2075990).sum := by decide
  have hdescent : baseEnd_2075990 < baseStart_2075990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076025 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_2076025 : Nat := 118140960795 + 2076025 * 2 ^ 59
def prefixEnd_2076025 : Nat := 4983230072969 + 3 ^ 40 * 2076025 * 2
def baseEnd_2076025 : Nat := 710665783833563517560027

theorem tailTrace_2076025 : CollatzResearch.WordTrace tailWord_2076025 prefixEnd_2076025 710665783833563517560027 := by
  unfold tailWord_2076025
  simp only [CollatzResearch.WordTrace]
  refine ⟨75718852303923456687397529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50479234869282304458265019 75718852303923456687397529)
  ·
    refine ⟨56789139227942592515548147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75718852303923456687397529 56789139227942592515548147)
    ·
      refine ⟨85183708841913888773322221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56789139227942592515548147 85183708841913888773322221)
      ·
        refine ⟨31943890815717708289995833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85183708841913888773322221 31943890815717708289995833)
        ·
          refine ⟨23957918111788281217496875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31943890815717708289995833 23957918111788281217496875)
          ·
            refine ⟨35936877167682421826245313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23957918111788281217496875 35936877167682421826245313)
            ·
              refine ⟨26952657875761816369683985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35936877167682421826245313 26952657875761816369683985)
              ·
                refine ⟨20214493406821362277262989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26952657875761816369683985 20214493406821362277262989)
                ·
                  refine ⟨7580435027558010853973621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20214493406821362277262989 7580435027558010853973621)
                  ·
                    refine ⟨710665783833563517560027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7580435027558010853973621 710665783833563517560027)
                    ·
                      rfl

theorem cell22_2076025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_2076025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076025 prefixEnd_2076025 := by exact prefixLift 2076025
  have htrace : WordTrace (prefixWord ++ tailWord_2076025) baseStart_2076025 baseEnd_2076025 := by
    simpa [prefixWord, tailWord_2076025, baseEnd_2076025] using wordTrace_append hprefix tailTrace_2076025
  have hstable : (prefixWord ++ tailWord_2076025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076025).length < 2 ^ (prefixWord ++ tailWord_2076025).sum := by decide
  have hdescent : baseEnd_2076025 < baseStart_2076025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076027 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 4]
def baseStart_2076027 : Nat := 118140960795 + 2076027 * 2 ^ 59
def prefixEnd_2076027 : Nat := 4983230072969 + 3 ^ 40 * 2076027 * 2
def baseEnd_2076027 : Nat := 236888822824812059670007

theorem tailTrace_2076027 : CollatzResearch.WordTrace tailWord_2076027 prefixEnd_2076027 236888822824812059670007 := by
  unfold tailWord_2076027
  simp only [CollatzResearch.WordTrace]
  refine ⟨75718925249916211028970335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50479283499944140685980223 75718925249916211028970335)
  ·
    refine ⟨113578387874874316543455503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75718925249916211028970335 113578387874874316543455503)
    ·
      refine ⟨170367581812311474815183255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113578387874874316543455503 170367581812311474815183255)
      ·
        refine ⟨255551372718467212222774883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170367581812311474815183255 255551372718467212222774883)
        ·
          refine ⟨383327059077700818334162325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255551372718467212222774883 383327059077700818334162325)
          ·
            refine ⟨17968455894267225859413859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383327059077700818334162325 17968455894267225859413859)
            ·
              refine ⟨26952683841400838789120789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968455894267225859413859 26952683841400838789120789)
              ·
                refine ⟨1263407055065664318240037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26952683841400838789120789 1263407055065664318240037)
                ·
                  refine ⟨236888822824812059670007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263407055065664318240037 236888822824812059670007)
                  ·
                    rfl

theorem cell22_2076027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 4].length) (baseStart_2076027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076027 prefixEnd_2076027 := by exact prefixLift 2076027
  have htrace : WordTrace (prefixWord ++ tailWord_2076027) baseStart_2076027 baseEnd_2076027 := by
    simpa [prefixWord, tailWord_2076027, baseEnd_2076027] using wordTrace_append hprefix tailTrace_2076027
  have hstable : (prefixWord ++ tailWord_2076027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076027).length < 2 ^ (prefixWord ++ tailWord_2076027).sum := by decide
  have hdescent : baseEnd_2076027 < baseStart_2076027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076046 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2076046 : Nat := 118140960795 + 2076046 * 2 ^ 59
def prefixEnd_2076046 : Nat := 4983230072969 + 3 ^ 40 * 2076046 * 2
def baseEnd_2076046 : Nat := 710672972562726462784963

theorem tailTrace_2076046 : CollatzResearch.WordTrace tailWord_2076046 prefixEnd_2076046 710672972562726462784963 := by
  unfold tailWord_2076046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464952279605922159238999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50479745491231584849274661 9464952279605922159238999)
  ·
    refine ⟨14197428419408883238858499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464952279605922159238999 14197428419408883238858499)
    ·
      refine ⟨21296142629113324858287749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197428419408883238858499 21296142629113324858287749)
      ·
        refine ⟨3993026742958748410928953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21296142629113324858287749 3993026742958748410928953)
        ·
          refine ⟨2994770057219061308196715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993026742958748410928953 2994770057219061308196715)
          ·
            refine ⟨4492155085828591962295073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994770057219061308196715 4492155085828591962295073)
            ·
              refine ⟨3369116314371443971721305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492155085828591962295073 3369116314371443971721305)
              ·
                refine ⟨2526837235778582978790979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369116314371443971721305 2526837235778582978790979)
                ·
                  refine ⟨3790255853667874468186469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526837235778582978790979 3790255853667874468186469)
                  ·
                    refine ⟨710672972562726462784963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790255853667874468186469 710672972562726462784963)
                    ·
                      rfl

theorem cell22_2076046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2076046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076046 prefixEnd_2076046 := by exact prefixLift 2076046
  have htrace : WordTrace (prefixWord ++ tailWord_2076046) baseStart_2076046 baseEnd_2076046 := by
    simpa [prefixWord, tailWord_2076046, baseEnd_2076046] using wordTrace_append hprefix tailTrace_2076046
  have hstable : (prefixWord ++ tailWord_2076046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076046).length < 2 ^ (prefixWord ++ tailWord_2076046).sum := by decide
  have hdescent : baseEnd_2076046 < baseStart_2076046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076061 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 4]
def baseStart_2076061 : Nat := 118140960795 + 2076061 * 2 ^ 59
def prefixEnd_2076061 : Nat := 4983230072969 + 3 ^ 40 * 2076061 * 2
def baseEnd_2076061 : Nat := 236892702456423807886639

theorem tailTrace_2076061 : CollatzResearch.WordTrace tailWord_2076061 prefixEnd_2076061 236892702456423807886639 := by
  unfold tailWord_2076061
  simp only [CollatzResearch.WordTrace]
  refine ⟨75720165331793034835708037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50480110221195356557138691 75720165331793034835708037)
  ·
    refine ⟨14197530999711194031695257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75720165331793034835708037 14197530999711194031695257)
    ·
      refine ⟨10648148249783395523771443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14197530999711194031695257 10648148249783395523771443)
      ·
        refine ⟨15972222374675093285657165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648148249783395523771443 15972222374675093285657165)
        ·
          refine ⟨5989583390503159982121437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15972222374675093285657165 5989583390503159982121437)
          ·
            refine ⟨2246093771438684993295539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5989583390503159982121437 2246093771438684993295539)
            ·
              refine ⟨3369140657158027489943309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246093771438684993295539 3369140657158027489943309)
              ·
                refine ⟨1263427746434260308728741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3369140657158027489943309 1263427746434260308728741)
                ·
                  refine ⟨236892702456423807886639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263427746434260308728741 236892702456423807886639)
                  ·
                    rfl

theorem cell22_2076061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_2076061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076061 prefixEnd_2076061 := by exact prefixLift 2076061
  have htrace : WordTrace (prefixWord ++ tailWord_2076061) baseStart_2076061 baseEnd_2076061 := by
    simpa [prefixWord, tailWord_2076061, baseEnd_2076061] using wordTrace_append hprefix tailTrace_2076061
  have hstable : (prefixWord ++ tailWord_2076061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076061).length < 2 ^ (prefixWord ++ tailWord_2076061).sum := by decide
  have hdescent : baseEnd_2076061 < baseStart_2076061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076138 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2076138 : Nat := 118140960795 + 2076138 * 2 ^ 59
def prefixEnd_2076138 : Nat := 4983230072969 + 3 ^ 40 * 2076138 * 2
def baseEnd_2076138 : Nat := 710704466042868889484681

theorem tailTrace_2076138 : CollatzResearch.WordTrace tailWord_2076138 prefixEnd_2076138 710704466042868889484681 := by
  unfold tailWord_2076138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930743438128519246565267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50481982501676051324174045 18930743438128519246565267)
  ·
    refine ⟨28396115157192778869847901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18930743438128519246565267 28396115157192778869847901)
    ·
      refine ⟨10648543183947292076192963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28396115157192778869847901 10648543183947292076192963)
      ·
        refine ⟨15972814775920938114289445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648543183947292076192963 15972814775920938114289445)
        ·
          refine ⟨2994902770485175896429271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15972814775920938114289445 2994902770485175896429271)
          ·
            refine ⟨4492354155727763844643907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994902770485175896429271 4492354155727763844643907)
            ·
              refine ⟨6738531233591645766965861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492354155727763844643907 6738531233591645766965861)
              ·
                refine ⟨1263474606298433581306099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6738531233591645766965861 1263474606298433581306099)
                ·
                  refine ⟨1895211909447650371959149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263474606298433581306099 1895211909447650371959149)
                  ·
                    refine ⟨710704466042868889484681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1895211909447650371959149 710704466042868889484681)
                    ·
                      rfl

theorem cell22_2076138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2076138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076138 prefixEnd_2076138 := by exact prefixLift 2076138
  have htrace : WordTrace (prefixWord ++ tailWord_2076138) baseStart_2076138 baseEnd_2076138 := by
    simpa [prefixWord, tailWord_2076138, baseEnd_2076138] using wordTrace_append hprefix tailTrace_2076138
  have hstable : (prefixWord ++ tailWord_2076138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076138).length < 2 ^ (prefixWord ++ tailWord_2076138).sum := by decide
  have hdescent : baseEnd_2076138 < baseStart_2076138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076149 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2076149 : Nat := 118140960795 + 2076149 * 2 ^ 59
def prefixEnd_2076149 : Nat := 4983230072969 + 3 ^ 40 * 2076149 * 2
def baseEnd_2076149 : Nat := 710708231567668527459647

theorem tailTrace_2076149 : CollatzResearch.WordTrace tailWord_2076149 prefixEnd_2076149 710708231567668527459647 := by
  unfold tailWord_2076149
  simp only [CollatzResearch.WordTrace]
  refine ⟨75723374955474225864911501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50482249970316150576607667 75723374955474225864911501)
  ·
    refine ⟨28396265608302834699341813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75723374955474225864911501 28396265608302834699341813)
    ·
      refine ⟨2662149900778390753063295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28396265608302834699341813 2662149900778390753063295)
      ·
        refine ⟨3993224851167586129594943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662149900778390753063295 3993224851167586129594943)
        ·
          refine ⟨5989837276751379194392415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993224851167586129594943 5989837276751379194392415)
          ·
            refine ⟨8984755915127068791588623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989837276751379194392415 8984755915127068791588623)
            ·
              refine ⟨13477133872690603187382935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984755915127068791588623 13477133872690603187382935)
              ·
                refine ⟨20215700809035904781074403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477133872690603187382935 20215700809035904781074403)
                ·
                  refine ⟨30323551213553857171611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20215700809035904781074403 30323551213553857171611605)
                  ·
                    refine ⟨710708231567668527459647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30323551213553857171611605 710708231567668527459647)
                    ·
                      rfl

theorem cell22_2076149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2076149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076149 prefixEnd_2076149 := by exact prefixLift 2076149
  have htrace : WordTrace (prefixWord ++ tailWord_2076149) baseStart_2076149 baseEnd_2076149 := by
    simpa [prefixWord, tailWord_2076149, baseEnd_2076149] using wordTrace_append hprefix tailTrace_2076149
  have hstable : (prefixWord ++ tailWord_2076149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076149).length < 2 ^ (prefixWord ++ tailWord_2076149).sum := by decide
  have hdescent : baseEnd_2076149 < baseStart_2076149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076177 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2076177 : Nat := 118140960795 + 2076177 * 2 ^ 59
def prefixEnd_2076177 : Nat := 4983230072969 + 3 ^ 40 * 2076177 * 2
def baseEnd_2076177 : Nat := 710717816539885787759561

theorem tailTrace_2076177 : CollatzResearch.WordTrace tailWord_2076177 prefixEnd_2076177 710717816539885787759561 := by
  unfold tailWord_2076177
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724396199372786646930785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50482930799581857764620523 75724396199372786646930785)
  ·
    refine ⟨56793297149529589985198089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75724396199372786646930785 56793297149529589985198089)
    ·
      refine ⟨42594972862147192488898567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56793297149529589985198089 42594972862147192488898567)
      ·
        refine ⟨63892459293220788733347851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42594972862147192488898567 63892459293220788733347851)
        ·
          refine ⟨95838688939831183100021777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63892459293220788733347851 95838688939831183100021777)
          ·
            refine ⟨71879016704873387325016333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95838688939831183100021777 71879016704873387325016333)
            ·
              refine ⟨26954631264327520246881125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71879016704873387325016333 26954631264327520246881125)
              ·
                refine ⟨5053993362061410046290211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26954631264327520246881125 5053993362061410046290211)
                ·
                  refine ⟨7580990043092115069435317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053993362061410046290211 7580990043092115069435317)
                  ·
                    refine ⟨710717816539885787759561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7580990043092115069435317 710717816539885787759561)
                    ·
                      rfl

theorem cell22_2076177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2076177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076177 prefixEnd_2076177 := by exact prefixLift 2076177
  have htrace : WordTrace (prefixWord ++ tailWord_2076177) baseStart_2076177 baseEnd_2076177 := by
    simpa [prefixWord, tailWord_2076177, baseEnd_2076177] using wordTrace_append hprefix tailTrace_2076177
  have hstable : (prefixWord ++ tailWord_2076177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076177).length < 2 ^ (prefixWord ++ tailWord_2076177).sum := by decide
  have hdescent : baseEnd_2076177 < baseStart_2076177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076179 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 4]
def baseStart_2076179 : Nat := 118140960795 + 2076179 * 2 ^ 59
def prefixEnd_2076179 : Nat := 4983230072969 + 3 ^ 40 * 2076179 * 2
def baseEnd_2076179 : Nat := 236906167060252816403185

theorem tailTrace_2076179 : CollatzResearch.WordTrace tailWord_2076179 prefixEnd_2076179 236906167060252816403185 := by
  unfold tailWord_2076179
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724469145365540988503591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50482979430243693992335727 75724469145365540988503591)
  ·
    refine ⟨113586703718048311482755387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75724469145365540988503591 113586703718048311482755387)
    ·
      refine ⟨170380055577072467224133081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113586703718048311482755387 170380055577072467224133081)
      ·
        refine ⟨127785041682804350418099811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170380055577072467224133081 127785041682804350418099811)
        ·
          refine ⟨191677562524206525627149717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127785041682804350418099811 191677562524206525627149717)
          ·
            refine ⟨8984885743322180888772643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191677562524206525627149717 8984885743322180888772643)
            ·
              refine ⟨13477328614983271333158965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984885743322180888772643 13477328614983271333158965)
              ·
                refine ⟨1263499557654681687483653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13477328614983271333158965 1263499557654681687483653)
                ·
                  refine ⟨236906167060252816403185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263499557654681687483653 236906167060252816403185)
                  ·
                    rfl

theorem cell22_2076179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 4].length) (baseStart_2076179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076179 prefixEnd_2076179 := by exact prefixLift 2076179
  have htrace : WordTrace (prefixWord ++ tailWord_2076179) baseStart_2076179 baseEnd_2076179 := by
    simpa [prefixWord, tailWord_2076179, baseEnd_2076179] using wordTrace_append hprefix tailTrace_2076179
  have hstable : (prefixWord ++ tailWord_2076179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076179).length < 2 ^ (prefixWord ++ tailWord_2076179).sum := by decide
  have hdescent : baseEnd_2076179 < baseStart_2076179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076181 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2076181 : Nat := 118140960795 + 2076181 * 2 ^ 59
def prefixEnd_2076181 : Nat := 4983230072969 + 3 ^ 40 * 2076181 * 2
def baseEnd_2076181 : Nat := 710719185821631110659549

theorem tailTrace_2076181 : CollatzResearch.WordTrace tailWord_2076181 prefixEnd_2076181 710719185821631110659549 := by
  unfold tailWord_2076181
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724542091358295330076397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50483028060905530220050931 75724542091358295330076397)
  ·
    refine ⟨28396703284259360748778649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75724542091358295330076397 28396703284259360748778649)
    ·
      refine ⟨21297527463194520561583987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28396703284259360748778649 21297527463194520561583987)
      ·
        refine ⟨31946291194791780842375981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21297527463194520561583987 31946291194791780842375981)
        ·
          refine ⟨11979859198046917815890993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31946291194791780842375981 11979859198046917815890993)
          ·
            refine ⟨8984894398535188361918245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11979859198046917815890993 8984894398535188361918245)
            ·
              refine ⟨1684667699725347817859671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8984894398535188361918245 1684667699725347817859671)
              ·
                refine ⟨2527001549588021726789507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684667699725347817859671 2527001549588021726789507)
                ·
                  refine ⟨3790502324382032590184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527001549588021726789507 3790502324382032590184261)
                  ·
                    refine ⟨710719185821631110659549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790502324382032590184261 710719185821631110659549)
                    ·
                      rfl

theorem cell22_2076181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2076181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076181 prefixEnd_2076181 := by exact prefixLift 2076181
  have htrace : WordTrace (prefixWord ++ tailWord_2076181) baseStart_2076181 baseEnd_2076181 := by
    simpa [prefixWord, tailWord_2076181, baseEnd_2076181] using wordTrace_append hprefix tailTrace_2076181
  have hstable : (prefixWord ++ tailWord_2076181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076181).length < 2 ^ (prefixWord ++ tailWord_2076181).sum := by decide
  have hdescent : baseEnd_2076181 < baseStart_2076181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076267 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_2076267 : Nat := 118140960795 + 2076267 * 2 ^ 59
def prefixEnd_2076267 : Nat := 4983230072969 + 3 ^ 40 * 2076267 * 2
def baseEnd_2076267 : Nat := 710748625379155553009285

theorem tailTrace_2076267 : CollatzResearch.WordTrace tailWord_2076267 prefixEnd_2076267 710748625379155553009285 := by
  unfold tailWord_2076267
  simp only [CollatzResearch.WordTrace]
  refine ⟨75727678769046732017707055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50485119179364488011804703 75727678769046732017707055)
  ·
    refine ⟨113591518153570098026560583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75727678769046732017707055 113591518153570098026560583)
    ·
      refine ⟨170387277230355147039840875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113591518153570098026560583 170387277230355147039840875)
      ·
        refine ⟨255580915845532720559761313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170387277230355147039840875 255580915845532720559761313)
        ·
          refine ⟨191685686884149540419820985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255580915845532720559761313 191685686884149540419820985)
          ·
            refine ⟨143764265163112155314865739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191685686884149540419820985 143764265163112155314865739)
            ·
              refine ⟨215646397744668232972298609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143764265163112155314865739 215646397744668232972298609)
              ·
                refine ⟨161734798308501174729223957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215646397744668232972298609 161734798308501174729223957)
                ·
                  refine ⟨7581318670710992565432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161734798308501174729223957 7581318670710992565432373)
                  ·
                    refine ⟨710748625379155553009285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7581318670710992565432373 710748625379155553009285)
                    ·
                      rfl

theorem cell22_2076267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_2076267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076267 prefixEnd_2076267 := by exact prefixLift 2076267
  have htrace : WordTrace (prefixWord ++ tailWord_2076267) baseStart_2076267 baseEnd_2076267 := by
    simpa [prefixWord, tailWord_2076267, baseEnd_2076267] using wordTrace_append hprefix tailTrace_2076267
  have hstable : (prefixWord ++ tailWord_2076267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076267).length < 2 ^ (prefixWord ++ tailWord_2076267).sum := by decide
  have hdescent : baseEnd_2076267 < baseStart_2076267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076348 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_2076348 : Nat := 118140960795 + 2076348 * 2 ^ 59
def prefixEnd_2076348 : Nat := 4983230072969 + 3 ^ 40 * 2076348 * 2
def baseEnd_2076348 : Nat := 236925451111499447244679

theorem tailTrace_2076348 : CollatzResearch.WordTrace tailWord_2076348 prefixEnd_2076348 236925451111499447244679 := by
  unfold tailWord_2076348
  simp only [CollatzResearch.WordTrace]
  refine ⟨37865316540876641425702849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50487088721168855234270465 37865316540876641425702849)
  ·
    refine ⟨28398987405657481069277137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37865316540876641425702849 28398987405657481069277137)
    ·
      refine ⟨21299240554243110801957853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28398987405657481069277137 21299240554243110801957853)
      ·
        refine ⟨7987215207841166550734195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21299240554243110801957853 7987215207841166550734195)
        ·
          refine ⟨11980822811761749826101293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987215207841166550734195 11980822811761749826101293)
          ·
            refine ⟨4492808554410656184787985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11980822811761749826101293 4492808554410656184787985)
            ·
              refine ⟨3369606415807992138590989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492808554410656184787985 3369606415807992138590989)
              ·
                refine ⟨1263602405927997051971621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3369606415807992138590989 1263602405927997051971621)
                ·
                  refine ⟨236925451111499447244679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263602405927997051971621 236925451111499447244679)
                  ·
                    rfl

theorem cell22_2076348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_2076348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076348 prefixEnd_2076348 := by exact prefixLift 2076348
  have htrace : WordTrace (prefixWord ++ tailWord_2076348) baseStart_2076348 baseEnd_2076348 := by
    simpa [prefixWord, tailWord_2076348, baseEnd_2076348] using wordTrace_append hprefix tailTrace_2076348
  have hstable : (prefixWord ++ tailWord_2076348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076348).length < 2 ^ (prefixWord ++ tailWord_2076348).sum := by decide
  have hdescent : baseEnd_2076348 < baseStart_2076348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076350 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2076350 : Nat := 118140960795 + 2076350 * 2 ^ 59
def prefixEnd_2076350 : Nat := 4983230072969 + 3 ^ 40 * 2076350 * 2
def baseEnd_2076350 : Nat := 710777037975371003184031

theorem tailTrace_2076350 : CollatzResearch.WordTrace tailWord_2076350 prefixEnd_2076350 710777037975371003184031 := by
  unfold tailWord_2076350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466338253468254649122313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50487137351830691461985669 9466338253468254649122313)
  ·
    refine ⟨7099753690101190986841735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9466338253468254649122313 7099753690101190986841735)
    ·
      refine ⟨10649630535151786480262603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7099753690101190986841735 10649630535151786480262603)
      ·
        refine ⟨15974445802727679720393905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649630535151786480262603 15974445802727679720393905)
        ·
          refine ⟨11980834352045759790295429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974445802727679720393905 11980834352045759790295429)
          ·
            refine ⟨2246406441008579960680393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11980834352045759790295429 2246406441008579960680393)
            ·
              refine ⟨1684804830756434970510295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246406441008579960680393 1684804830756434970510295)
              ·
                refine ⟨2527207246134652455765443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684804830756434970510295 2527207246134652455765443)
                ·
                  refine ⟨3790810869201978683648165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527207246134652455765443 3790810869201978683648165)
                  ·
                    refine ⟨710777037975371003184031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790810869201978683648165 710777037975371003184031)
                    ·
                      rfl

theorem cell22_2076350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2076350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076350 prefixEnd_2076350 := by exact prefixLift 2076350
  have htrace : WordTrace (prefixWord ++ tailWord_2076350) baseStart_2076350 baseEnd_2076350 := by
    simpa [prefixWord, tailWord_2076350, baseEnd_2076350] using wordTrace_append hprefix tailTrace_2076350
  have hstable : (prefixWord ++ tailWord_2076350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076350).length < 2 ^ (prefixWord ++ tailWord_2076350).sum := by decide
  have hdescent : baseEnd_2076350 < baseStart_2076350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076354 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2076354 : Nat := 118140960795 + 2076354 * 2 ^ 59
def prefixEnd_2076354 : Nat := 4983230072969 + 3 ^ 40 * 2076354 * 2
def baseEnd_2076354 : Nat := 236926135752372108694673

theorem tailTrace_2076354 : CollatzResearch.WordTrace tailWord_2076354 prefixEnd_2076354 236926135752372108694673 := by
  unfold tailWord_2076354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932712979932886469031029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50487234613154363917416077 18932712979932886469031029)
  ·
    refine ⟨1774941841868708106471659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18932712979932886469031029 1774941841868708106471659)
    ·
      refine ⟨2662412762803062159707489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774941841868708106471659 2662412762803062159707489)
      ·
        refine ⟨1996809572102296619780617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662412762803062159707489 1996809572102296619780617)
        ·
          refine ⟨1497607179076722464835463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996809572102296619780617 1497607179076722464835463)
          ·
            refine ⟨2246410768615083697253195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497607179076722464835463 2246410768615083697253195)
            ·
              refine ⟨3369616152922625545879793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246410768615083697253195 3369616152922625545879793)
              ·
                refine ⟨2527212114691969159409845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369616152922625545879793 2527212114691969159409845)
                ·
                  refine ⟨236926135752372108694673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527212114691969159409845 236926135752372108694673)
                  ·
                    rfl

theorem cell22_2076354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2076354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076354 prefixEnd_2076354 := by exact prefixLift 2076354
  have htrace : WordTrace (prefixWord ++ tailWord_2076354) baseStart_2076354 baseEnd_2076354 := by
    simpa [prefixWord, tailWord_2076354, baseEnd_2076354] using wordTrace_append hprefix tailTrace_2076354
  have hstable : (prefixWord ++ tailWord_2076354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076354).length < 2 ^ (prefixWord ++ tailWord_2076354).sum := by decide
  have hdescent : baseEnd_2076354 < baseStart_2076354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076365 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2076365 : Nat := 118140960795 + 2076365 * 2 ^ 59
def prefixEnd_2076365 : Nat := 4983230072969 + 3 ^ 40 * 2076365 * 2
def baseEnd_2076365 : Nat := 236927390927305321352995

theorem tailTrace_2076365 : CollatzResearch.WordTrace tailWord_2076365 prefixEnd_2076365 236927390927305321352995 := by
  unfold tailWord_2076365
  simp only [CollatzResearch.WordTrace]
  refine ⟨75731253122691694754774549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50487502081794463169849699 75731253122691694754774549)
  ·
    refine ⟨3549902490126173191630057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75731253122691694754774549 3549902490126173191630057)
    ·
      refine ⟨2662426867594629893722543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549902490126173191630057 2662426867594629893722543)
      ·
        refine ⟨3993640301391944840583815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662426867594629893722543 3993640301391944840583815)
        ·
          refine ⟨5990460452087917260875723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993640301391944840583815 5990460452087917260875723)
          ·
            refine ⟨8985690678131875891313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990460452087917260875723 8985690678131875891313585)
            ·
              refine ⟨6739268008598906918485189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985690678131875891313585 6739268008598906918485189)
              ·
                refine ⟨1263612751612295047215973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6739268008598906918485189 1263612751612295047215973)
                ·
                  refine ⟨236927390927305321352995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263612751612295047215973 236927390927305321352995)
                  ·
                    rfl

theorem cell22_2076365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2076365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076365 prefixEnd_2076365 := by exact prefixLift 2076365
  have htrace : WordTrace (prefixWord ++ tailWord_2076365) baseStart_2076365 baseEnd_2076365 := by
    simpa [prefixWord, tailWord_2076365, baseEnd_2076365] using wordTrace_append hprefix tailTrace_2076365
  have hstable : (prefixWord ++ tailWord_2076365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076365).length < 2 ^ (prefixWord ++ tailWord_2076365).sum := by decide
  have hdescent : baseEnd_2076365 < baseStart_2076365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076380 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2076380 : Nat := 118140960795 + 2076380 * 2 ^ 59
def prefixEnd_2076380 : Nat := 4983230072969 + 3 ^ 40 * 2076380 * 2
def baseEnd_2076380 : Nat := 710787307588460924933939

theorem tailTrace_2076380 : CollatzResearch.WordTrace tailWord_2076380 prefixEnd_2076380 710787307588460924933939 := by
  unfold tailWord_2076380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37865900108818676158285297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50487866811758234877713729 37865900108818676158285297)
  ·
    refine ⟨28399425081614007118713973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37865900108818676158285297 28399425081614007118713973)
    ·
      refine ⟨2662446101401313167379435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28399425081614007118713973 2662446101401313167379435)
      ·
        refine ⟨3993669152101969751069153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662446101401313167379435 3993669152101969751069153)
        ·
          refine ⟨2995251864076477313301865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993669152101969751069153 2995251864076477313301865)
          ·
            refine ⟨2246438898057357984976399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995251864076477313301865 2246438898057357984976399)
            ·
              refine ⟨3369658347086036977464599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246438898057357984976399 3369658347086036977464599)
              ·
                refine ⟨5054487520629055466196899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369658347086036977464599 5054487520629055466196899)
                ·
                  refine ⟨7581731280943583199295349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054487520629055466196899 7581731280943583199295349)
                  ·
                    refine ⟨710787307588460924933939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7581731280943583199295349 710787307588460924933939)
                    ·
                      rfl

theorem cell22_2076380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2076380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076380 prefixEnd_2076380 := by exact prefixLift 2076380
  have htrace : WordTrace (prefixWord ++ tailWord_2076380) baseStart_2076380 baseEnd_2076380 := by
    simpa [prefixWord, tailWord_2076380, baseEnd_2076380] using wordTrace_append hprefix tailTrace_2076380
  have hstable : (prefixWord ++ tailWord_2076380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076380).length < 2 ^ (prefixWord ++ tailWord_2076380).sum := by decide
  have hdescent : baseEnd_2076380 < baseStart_2076380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076408 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_2076408 : Nat := 118140960795 + 2076408 * 2 ^ 59
def prefixEnd_2076408 : Nat := 4983230072969 + 3 ^ 40 * 2076408 * 2
def baseEnd_2076408 : Nat := 710796892560678185233853

theorem tailTrace_2076408 : CollatzResearch.WordTrace tailWord_2076408 prefixEnd_2076408 710796892560678185233853 := by
  unfold tailWord_2076408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866410730767956549294939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50488547641023942065726585 37866410730767956549294939)
  ·
    refine ⟨56799616096151934823942409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37866410730767956549294939 56799616096151934823942409)
    ·
      refine ⟨42599712072113951117956807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56799616096151934823942409 42599712072113951117956807)
      ·
        refine ⟨63899568108170926676935211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42599712072113951117956807 63899568108170926676935211)
        ·
          refine ⟨95849352162256390015402817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63899568108170926676935211 95849352162256390015402817)
          ·
            refine ⟨71887014121692292511552113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95849352162256390015402817 71887014121692292511552113)
            ·
              refine ⟨53915260591269219383664085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71887014121692292511552113 53915260591269219383664085)
              ·
                refine ⟨1263638920107872329304627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53915260591269219383664085 1263638920107872329304627)
                ·
                  refine ⟨1895458380161808493956941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263638920107872329304627 1895458380161808493956941)
                  ·
                    refine ⟨710796892560678185233853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1895458380161808493956941 710796892560678185233853)
                    ·
                      rfl

theorem cell22_2076408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_2076408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076408 prefixEnd_2076408 := by exact prefixLift 2076408
  have htrace : WordTrace (prefixWord ++ tailWord_2076408) baseStart_2076408 baseEnd_2076408 := by
    simpa [prefixWord, tailWord_2076408, baseEnd_2076408] using wordTrace_append hprefix tailTrace_2076408
  have hstable : (prefixWord ++ tailWord_2076408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076408).length < 2 ^ (prefixWord ++ tailWord_2076408).sum := by decide
  have hdescent : baseEnd_2076408 < baseStart_2076408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076419 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_2076419 : Nat := 118140960795 + 2076419 * 2 ^ 59
def prefixEnd_2076419 : Nat := 4983230072969 + 3 ^ 40 * 2076419 * 2
def baseEnd_2076419 : Nat := 710800658085477823208819

theorem tailTrace_2076419 : CollatzResearch.WordTrace tailWord_2076419 prefixEnd_2076419 710800658085477823208819 := by
  unfold tailWord_2076419
  simp only [CollatzResearch.WordTrace]
  refine ⟨75733222664496061977240311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50488815109664041318160207 75733222664496061977240311)
  ·
    refine ⟨113599833996744092965860467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75733222664496061977240311 113599833996744092965860467)
    ·
      refine ⟨170399750995116139448790701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113599833996744092965860467 170399750995116139448790701)
      ·
        refine ⟨63899906623168552293296513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170399750995116139448790701 63899906623168552293296513)
        ·
          refine ⟨47924929967376414219972385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63899906623168552293296513 47924929967376414219972385)
          ·
            refine ⟨35943697475532310664979289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47924929967376414219972385 35943697475532310664979289)
            ·
              refine ⟨26957773106649232998734467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35943697475532310664979289 26957773106649232998734467)
              ·
                refine ⟨40436659659973849498101701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26957773106649232998734467 40436659659973849498101701)
                ·
                  refine ⟨7581873686245096780894069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40436659659973849498101701 7581873686245096780894069)
                  ·
                    refine ⟨710800658085477823208819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7581873686245096780894069 710800658085477823208819)
                    ·
                      rfl

theorem cell22_2076419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_2076419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076419 prefixEnd_2076419 := by exact prefixLift 2076419
  have htrace : WordTrace (prefixWord ++ tailWord_2076419) baseStart_2076419 baseEnd_2076419 := by
    simpa [prefixWord, tailWord_2076419, baseEnd_2076419] using wordTrace_append hprefix tailTrace_2076419
  have hstable : (prefixWord ++ tailWord_2076419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076419).length < 2 ^ (prefixWord ++ tailWord_2076419).sum := by decide
  have hdescent : baseEnd_2076419 < baseStart_2076419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076483 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 4]
def baseStart_2076483 : Nat := 118140960795 + 2076483 * 2 ^ 59
def prefixEnd_2076483 : Nat := 4983230072969 + 3 ^ 40 * 2076483 * 2
def baseEnd_2076483 : Nat := 236940855531134329869541

theorem tailTrace_2076483 : CollatzResearch.WordTrace tailWord_2076483 prefixEnd_2076483 236940855531134329869541 := by
  unfold tailWord_2076483
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735556936264200907570103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50490371290842800605046735 75735556936264200907570103)
  ·
    refine ⟨113603335404396301361355155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75735556936264200907570103 113603335404396301361355155)
    ·
      refine ⟨170405003106594452042032733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113603335404396301361355155 170405003106594452042032733)
      ·
        refine ⟨63901876164972919515762275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170405003106594452042032733 63901876164972919515762275)
        ·
          refine ⟨95852814247459379273643413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63901876164972919515762275 95852814247459379273643413)
          ·
            refine ⟨4493100667849658403452035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95852814247459379273643413 4493100667849658403452035)
            ·
              refine ⟨6739651001774487605178053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493100667849658403452035 6739651001774487605178053)
              ·
                refine ⟨1263684562832716425970885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6739651001774487605178053 1263684562832716425970885)
                ·
                  refine ⟨236940855531134329869541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263684562832716425970885 236940855531134329869541)
                  ·
                    rfl

theorem cell22_2076483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 4].length) (baseStart_2076483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076483 prefixEnd_2076483 := by exact prefixLift 2076483
  have htrace : WordTrace (prefixWord ++ tailWord_2076483) baseStart_2076483 baseEnd_2076483 := by
    simpa [prefixWord, tailWord_2076483, baseEnd_2076483] using wordTrace_append hprefix tailTrace_2076483
  have hstable : (prefixWord ++ tailWord_2076483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076483).length < 2 ^ (prefixWord ++ tailWord_2076483).sum := by decide
  have hdescent : baseEnd_2076483 < baseStart_2076483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076498 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2076498 : Nat := 118140960795 + 2076498 * 2 ^ 59
def prefixEnd_2076498 : Nat := 4983230072969 + 3 ^ 40 * 2076498 * 2
def baseEnd_2076498 : Nat := 710827701399947950483577

theorem tailTrace_2076498 : CollatzResearch.WordTrace tailWord_2076498 prefixEnd_2076498 710827701399947950483577 := by
  unfold tailWord_2076498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934026007802464617341537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50490736020806572312910765 18934026007802464617341537)
  ·
    refine ⟨14200519505851848463006153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18934026007802464617341537 14200519505851848463006153)
    ·
      refine ⟨10650389629388886347254615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14200519505851848463006153 10650389629388886347254615)
      ·
        refine ⟨15975584444083329520881923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650389629388886347254615 15975584444083329520881923)
        ·
          refine ⟨23963376666124994281322885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975584444083329520881923 23963376666124994281322885)
          ·
            refine ⟨4493133124898436427748041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23963376666124994281322885 4493133124898436427748041)
            ·
              refine ⟨3369849843673827320811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493133124898436427748041 3369849843673827320811031)
              ·
                refine ⟨5054774765510740981216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369849843673827320811031 5054774765510740981216547)
                ·
                  refine ⟨7582162148266111471824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054774765510740981216547 7582162148266111471824821)
                  ·
                    refine ⟨710827701399947950483577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7582162148266111471824821 710827701399947950483577)
                    ·
                      rfl

theorem cell22_2076498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2076498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076498 prefixEnd_2076498 := by exact prefixLift 2076498
  have htrace : WordTrace (prefixWord ++ tailWord_2076498) baseStart_2076498 baseEnd_2076498 := by
    simpa [prefixWord, tailWord_2076498, baseEnd_2076498] using wordTrace_append hprefix tailTrace_2076498
  have hstable : (prefixWord ++ tailWord_2076498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076498).length < 2 ^ (prefixWord ++ tailWord_2076498).sum := by decide
  have hdescent : baseEnd_2076498 < baseStart_2076498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076620 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_2076620 : Nat := 118140960795 + 2076620 * 2 ^ 59
def prefixEnd_2076620 : Nat := 4983230072969 + 3 ^ 40 * 2076620 * 2
def baseEnd_2076620 : Nat := 710869464493180298933203

theorem tailTrace_2076620 : CollatzResearch.WordTrace tailWord_2076620 prefixEnd_2076620 710869464493180298933203 := by
  unfold tailWord_2076620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37870276868383936652653657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50493702491178582203538209 37870276868383936652653657)
  ·
    refine ⟨28402707651287952489490243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37870276868383936652653657 28402707651287952489490243)
    ·
      refine ⟨42604061476931928734235365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28402707651287952489490243 42604061476931928734235365)
      ·
        refine ⟨7988261526924736637669131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42604061476931928734235365 7988261526924736637669131)
        ·
          refine ⟨11982392290387104956503697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988261526924736637669131 11982392290387104956503697)
          ·
            refine ⟨8986794217790328717377773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11982392290387104956503697 8986794217790328717377773)
            ·
              refine ⟨3370047831671373269016665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8986794217790328717377773 3370047831671373269016665)
              ·
                refine ⟨2527535873753529951762499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370047831671373269016665 2527535873753529951762499)
                ·
                  refine ⟨3791303810630294927643749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527535873753529951762499 3791303810630294927643749)
                  ·
                    refine ⟨710869464493180298933203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791303810630294927643749 710869464493180298933203)
                    ·
                      rfl

theorem cell22_2076620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_2076620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076620 prefixEnd_2076620 := by exact prefixLift 2076620
  have htrace : WordTrace (prefixWord ++ tailWord_2076620) baseStart_2076620 baseEnd_2076620 := by
    simpa [prefixWord, tailWord_2076620, baseEnd_2076620] using wordTrace_append hprefix tailTrace_2076620
  have hstable : (prefixWord ++ tailWord_2076620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076620).length < 2 ^ (prefixWord ++ tailWord_2076620).sum := by decide
  have hdescent : baseEnd_2076620 < baseStart_2076620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076682 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_2076682 : Nat := 118140960795 + 2076682 * 2 ^ 59
def prefixEnd_2076682 : Nat := 4983230072969 + 3 ^ 40 * 2076682 * 2
def baseEnd_2076682 : Nat := 710890688360232803883013

theorem tailTrace_2076682 : CollatzResearch.WordTrace tailWord_2076682 prefixEnd_2076682 710890688360232803883013 := by
  unfold tailWord_2076682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935703765635814473516075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50495210041695505262709533 18935703765635814473516075)
  ·
    refine ⟨28403555648453721710274113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18935703765635814473516075 28403555648453721710274113)
    ·
      refine ⟨21302666736340291282705585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28403555648453721710274113 21302666736340291282705585)
      ·
        refine ⟨15977000052255218462029189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21302666736340291282705585 15977000052255218462029189)
        ·
          refine ⟨2995687509797853461630473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15977000052255218462029189 2995687509797853461630473)
          ·
            refine ⟨2246765632348390096222855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995687509797853461630473 2246765632348390096222855)
            ·
              refine ⟨3370148448522585144334283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246765632348390096222855 3370148448522585144334283)
              ·
                refine ⟨5055222672783877716501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370148448522585144334283 5055222672783877716501425)
                ·
                  refine ⟨3791417004587908287376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055222672783877716501425 3791417004587908287376069)
                  ·
                    refine ⟨710890688360232803883013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791417004587908287376069 710890688360232803883013)
                    ·
                      rfl

theorem cell22_2076682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_2076682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076682 prefixEnd_2076682 := by exact prefixLift 2076682
  have htrace : WordTrace (prefixWord ++ tailWord_2076682) baseStart_2076682 baseEnd_2076682 := by
    simpa [prefixWord, tailWord_2076682, baseEnd_2076682] using wordTrace_append hprefix tailTrace_2076682
  have hstable : (prefixWord ++ tailWord_2076682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076682).length < 2 ^ (prefixWord ++ tailWord_2076682).sum := by decide
  have hdescent : baseEnd_2076682 < baseStart_2076682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076723 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_2076723 : Nat := 118140960795 + 2076723 * 2 ^ 59
def prefixEnd_2076723 : Nat := 4983230072969 + 3 ^ 40 * 2076723 * 2
def baseEnd_2076723 : Nat := 710904723498122363607887

theorem tailTrace_2076723 : CollatzResearch.WordTrace tailWord_2076723 prefixEnd_2076723 710904723498122363607887 := by
  unfold tailWord_2076723
  simp only [CollatzResearch.WordTrace]
  refine ⟨75744310455394721896306823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50496206970263147930871215 75744310455394721896306823)
  ·
    refine ⟨113616465683092082844460235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75744310455394721896306823 113616465683092082844460235)
    ·
      refine ⟨170424698524638124266690353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113616465683092082844460235 170424698524638124266690353)
      ·
        refine ⟨127818523893478593200017765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170424698524638124266690353 127818523893478593200017765)
        ·
          refine ⟨23965973230027236225003331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127818523893478593200017765 23965973230027236225003331)
          ·
            refine ⟨35948959845040854337504997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23965973230027236225003331 35948959845040854337504997)
            ·
              refine ⟨6740429970945160188282187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35948959845040854337504997 6740429970945160188282187)
              ·
                refine ⟨10110644956417740282423281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740429970945160188282187 10110644956417740282423281)
                ·
                  refine ⟨7582983717313305211817461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10110644956417740282423281 7582983717313305211817461)
                  ·
                    refine ⟨710904723498122363607887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7582983717313305211817461 710904723498122363607887)
                    ·
                      rfl

theorem cell22_2076723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_2076723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076723 prefixEnd_2076723 := by exact prefixLift 2076723
  have htrace : WordTrace (prefixWord ++ tailWord_2076723) baseStart_2076723 baseEnd_2076723 := by
    simpa [prefixWord, tailWord_2076723, baseEnd_2076723] using wordTrace_append hprefix tailTrace_2076723
  have hstable : (prefixWord ++ tailWord_2076723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076723).length < 2 ^ (prefixWord ++ tailWord_2076723).sum := by decide
  have hdescent : baseEnd_2076723 < baseStart_2076723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076864 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_2076864 : Nat := 118140960795 + 2076864 * 2 ^ 59
def prefixEnd_2076864 : Nat := 4983230072969 + 3 ^ 40 * 2076864 * 2
def baseEnd_2076864 : Nat := 710952990679644995832455

theorem tailTrace_2076864 : CollatzResearch.WordTrace tailWord_2076864 prefixEnd_2076864 710952990679644995832455 := by
  unfold tailWord_2076864
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874726573941951488594823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50499635431922601984793097 37874726573941951488594823)
  ·
    refine ⟨56812089860912927232892235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37874726573941951488594823 56812089860912927232892235)
    ·
      refine ⟨85218134791369390849338353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56812089860912927232892235 85218134791369390849338353)
      ·
        refine ⟨63913601093527043137003765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85218134791369390849338353 63913601093527043137003765)
        ·
          refine ⟨5991900102518160294094103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63913601093527043137003765 5991900102518160294094103)
          ·
            refine ⟨8987850153777240441141155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991900102518160294094103 8987850153777240441141155)
            ·
              refine ⟨13481775230665860661711733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987850153777240441141155 13481775230665860661711733)
              ·
                refine ⟨1263916427874924437035475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13481775230665860661711733 1263916427874924437035475)
                ·
                  refine ⟨1895874641812386655553213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263916427874924437035475 1895874641812386655553213)
                  ·
                    refine ⟨710952990679644995832455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1895874641812386655553213 710952990679644995832455)
                    ·
                      rfl

theorem cell22_2076864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_2076864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076864 prefixEnd_2076864 := by exact prefixLift 2076864
  have htrace : WordTrace (prefixWord ++ tailWord_2076864) baseStart_2076864 baseEnd_2076864 := by
    simpa [prefixWord, tailWord_2076864, baseEnd_2076864] using wordTrace_append hprefix tailTrace_2076864
  have hstable : (prefixWord ++ tailWord_2076864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076864).length < 2 ^ (prefixWord ++ tailWord_2076864).sum := by decide
  have hdescent : baseEnd_2076864 < baseStart_2076864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076890 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_2076890 : Nat := 118140960795 + 2076890 * 2 ^ 59
def prefixEnd_2076890 : Nat := 4983230072969 + 3 ^ 40 * 2076890 * 2
def baseEnd_2076890 : Nat := 710961891010989594682375

theorem tailTrace_2076890 : CollatzResearch.WordTrace tailWord_2076890 prefixEnd_2076890 710961891010989594682375 := by
  unfold tailWord_2076890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937600361447427354409031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50500267630526472945090749 18937600361447427354409031)
  ·
    refine ⟨28406400542171141031613547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18937600361447427354409031 28406400542171141031613547)
    ·
      refine ⟨42609600813256711547420321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28406400542171141031613547 42609600813256711547420321)
      ·
        refine ⟨31957200609942533660565241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42609600813256711547420321 31957200609942533660565241)
        ·
          refine ⟨23967900457456900245423931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31957200609942533660565241 23967900457456900245423931)
          ·
            refine ⟨35951850686185350368135897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23967900457456900245423931 35951850686185350368135897)
            ·
              refine ⟨26963888014639012776101923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35951850686185350368135897 26963888014639012776101923)
              ·
                refine ⟨40445832021958519164152885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26963888014639012776101923 40445832021958519164152885)
                ·
                  refine ⟨3791796752058611171639333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40445832021958519164152885 3791796752058611171639333)
                  ·
                    refine ⟨710961891010989594682375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791796752058611171639333 710961891010989594682375)
                    ·
                      rfl

theorem cell22_2076890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_2076890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076890 prefixEnd_2076890 := by exact prefixLift 2076890
  have htrace : WordTrace (prefixWord ++ tailWord_2076890) baseStart_2076890 baseEnd_2076890 := by
    simpa [prefixWord, tailWord_2076890, baseEnd_2076890] using wordTrace_append hprefix tailTrace_2076890
  have hstable : (prefixWord ++ tailWord_2076890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076890).length < 2 ^ (prefixWord ++ tailWord_2076890).sum := by decide
  have hdescent : baseEnd_2076890 < baseStart_2076890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076907 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 1, 4]
def baseStart_2076907 : Nat := 118140960795 + 2076907 * 2 ^ 59
def prefixEnd_2076907 : Nat := 4983230072969 + 3 ^ 40 * 2076907 * 2
def baseEnd_2076907 : Nat := 710967710458407217007323

theorem tailTrace_2076907 : CollatzResearch.WordTrace tailWord_2076907 prefixEnd_2076907 710967710458407217007323 := by
  unfold tailWord_2076907
  simp only [CollatzResearch.WordTrace]
  refine ⟨75751021486728121321004975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50500680991152080880669983 75751021486728121321004975)
  ·
    refine ⟨113626532230092181981507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75751021486728121321004975 113626532230092181981507463)
    ·
      refine ⟨170439798345138272972261195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113626532230092181981507463 170439798345138272972261195)
      ·
        refine ⟨255659697517707409458391793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170439798345138272972261195 255659697517707409458391793)
        ·
          refine ⟨191744773138280557093793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255659697517707409458391793 191744773138280557093793845)
          ·
            refine ⟨17976072481713802227543173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191744773138280557093793845 17976072481713802227543173)
            ·
              refine ⟨3370513590321337917664345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17976072481713802227543173 3370513590321337917664345)
              ·
                refine ⟨2527885192741003438248259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370513590321337917664345 2527885192741003438248259)
                ·
                  refine ⟨3791827789111505157372389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527885192741003438248259 3791827789111505157372389)
                  ·
                    refine ⟨710967710458407217007323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791827789111505157372389 710967710458407217007323)
                    ·
                      rfl

theorem cell22_2076907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_2076907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076907 prefixEnd_2076907 := by exact prefixLift 2076907
  have htrace : WordTrace (prefixWord ++ tailWord_2076907) baseStart_2076907 baseEnd_2076907 := by
    simpa [prefixWord, tailWord_2076907, baseEnd_2076907] using wordTrace_append hprefix tailTrace_2076907
  have hstable : (prefixWord ++ tailWord_2076907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076907).length < 2 ^ (prefixWord ++ tailWord_2076907).sum := by decide
  have hdescent : baseEnd_2076907 < baseStart_2076907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076920 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_2076920 : Nat := 118140960795 + 2076920 * 2 ^ 59
def prefixEnd_2076920 : Nat := 4983230072969 + 3 ^ 40 * 2076920 * 2
def baseEnd_2076920 : Nat := 710972160624079516432283

theorem tailTrace_2076920 : CollatzResearch.WordTrace tailWord_2076920 prefixEnd_2076920 710972160624079516432283 := by
  unfold tailWord_2076920
  simp only [CollatzResearch.WordTrace]
  refine ⟨37875747817840512270614107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50500997090454016360818809 37875747817840512270614107)
  ·
    refine ⟨56813621726760768405921161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37875747817840512270614107 56813621726760768405921161)
    ·
      refine ⟨42610216295070576304440871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56813621726760768405921161 42610216295070576304440871)
      ·
        refine ⟨63915324442605864456661307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42610216295070576304440871 63915324442605864456661307)
        ·
          refine ⟨95872986663908796684991961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63915324442605864456661307 95872986663908796684991961)
          ·
            refine ⟨71904739997931597513743971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95872986663908796684991961 71904739997931597513743971)
            ·
              refine ⟨107857109996897396270615957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71904739997931597513743971 107857109996897396270615957)
              ·
                refine ⟨5055802031104565450185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107857109996897396270615957 5055802031104565450185123)
                ·
                  refine ⟨7583703046656848175277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055802031104565450185123 7583703046656848175277685)
                  ·
                    refine ⟨710972160624079516432283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7583703046656848175277685 710972160624079516432283)
                    ·
                      rfl

theorem cell22_2076920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_2076920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076920 prefixEnd_2076920 := by exact prefixLift 2076920
  have htrace : WordTrace (prefixWord ++ tailWord_2076920) baseStart_2076920 baseEnd_2076920 := by
    simpa [prefixWord, tailWord_2076920, baseEnd_2076920] using wordTrace_append hprefix tailTrace_2076920
  have hstable : (prefixWord ++ tailWord_2076920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076920).length < 2 ^ (prefixWord ++ tailWord_2076920).sum := by decide
  have hdescent : baseEnd_2076920 < baseStart_2076920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076937 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_2076937 : Nat := 118140960795 + 2076937 * 2 ^ 59
def prefixEnd_2076937 : Nat := 4983230072969 + 3 ^ 40 * 2076937 * 2
def baseEnd_2076937 : Nat := 710977980071497138757231

theorem tailTrace_2076937 : CollatzResearch.WordTrace tailWord_2076937 prefixEnd_2076937 710977980071497138757231 := by
  unfold tailWord_2076937
  simp only [CollatzResearch.WordTrace]
  refine ⟨75752115676619436444597065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50501410451079624296398043 75752115676619436444597065)
  ·
    refine ⟨56814086757464577333447799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75752115676619436444597065 56814086757464577333447799)
    ·
      refine ⟨85221130136196866000171699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56814086757464577333447799 85221130136196866000171699)
      ·
        refine ⟨127831695204295299000257549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85221130136196866000171699 127831695204295299000257549)
        ·
          refine ⟨47936885701610737125096581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127831695204295299000257549 47936885701610737125096581)
          ·
            refine ⟨8988166069052013210955609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47936885701610737125096581 8988166069052013210955609)
            ·
              refine ⟨6741124551789009908216707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8988166069052013210955609 6741124551789009908216707)
              ·
                refine ⟨10111686827683514862325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741124551789009908216707 10111686827683514862325061)
                ·
                  refine ⟨1895941280190659036685949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10111686827683514862325061 1895941280190659036685949)
                  ·
                    refine ⟨710977980071497138757231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1895941280190659036685949 710977980071497138757231)
                    ·
                      rfl

theorem cell22_2076937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_2076937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076937 prefixEnd_2076937 := by exact prefixLift 2076937
  have htrace : WordTrace (prefixWord ++ tailWord_2076937) baseStart_2076937 baseEnd_2076937 := by
    simpa [prefixWord, tailWord_2076937, baseEnd_2076937] using wordTrace_append hprefix tailTrace_2076937
  have hstable : (prefixWord ++ tailWord_2076937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076937).length < 2 ^ (prefixWord ++ tailWord_2076937).sum := by decide
  have hdescent : baseEnd_2076937 < baseStart_2076937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076939 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 4]
def baseStart_2076939 : Nat := 118140960795 + 2076939 * 2 ^ 59
def prefixEnd_2076939 : Nat := 4983230072969 + 3 ^ 40 * 2076939 * 2
def baseEnd_2076939 : Nat := 236992888237456600069075

theorem tailTrace_2076939 : CollatzResearch.WordTrace tailWord_2076939 prefixEnd_2076939 236992888237456600069075 := by
  unfold tailWord_2076939
  simp only [CollatzResearch.WordTrace]
  refine ⟨75752188622612190786169871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50501459081741460524113247 75752188622612190786169871)
  ·
    refine ⟨113628282933918286179254807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75752188622612190786169871 113628282933918286179254807)
    ·
      refine ⟨170442424400877429268882211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113628282933918286179254807 170442424400877429268882211)
      ·
        refine ⟨255663636601316143903323317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170442424400877429268882211 255663636601316143903323317)
        ·
          refine ⟨23968465931373388490936561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255663636601316143903323317 23968465931373388490936561)
          ·
            refine ⟨17976349448530041368202421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23968465931373388490936561 17976349448530041368202421)
            ·
              refine ⟨1685282760799691378268977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17976349448530041368202421 1685282760799691378268977)
              ·
                refine ⟨1263962070599768533701733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685282760799691378268977 1263962070599768533701733)
                ·
                  refine ⟨236992888237456600069075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263962070599768533701733 236992888237456600069075)
                  ·
                    rfl

theorem cell22_2076939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 4].length) (baseStart_2076939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076939 prefixEnd_2076939 := by exact prefixLift 2076939
  have htrace : WordTrace (prefixWord ++ tailWord_2076939) baseStart_2076939 baseEnd_2076939 := by
    simpa [prefixWord, tailWord_2076939, baseEnd_2076939] using wordTrace_append hprefix tailTrace_2076939
  have hstable : (prefixWord ++ tailWord_2076939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076939).length < 2 ^ (prefixWord ++ tailWord_2076939).sum := by decide
  have hdescent : baseEnd_2076939 < baseStart_2076939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076958 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2076958 : Nat := 118140960795 + 2076958 * 2 ^ 59
def prefixEnd_2076958 : Nat := 4983230072969 + 3 ^ 40 * 2076958 * 2
def baseEnd_2076958 : Nat := 710985168800660083982167

theorem tailTrace_2076958 : CollatzResearch.WordTrace tailWord_2076958 prefixEnd_2076958 710985168800660083982167 := by
  unfold tailWord_2076958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469110201192919628888941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50501921073028904687407685 9469110201192919628888941)
  ·
    refine ⟨3550916325447344860833353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9469110201192919628888941 3550916325447344860833353)
    ·
      refine ⟨2663187244085508645625015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550916325447344860833353 2663187244085508645625015)
      ·
        refine ⟨3994780866128262968437523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663187244085508645625015 3994780866128262968437523)
        ·
          refine ⟨5992171299192394452656285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994780866128262968437523 5992171299192394452656285)
          ·
            refine ⟨2247064237197147919746107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5992171299192394452656285 2247064237197147919746107)
            ·
              refine ⟨3370596355795721879619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247064237197147919746107 3370596355795721879619161)
              ·
                refine ⟨2527947266846791409714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370596355795721879619161 2527947266846791409714371)
                ·
                  refine ⟨3791920900270187114571557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527947266846791409714371 3791920900270187114571557)
                  ·
                    refine ⟨710985168800660083982167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791920900270187114571557 710985168800660083982167)
                    ·
                      rfl

theorem cell22_2076958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2076958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076958 prefixEnd_2076958 := by exact prefixLift 2076958
  have htrace : WordTrace (prefixWord ++ tailWord_2076958) baseStart_2076958 baseEnd_2076958 := by
    simpa [prefixWord, tailWord_2076958, baseEnd_2076958] using wordTrace_append hprefix tailTrace_2076958
  have hstable : (prefixWord ++ tailWord_2076958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076958).length < 2 ^ (prefixWord ++ tailWord_2076958).sum := by decide
  have hdescent : baseEnd_2076958 < baseStart_2076958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076995 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 7]
def baseStart_2076995 : Nat := 118140960795 + 2076995 * 2 ^ 59
def prefixEnd_2076995 : Nat := 4983230072969 + 3 ^ 40 * 2076995 * 2
def baseEnd_2076995 : Nat := 236999278218934773602351

theorem tailTrace_2076995 : CollatzResearch.WordTrace tailWord_2076995 prefixEnd_2076995 236999278218934773602351 := by
  unfold tailWord_2076995
  simp only [CollatzResearch.WordTrace]
  refine ⟨75754231110409312350208439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50502820740272874900138959 75754231110409312350208439)
  ·
    refine ⟨113631346665613968525312659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75754231110409312350208439 113631346665613968525312659)
    ·
      refine ⟨170447019998420952787968989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113631346665613968525312659 170447019998420952787968989)
      ·
        refine ⟨63917632499407857295488371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170447019998420952787968989 63917632499407857295488371)
        ·
          refine ⟨95876448749111785943232557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63917632499407857295488371 95876448749111785943232557)
          ·
            refine ⟨35953668280916919728712209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95876448749111785943232557 35953668280916919728712209)
            ·
              refine ⟨26965251210687689796534157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35953668280916919728712209 26965251210687689796534157)
              ·
                refine ⟨10111969204007883673700309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26965251210687689796534157 10111969204007883673700309)
                ·
                  refine ⟨236999278218934773602351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10111969204007883673700309 236999278218934773602351)
                  ·
                    rfl

theorem cell22_2076995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_2076995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2076995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2076995 prefixEnd_2076995 := by exact prefixLift 2076995
  have htrace : WordTrace (prefixWord ++ tailWord_2076995) baseStart_2076995 baseEnd_2076995 := by
    simpa [prefixWord, tailWord_2076995, baseEnd_2076995] using wordTrace_append hprefix tailTrace_2076995
  have hstable : (prefixWord ++ tailWord_2076995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076995).length < 2 ^ (prefixWord ++ tailWord_2076995).sum := by decide
  have hdescent : baseEnd_2076995 < baseStart_2076995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077046 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_2077046 : Nat := 118140960795 + 2077046 * 2 ^ 59
def prefixEnd_2077046 : Nat := 4983230072969 + 3 ^ 40 * 2077046 * 2
def baseEnd_2077046 : Nat := 237005097666352395927299

theorem tailTrace_2077046 : CollatzResearch.WordTrace tailWord_2077046 prefixEnd_2077046 237005097666352395927299 := by
  unfold tailWord_2077046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734755702076534253769687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50504060822149698706876661 4734755702076534253769687)
  ·
    refine ⟨7102133553114801380654531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4734755702076534253769687 7102133553114801380654531)
    ·
      refine ⟨10653200329672202070981797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102133553114801380654531 10653200329672202070981797)
      ·
        refine ⟨1997475061813537888309087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10653200329672202070981797 1997475061813537888309087)
        ·
          refine ⟨2996212592720306832463631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997475061813537888309087 2996212592720306832463631)
          ·
            refine ⟨4494318889080460248695447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996212592720306832463631 4494318889080460248695447)
            ·
              refine ⟨6741478333620690373043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494318889080460248695447 6741478333620690373043171)
              ·
                refine ⟨10112217500431035559564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741478333620690373043171 10112217500431035559564757)
                ·
                  refine ⟨237005097666352395927299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10112217500431035559564757 237005097666352395927299)
                  ·
                    rfl

theorem cell22_2077046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_2077046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077046 prefixEnd_2077046 := by exact prefixLift 2077046
  have htrace : WordTrace (prefixWord ++ tailWord_2077046) baseStart_2077046 baseEnd_2077046 := by
    simpa [prefixWord, tailWord_2077046, baseEnd_2077046] using wordTrace_append hprefix tailTrace_2077046
  have hstable : (prefixWord ++ tailWord_2077046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077046).length < 2 ^ (prefixWord ++ tailWord_2077046).sum := by decide
  have hdescent : baseEnd_2077046 < baseStart_2077046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077087 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_2077087 : Nat := 118140960795 + 2077087 * 2 ^ 59
def prefixEnd_2077087 : Nat := 4983230072969 + 3 ^ 40 * 2077087 * 2
def baseEnd_2077087 : Nat := 711029328136946747506771

theorem tailTrace_2077087 : CollatzResearch.WordTrace tailWord_2077087 prefixEnd_2077087 711029328136946747506771 := by
  unfold tailWord_2077087
  simp only [CollatzResearch.WordTrace]
  refine ⟨75757586626076012062557515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50505057750717341375038343 75757586626076012062557515)
  ·
    refine ⟨113636379939114018093836273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75757586626076012062557515 113636379939114018093836273)
    ·
      refine ⟨85227284954335513570377205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113636379939114018093836273 85227284954335513570377205)
      ·
        refine ⟨7990057964468954397222863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85227284954335513570377205 7990057964468954397222863)
        ·
          refine ⟨11985086946703431595834295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990057964468954397222863 11985086946703431595834295)
          ·
            refine ⟨17977630420055147393751443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985086946703431595834295 17977630420055147393751443)
            ·
              refine ⟨26966445630082721090627165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977630420055147393751443 26966445630082721090627165)
              ·
                refine ⟨10112417111281020408985187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26966445630082721090627165 10112417111281020408985187)
                ·
                  refine ⟨15168625666921530613477781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112417111281020408985187 15168625666921530613477781)
                  ·
                    refine ⟨711029328136946747506771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15168625666921530613477781 711029328136946747506771)
                    ·
                      rfl

theorem cell22_2077087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_2077087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077087 prefixEnd_2077087 := by exact prefixLift 2077087
  have htrace : WordTrace (prefixWord ++ tailWord_2077087) baseStart_2077087 baseEnd_2077087 := by
    simpa [prefixWord, tailWord_2077087, baseEnd_2077087] using wordTrace_append hprefix tailTrace_2077087
  have hstable : (prefixWord ++ tailWord_2077087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077087).length < 2 ^ (prefixWord ++ tailWord_2077087).sum := by decide
  have hdescent : baseEnd_2077087 < baseStart_2077087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077091 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 4]
def baseStart_2077091 : Nat := 118140960795 + 2077091 * 2 ^ 59
def prefixEnd_2077091 : Nat := 4983230072969 + 3 ^ 40 * 2077091 * 2
def baseEnd_2077091 : Nat := 237010232472897356802253

theorem tailTrace_2077091 : CollatzResearch.WordTrace tailWord_2077091 prefixEnd_2077091 237010232472897356802253 := by
  unfold tailWord_2077091
  simp only [CollatzResearch.WordTrace]
  refine ⟨75757732518061520745703127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50505155012041013830468751 75757732518061520745703127)
  ·
    refine ⟨113636598777092281118554691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75757732518061520745703127 113636598777092281118554691)
    ·
      refine ⟨170454898165638421677832037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113636598777092281118554691 170454898165638421677832037)
      ·
        refine ⟨31960293406057204064593507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170454898165638421677832037 31960293406057204064593507)
        ·
          refine ⟨47940440109085806096890261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31960293406057204064593507 47940440109085806096890261)
          ·
            refine ⟨2247208130113397160791731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47940440109085806096890261 2247208130113397160791731)
            ·
              refine ⟨3370812195170095741187597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247208130113397160791731 3370812195170095741187597)
              ·
                refine ⟨1264054573188785902945349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3370812195170095741187597 1264054573188785902945349)
                ·
                  refine ⟨237010232472897356802253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264054573188785902945349 237010232472897356802253)
                  ·
                    rfl

theorem cell22_2077091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 4].length) (baseStart_2077091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077091 prefixEnd_2077091 := by exact prefixLift 2077091
  have htrace : WordTrace (prefixWord ++ tailWord_2077091) baseStart_2077091 baseEnd_2077091 := by
    simpa [prefixWord, tailWord_2077091, baseEnd_2077091] using wordTrace_append hprefix tailTrace_2077091
  have hstable : (prefixWord ++ tailWord_2077091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077091).length < 2 ^ (prefixWord ++ tailWord_2077091).sum := by decide
  have hdescent : baseEnd_2077091 < baseStart_2077091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077134 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2077134 : Nat := 118140960795 + 2077134 * 2 ^ 59
def prefixEnd_2077134 : Nat := 4983230072969 + 3 ^ 40 * 2077134 * 2
def baseEnd_2077134 : Nat := 711045417197454291581627

theorem tailTrace_2077134 : CollatzResearch.WordTrace tailWord_2077134 prefixEnd_2077134 711045417197454291581627 := by
  unfold tailWord_2077134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469912607113217386189807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50506200571270492726345637 9469912607113217386189807)
  ·
    refine ⟨14204868910669826079284711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469912607113217386189807 14204868910669826079284711)
    ·
      refine ⟨21307303366004739118927067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204868910669826079284711 21307303366004739118927067)
      ·
        refine ⟨31960955049007108678390601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307303366004739118927067 31960955049007108678390601)
        ·
          refine ⟨23970716286755331508792951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31960955049007108678390601 23970716286755331508792951)
          ·
            refine ⟨35956074430132997263189427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23970716286755331508792951 35956074430132997263189427)
            ·
              refine ⟨53934111645199495894784141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35956074430132997263189427 53934111645199495894784141)
              ·
                refine ⟨20225291866949810960544053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53934111645199495894784141 20225291866949810960544053)
                ·
                  refine ⟨1896121112526544777551005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20225291866949810960544053 1896121112526544777551005)
                  ·
                    refine ⟨711045417197454291581627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896121112526544777551005 711045417197454291581627)
                    ·
                      rfl

theorem cell22_2077134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2077134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077134 prefixEnd_2077134 := by exact prefixLift 2077134
  have htrace : WordTrace (prefixWord ++ tailWord_2077134) baseStart_2077134 baseEnd_2077134 := by
    simpa [prefixWord, tailWord_2077134, baseEnd_2077134] using wordTrace_append hprefix tailTrace_2077134
  have hstable : (prefixWord ++ tailWord_2077134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077134).length < 2 ^ (prefixWord ++ tailWord_2077134).sum := by decide
  have hdescent : baseEnd_2077134 < baseStart_2077134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077138 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2077138 : Nat := 118140960795 + 2077138 * 2 ^ 59
def prefixEnd_2077138 : Nat := 4983230072969 + 3 ^ 40 * 2077138 * 2
def baseEnd_2077138 : Nat := 711046786479199614481615

theorem tailTrace_2077138 : CollatzResearch.WordTrace tailWord_2077138 prefixEnd_2077138 711046786479199614481615 := by
  unfold tailWord_2077138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939861687222811943166017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50506297832594165181776045 18939861687222811943166017)
  ·
    refine ⟨14204896265417108957374513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18939861687222811943166017 14204896265417108957374513)
    ·
      refine ⟨10653672199062831718030885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14204896265417108957374513 10653672199062831718030885)
      ·
        refine ⟨1997563537324280947130791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10653672199062831718030885 1997563537324280947130791)
        ·
          refine ⟨2996345305986421420696187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997563537324280947130791 2996345305986421420696187)
          ·
            refine ⟨4494517958979632131044281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996345305986421420696187 4494517958979632131044281)
            ·
              refine ⟨3370888469234724098283211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494517958979632131044281 3370888469234724098283211)
              ·
                refine ⟨5056332703852086147424817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370888469234724098283211 5056332703852086147424817)
                ·
                  refine ⟨3792249527889064610568613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056332703852086147424817 3792249527889064610568613)
                  ·
                    refine ⟨711046786479199614481615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792249527889064610568613 711046786479199614481615)
                    ·
                      rfl

theorem cell22_2077138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2077138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077138 prefixEnd_2077138 := by exact prefixLift 2077138
  have htrace : WordTrace (prefixWord ++ tailWord_2077138) baseStart_2077138 baseEnd_2077138 := by
    simpa [prefixWord, tailWord_2077138, baseEnd_2077138] using wordTrace_append hprefix tailTrace_2077138
  have hstable : (prefixWord ++ tailWord_2077138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077138).length < 2 ^ (prefixWord ++ tailWord_2077138).sum := by decide
  have hdescent : baseEnd_2077138 < baseStart_2077138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077164 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_2077164 : Nat := 118140960795 + 2077164 * 2 ^ 59
def prefixEnd_2077164 : Nat := 4983230072969 + 3 ^ 40 * 2077164 * 2
def baseEnd_2077164 : Nat := 237018562270181404443845

theorem tailTrace_2077164 : CollatzResearch.WordTrace tailWord_2077164 prefixEnd_2077164 237018562270181404443845 := by
  unfold tailWord_2077164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37880197523398527106555273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50506930031198036142073697 37880197523398527106555273)
  ·
    refine ⟨28410148142548895329916455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37880197523398527106555273 28410148142548895329916455)
    ·
      refine ⟨42615222213823342994874683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28410148142548895329916455 42615222213823342994874683)
      ·
        refine ⟨63922833320735014492312025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42615222213823342994874683 63922833320735014492312025)
        ·
          refine ⟨47942124990551260869234019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63922833320735014492312025 47942124990551260869234019)
          ·
            refine ⟨71913187485826891303851029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47942124990551260869234019 71913187485826891303851029)
            ·
              refine ⟨3370930663398135529868017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71913187485826891303851029 3370930663398135529868017)
              ·
                refine ⟨2528197997548601647401013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370930663398135529868017 2528197997548601647401013)
                ·
                  refine ⟨237018562270181404443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528197997548601647401013 237018562270181404443845)
                  ·
                    rfl

theorem cell22_2077164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_2077164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077164 prefixEnd_2077164 := by exact prefixLift 2077164
  have htrace : WordTrace (prefixWord ++ tailWord_2077164) baseStart_2077164 baseEnd_2077164 := by
    simpa [prefixWord, tailWord_2077164, baseEnd_2077164] using wordTrace_append hprefix tailTrace_2077164
  have hstable : (prefixWord ++ tailWord_2077164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077164).length < 2 ^ (prefixWord ++ tailWord_2077164).sum := by decide
  have hdescent : baseEnd_2077164 < baseStart_2077164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077194 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2077194 : Nat := 118140960795 + 2077194 * 2 ^ 59
def prefixEnd_2077194 : Nat := 4983230072969 + 3 ^ 40 * 2077194 * 2
def baseEnd_2077194 : Nat := 711065956423634135081443

theorem tailTrace_2077194 : CollatzResearch.WordTrace tailWord_2077194 prefixEnd_2077194 711065956423634135081443 := by
  unfold tailWord_2077194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940372309172092334175659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50507659491125579557801757 18940372309172092334175659)
  ·
    refine ⟨28410558463758138501263489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18940372309172092334175659 28410558463758138501263489)
    ·
      refine ⟨21307918847818603875947617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28410558463758138501263489 21307918847818603875947617)
      ·
        refine ⟨15980939135863952906960713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21307918847818603875947617 15980939135863952906960713)
        ·
          refine ⟨11985704351897964680220535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15980939135863952906960713 11985704351897964680220535)
          ·
            refine ⟨17978556527846947020330803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985704351897964680220535 17978556527846947020330803)
            ·
              refine ⟨26967834791770420530496205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17978556527846947020330803 26967834791770420530496205)
              ·
                refine ⟨10112938046913907698936077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26967834791770420530496205 10112938046913907698936077)
                ·
                  refine ⟨3792351767592715387101029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112938046913907698936077 3792351767592715387101029)
                  ·
                    refine ⟨711065956423634135081443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792351767592715387101029 711065956423634135081443)
                    ·
                      rfl

theorem cell22_2077194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2077194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077194 prefixEnd_2077194 := by exact prefixLift 2077194
  have htrace : WordTrace (prefixWord ++ tailWord_2077194) baseStart_2077194 baseEnd_2077194 := by
    simpa [prefixWord, tailWord_2077194, baseEnd_2077194] using wordTrace_append hprefix tailTrace_2077194
  have hstable : (prefixWord ++ tailWord_2077194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077194).length < 2 ^ (prefixWord ++ tailWord_2077194).sum := by decide
  have hdescent : baseEnd_2077194 < baseStart_2077194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077226 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_2077226 : Nat := 118140960795 + 2077226 * 2 ^ 59
def prefixEnd_2077226 : Nat := 4983230072969 + 3 ^ 40 * 2077226 * 2
def baseEnd_2077226 : Nat := 237025636892532239427115

theorem tailTrace_2077226 : CollatzResearch.WordTrace tailWord_2077226 prefixEnd_2077226 237025636892532239427115 := by
  unfold tailWord_2077226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940664093143109700466883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50508437581714959201245021 18940664093143109700466883)
  ·
    refine ⟨28410996139714664550700325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18940664093143109700466883 28410996139714664550700325)
    ·
      refine ⟨5327061776196499603256311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28410996139714664550700325 5327061776196499603256311)
      ·
        refine ⟨7990592664294749404884467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327061776196499603256311 7990592664294749404884467)
        ·
          refine ⟨11985888996442124107326701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990592664294749404884467 11985888996442124107326701)
          ·
            refine ⟨4494708373665796540247513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11985888996442124107326701 4494708373665796540247513)
            ·
              refine ⟨3371031280249347405185635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494708373665796540247513 3371031280249347405185635)
              ·
                refine ⟨5056546920374021107778453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371031280249347405185635 5056546920374021107778453)
                ·
                  refine ⟨237025636892532239427115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5056546920374021107778453 237025636892532239427115)
                  ·
                    rfl

theorem cell22_2077226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_2077226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077226 prefixEnd_2077226 := by exact prefixLift 2077226
  have htrace : WordTrace (prefixWord ++ tailWord_2077226) baseStart_2077226 baseEnd_2077226 := by
    simpa [prefixWord, tailWord_2077226, baseEnd_2077226] using wordTrace_append hprefix tailTrace_2077226
  have hstable : (prefixWord ++ tailWord_2077226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077226).length < 2 ^ (prefixWord ++ tailWord_2077226).sum := by decide
  have hdescent : baseEnd_2077226 < baseStart_2077226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077284 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2077284 : Nat := 118140960795 + 2077284 * 2 ^ 59
def prefixEnd_2077284 : Nat := 4983230072969 + 3 ^ 40 * 2077284 * 2
def baseEnd_2077284 : Nat := 711096765262903900331167

theorem tailTrace_2077284 : CollatzResearch.WordTrace tailWord_2077284 prefixEnd_2077284 711096765262903900331167 := by
  unfold tailWord_2077284
  simp only [CollatzResearch.WordTrace]
  refine ⟨37882385903181157353739453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50509847870908209804985937 37882385903181157353739453)
  ·
    refine ⟨14205894713692934007652295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37882385903181157353739453 14205894713692934007652295)
    ·
      refine ⟨21308842070539401011478443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205894713692934007652295 21308842070539401011478443)
      ·
        refine ⟨31963263105809101517217665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308842070539401011478443 31963263105809101517217665)
        ·
          refine ⟨23972447329356826137913249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31963263105809101517217665 23972447329356826137913249)
          ·
            refine ⟨17979335497017619603434937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23972447329356826137913249 17979335497017619603434937)
            ·
              refine ⟨13484501622763214702576203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17979335497017619603434937 13484501622763214702576203)
              ·
                refine ⟨20226752434144822053864305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13484501622763214702576203 20226752434144822053864305)
                ·
                  refine ⟨15170064325608616540398229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20226752434144822053864305 15170064325608616540398229)
                  ·
                    refine ⟨711096765262903900331167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15170064325608616540398229 711096765262903900331167)
                    ·
                      rfl

theorem cell22_2077284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2077284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077284 prefixEnd_2077284 := by exact prefixLift 2077284
  have htrace : WordTrace (prefixWord ++ tailWord_2077284) baseStart_2077284 baseEnd_2077284 := by
    simpa [prefixWord, tailWord_2077284, baseEnd_2077284] using wordTrace_append hprefix tailTrace_2077284
  have hstable : (prefixWord ++ tailWord_2077284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077284).length < 2 ^ (prefixWord ++ tailWord_2077284).sum := by decide
  have hdescent : baseEnd_2077284 < baseStart_2077284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077376 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_2077376 : Nat := 118140960795 + 2077376 * 2 ^ 59
def prefixEnd_2077376 : Nat := 4983230072969 + 3 ^ 40 * 2077376 * 2
def baseEnd_2077376 : Nat := 711128258743046327030885

theorem tailTrace_2077376 : CollatzResearch.WordTrace tailWord_2077376 prefixEnd_2077376 711128258743046327030885 := by
  unfold tailWord_2077376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37884063661014507209913991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50512084881352676279885321 37884063661014507209913991)
  ·
    refine ⟨56826095491521760814870987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37884063661014507209913991 56826095491521760814870987)
    ·
      refine ⟨85239143237282641222306481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56826095491521760814870987 85239143237282641222306481)
      ·
        refine ⟨63929357427961980916729861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85239143237282641222306481 63929357427961980916729861)
        ·
          refine ⟨11986754517742871421886849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63929357427961980916729861 11986754517742871421886849)
          ·
            refine ⟨8990065888307153566415137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11986754517742871421886849 8990065888307153566415137)
            ·
              refine ⟨6742549416230365174811353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990065888307153566415137 6742549416230365174811353)
              ·
                refine ⟨5056912062172773881108515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742549416230365174811353 5056912062172773881108515)
                ·
                  refine ⟨7585368093259160821662773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056912062172773881108515 7585368093259160821662773)
                  ·
                    refine ⟨711128258743046327030885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7585368093259160821662773 711128258743046327030885)
                    ·
                      rfl

theorem cell22_2077376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_2077376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077376 prefixEnd_2077376 := by exact prefixLift 2077376
  have htrace : WordTrace (prefixWord ++ tailWord_2077376) baseStart_2077376 baseEnd_2077376 := by
    simpa [prefixWord, tailWord_2077376, baseEnd_2077376] using wordTrace_append hprefix tailTrace_2077376
  have hstable : (prefixWord ++ tailWord_2077376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077376).length < 2 ^ (prefixWord ++ tailWord_2077376).sum := by decide
  have hdescent : baseEnd_2077376 < baseStart_2077376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077380 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2077380 : Nat := 118140960795 + 2077380 * 2 ^ 59
def prefixEnd_2077380 : Nat := 4983230072969 + 3 ^ 40 * 2077380 * 2
def baseEnd_2077380 : Nat := 711129628024791649930873

theorem tailTrace_2077380 : CollatzResearch.WordTrace tailWord_2077380 prefixEnd_2077380 711129628024791649930873 := by
  unfold tailWord_2077380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37884136607007261551486797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50512182142676348735315729 37884136607007261551486797)
  ·
    refine ⟨14206551227627723081807549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37884136607007261551486797 14206551227627723081807549)
    ·
      refine ⟨5327456710360396155677831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14206551227627723081807549 5327456710360396155677831)
      ·
        refine ⟨7991185065540594233516747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327456710360396155677831 7991185065540594233516747)
        ·
          refine ⟨11986777598310891350275121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991185065540594233516747 11986777598310891350275121)
          ·
            refine ⟨8990083198733168512706341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11986777598310891350275121 8990083198733168512706341)
            ·
              refine ⟨1685640599762469096132439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8990083198733168512706341 1685640599762469096132439)
              ·
                refine ⟨2528460899643703644198659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685640599762469096132439 2528460899643703644198659)
                ·
                  refine ⟨3792691349465555466297989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528460899643703644198659 3792691349465555466297989)
                  ·
                    refine ⟨711129628024791649930873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792691349465555466297989 711129628024791649930873)
                    ·
                      rfl

theorem cell22_2077380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2077380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077380 prefixEnd_2077380 := by exact prefixLift 2077380
  have htrace : WordTrace (prefixWord ++ tailWord_2077380) baseStart_2077380 baseEnd_2077380 := by
    simpa [prefixWord, tailWord_2077380, baseEnd_2077380] using wordTrace_append hprefix tailTrace_2077380
  have hstable : (prefixWord ++ tailWord_2077380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077380).length < 2 ^ (prefixWord ++ tailWord_2077380).sum := by decide
  have hdescent : baseEnd_2077380 < baseStart_2077380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077421 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2077421 : Nat := 118140960795 + 2077421 * 2 ^ 59
def prefixEnd_2077421 : Nat := 4983230072969 + 3 ^ 40 * 2077421 * 2
def baseEnd_2077421 : Nat := 711143663162681209655747

theorem tailTrace_2077421 : CollatzResearch.WordTrace tailWord_2077421 prefixEnd_2077421 711143663162681209655747 := by
  unfold tailWord_2077421
  simp only [CollatzResearch.WordTrace]
  refine ⟨75769768606865987105216117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50513179071243991403477411 75769768606865987105216117)
  ·
    refine ⟨7103415806893686291114011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75769768606865987105216117 7103415806893686291114011)
    ·
      refine ⟨10655123710340529436671017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103415806893686291114011 10655123710340529436671017)
      ·
        refine ⟨7991342782755397077503263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10655123710340529436671017 7991342782755397077503263)
        ·
          refine ⟨11987014174133095616254895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991342782755397077503263 11987014174133095616254895)
          ·
            refine ⟨17980521261199643424382343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987014174133095616254895 17980521261199643424382343)
            ·
              refine ⟨26970781891799465136573515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17980521261199643424382343 26970781891799465136573515)
              ·
                refine ⟨40456172837699197704860273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26970781891799465136573515 40456172837699197704860273)
                ·
                  refine ⟨30342129628274398278645205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40456172837699197704860273 30342129628274398278645205)
                  ·
                    refine ⟨711143663162681209655747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30342129628274398278645205 711143663162681209655747)
                    ·
                      rfl

theorem cell22_2077421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2077421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077421 prefixEnd_2077421 := by exact prefixLift 2077421
  have htrace : WordTrace (prefixWord ++ tailWord_2077421) baseStart_2077421 baseEnd_2077421 := by
    simpa [prefixWord, tailWord_2077421, baseEnd_2077421] using wordTrace_append hprefix tailTrace_2077421
  have hstable : (prefixWord ++ tailWord_2077421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077421).length < 2 ^ (prefixWord ++ tailWord_2077421).sum := by decide
  have hdescent : baseEnd_2077421 < baseStart_2077421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077423 : List Nat := [1, 1, 2, 1, 5, 4, 2, 6]
def baseStart_2077423 : Nat := 118140960795 + 2077423 * 2 ^ 59
def prefixEnd_2077423 : Nat := 4983230072969 + 3 ^ 40 * 2077423 * 2
def baseEnd_2077423 : Nat := 79016038644839319011749

theorem tailTrace_2077423 : CollatzResearch.WordTrace tailWord_2077423 prefixEnd_2077423 79016038644839319011749 := by
  unfold tailWord_2077423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75769841552858741446788923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50513227701905827631192615 75769841552858741446788923)
  ·
    refine ⟨113654762329288112170183385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75769841552858741446788923 113654762329288112170183385)
    ·
      refine ⟨85241071746966084127637539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113654762329288112170183385 85241071746966084127637539)
      ·
        refine ⟨127861607620449126191456309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85241071746966084127637539 127861607620449126191456309)
        ·
          refine ⟨11987025714417105580449029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127861607620449126191456309 11987025714417105580449029)
          ·
            refine ⟨2247567321453207296334193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11987025714417105580449029 2247567321453207296334193)
            ·
              refine ⟨1685675491089905472250645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247567321453207296334193 1685675491089905472250645)
              ·
                refine ⟨79016038644839319011749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1685675491089905472250645 79016038644839319011749)
                ·
                  rfl

theorem cell22_2077423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 6].length) (baseStart_2077423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077423 prefixEnd_2077423 := by exact prefixLift 2077423
  have htrace : WordTrace (prefixWord ++ tailWord_2077423) baseStart_2077423 baseEnd_2077423 := by
    simpa [prefixWord, tailWord_2077423, baseEnd_2077423] using wordTrace_append hprefix tailTrace_2077423
  have hstable : (prefixWord ++ tailWord_2077423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077423).length < 2 ^ (prefixWord ++ tailWord_2077423).sum := by decide
  have hdescent : baseEnd_2077423 < baseStart_2077423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077451 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 5]
def baseStart_2077451 : Nat := 118140960795 + 2077451 * 2 ^ 59
def prefixEnd_2077451 : Nat := 4983230072969 + 3 ^ 40 * 2077451 * 2
def baseEnd_2077451 : Nat := 237051310925257043801885

theorem tailTrace_2077451 : CollatzResearch.WordTrace tailWord_2077451 prefixEnd_2077451 237051310925257043801885 := by
  unfold tailWord_2077451
  simp only [CollatzResearch.WordTrace]
  refine ⟨75770862796757302228808207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50513908531171534819205471 75770862796757302228808207)
  ·
    refine ⟨113656294195135953343212311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75770862796757302228808207 113656294195135953343212311)
    ·
      refine ⟨170484441292703930014818467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113656294195135953343212311 170484441292703930014818467)
      ·
        refine ⟨255726661939055895022227701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170484441292703930014818467 255726661939055895022227701)
        ·
          refine ⟨23974374556786490158333847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255726661939055895022227701 23974374556786490158333847)
          ·
            refine ⟨35961561835179735237500771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23974374556786490158333847 35961561835179735237500771)
            ·
              refine ⟨53942342752769602856251157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35961561835179735237500771 53942342752769602856251157)
              ·
                refine ⟨2528547316536075133886773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53942342752769602856251157 2528547316536075133886773)
                ·
                  refine ⟨237051310925257043801885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528547316536075133886773 237051310925257043801885)
                  ·
                    rfl

theorem cell22_2077451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].length) (baseStart_2077451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077451 prefixEnd_2077451 := by exact prefixLift 2077451
  have htrace : WordTrace (prefixWord ++ tailWord_2077451) baseStart_2077451 baseEnd_2077451 := by
    simpa [prefixWord, tailWord_2077451, baseEnd_2077451] using wordTrace_append hprefix tailTrace_2077451
  have hstable : (prefixWord ++ tailWord_2077451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077451).length < 2 ^ (prefixWord ++ tailWord_2077451).sum := by decide
  have hdescent : baseEnd_2077451 < baseStart_2077451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077466 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_2077466 : Nat := 118140960795 + 2077466 * 2 ^ 59
def prefixEnd_2077466 : Nat := 4983230072969 + 3 ^ 40 * 2077466 * 2
def baseEnd_2077466 : Nat := 711159067582316092280609

theorem tailTrace_2077466 : CollatzResearch.WordTrace tailWord_2077466 prefixEnd_2077466 711159067582316092280609 := by
  unfold tailWord_2077466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18942852472925739947651063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50514273261135306527069501 18942852472925739947651063)
  ·
    refine ⟨28414278709388609921476595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18942852472925739947651063 28414278709388609921476595)
    ·
      refine ⟨42621418064082914882214893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28414278709388609921476595 42621418064082914882214893)
      ·
        refine ⟨15983031774031093080830585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42621418064082914882214893 15983031774031093080830585)
        ·
          refine ⟨11987273830523319810622939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15983031774031093080830585 11987273830523319810622939)
          ·
            refine ⟨17980910745784979715934409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987273830523319810622939 17980910745784979715934409)
            ·
              refine ⟨13485683059338734786950807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17980910745784979715934409 13485683059338734786950807)
              ·
                refine ⟨20228524589008102180426211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13485683059338734786950807 20228524589008102180426211)
                ·
                  refine ⟨30342786883512153270639317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20228524589008102180426211 30342786883512153270639317)
                  ·
                    refine ⟨711159067582316092280609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30342786883512153270639317 711159067582316092280609)
                    ·
                      rfl

theorem cell22_2077466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_2077466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077466 prefixEnd_2077466 := by exact prefixLift 2077466
  have htrace : WordTrace (prefixWord ++ tailWord_2077466) baseStart_2077466 baseEnd_2077466 := by
    simpa [prefixWord, tailWord_2077466, baseEnd_2077466] using wordTrace_append hprefix tailTrace_2077466
  have hstable : (prefixWord ++ tailWord_2077466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077466).length < 2 ^ (prefixWord ++ tailWord_2077466).sum := by decide
  have hdescent : baseEnd_2077466 < baseStart_2077466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077468 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_2077468 : Nat := 118140960795 + 2077468 * 2 ^ 59
def prefixEnd_2077468 : Nat := 4983230072969 + 3 ^ 40 * 2077468 * 2
def baseEnd_2077468 : Nat := 237053250741062917910201

theorem tailTrace_2077468 : CollatzResearch.WordTrace tailWord_2077468 prefixEnd_2077468 237053250741062917910201 := by
  unfold tailWord_2077468
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885741418847857066088529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50514321891797142754784705 37885741418847857066088529)
  ·
    refine ⟨28414306064135892799566397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37885741418847857066088529 28414306064135892799566397)
    ·
      refine ⟨10655364774050959799837399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28414306064135892799566397 10655364774050959799837399)
      ·
        refine ⟨15983047161076439699756099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655364774050959799837399 15983047161076439699756099)
        ·
          refine ⟨23974570741614659549634149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983047161076439699756099 23974570741614659549634149)
          ·
            refine ⟨4495232014052748665556403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23974570741614659549634149 4495232014052748665556403)
            ·
              refine ⟨6742848021079122998334605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495232014052748665556403 6742848021079122998334605)
              ·
                refine ⟨2528568007904671124375477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6742848021079122998334605 2528568007904671124375477)
                ·
                  refine ⟨237053250741062917910201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528568007904671124375477 237053250741062917910201)
                  ·
                    rfl

theorem cell22_2077468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_2077468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077468 prefixEnd_2077468 := by exact prefixLift 2077468
  have htrace : WordTrace (prefixWord ++ tailWord_2077468) baseStart_2077468 baseEnd_2077468 := by
    simpa [prefixWord, tailWord_2077468, baseEnd_2077468] using wordTrace_append hprefix tailTrace_2077468
  have hstable : (prefixWord ++ tailWord_2077468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077468).length < 2 ^ (prefixWord ++ tailWord_2077468).sum := by decide
  have hdescent : baseEnd_2077468 < baseStart_2077468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077481 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_2077481 : Nat := 118140960795 + 2077481 * 2 ^ 59
def prefixEnd_2077481 : Nat := 4983230072969 + 3 ^ 40 * 2077481 * 2
def baseEnd_2077481 : Nat := 711164202388861053155563

theorem tailTrace_2077481 : CollatzResearch.WordTrace tailWord_2077481 prefixEnd_2077481 711164202388861053155563 := by
  unfold tailWord_2077481
  simp only [CollatzResearch.WordTrace]
  refine ⟨75771956986648617352400297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50514637991099078234933531 75771956986648617352400297)
  ·
    refine ⟨56828967739986463014300223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75771956986648617352400297 56828967739986463014300223)
    ·
      refine ⟨85243451609979694521450335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56828967739986463014300223 85243451609979694521450335)
      ·
        refine ⟨127865177414969541782175503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85243451609979694521450335 127865177414969541782175503)
        ·
          refine ⟨191797766122454312673263255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127865177414969541782175503 191797766122454312673263255)
          ·
            refine ⟨287696649183681469009894883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191797766122454312673263255 287696649183681469009894883)
            ·
              refine ⟨431544973775522203514842325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287696649183681469009894883 431544973775522203514842325)
              ·
                refine ⟨10114335322863801644879117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431544973775522203514842325 10114335322863801644879117)
                ·
                  refine ⟨3792875746073925616829669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10114335322863801644879117 3792875746073925616829669)
                  ·
                    refine ⟨711164202388861053155563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792875746073925616829669 711164202388861053155563)
                    ·
                      rfl

theorem cell22_2077481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_2077481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077481 prefixEnd_2077481 := by exact prefixLift 2077481
  have htrace : WordTrace (prefixWord ++ tailWord_2077481) baseStart_2077481 baseEnd_2077481 := by
    simpa [prefixWord, tailWord_2077481, baseEnd_2077481] using wordTrace_append hprefix tailTrace_2077481
  have hstable : (prefixWord ++ tailWord_2077481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077481).length < 2 ^ (prefixWord ++ tailWord_2077481).sum := by decide
  have hdescent : baseEnd_2077481 < baseStart_2077481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077511 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2077511 : Nat := 118140960795 + 2077511 * 2 ^ 59
def prefixEnd_2077511 : Nat := 4983230072969 + 3 ^ 40 * 2077511 * 2
def baseEnd_2077511 : Nat := 711174472001950974905471

theorem tailTrace_2077511 : CollatzResearch.WordTrace tailWord_2077511 prefixEnd_2077511 711174472001950974905471 := by
  unfold tailWord_2077511
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773051176539932475992387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50515367451026621650661591 75773051176539932475992387)
  ·
    refine ⟨113659576764809898713988581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75773051176539932475992387 113659576764809898713988581)
    ·
      refine ⟨21311170643401856008872859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113659576764809898713988581 21311170643401856008872859)
      ·
        refine ⟨31966755965102784013309289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21311170643401856008872859 31966755965102784013309289)
        ·
          refine ⟨23975066973827088009981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31966755965102784013309289 23975066973827088009981967)
          ·
            refine ⟨35962600460740632014972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975066973827088009981967 35962600460740632014972951)
            ·
              refine ⟨53943900691110948022459427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35962600460740632014972951 53943900691110948022459427)
              ·
                refine ⟨80915851036666422033689141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53943900691110948022459427 80915851036666422033689141)
                ·
                  refine ⟨7585861034687477065658357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80915851036666422033689141 7585861034687477065658357)
                  ·
                    refine ⟨711174472001950974905471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7585861034687477065658357 711174472001950974905471)
                    ·
                      rfl

theorem cell22_2077511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2077511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077511 prefixEnd_2077511 := by exact prefixLift 2077511
  have htrace : WordTrace (prefixWord ++ tailWord_2077511) baseStart_2077511 baseEnd_2077511 := by
    simpa [prefixWord, tailWord_2077511, baseEnd_2077511] using wordTrace_append hprefix tailTrace_2077511
  have hstable : (prefixWord ++ tailWord_2077511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077511).length < 2 ^ (prefixWord ++ tailWord_2077511).sum := by decide
  have hdescent : baseEnd_2077511 < baseStart_2077511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077541 : List Nat := [1, 3, 1, 3, 1, 1, 2, 10]
def baseStart_2077541 : Nat := 118140960795 + 2077541 * 2 ^ 59
def prefixEnd_2077541 : Nat := 4983230072969 + 3 ^ 40 * 2077541 * 2
def baseEnd_2077541 : Nat := 79020526846115655183931

theorem tailTrace_2077541 : CollatzResearch.WordTrace tailWord_2077541 prefixEnd_2077541 79020526846115655183931 := by
  unfold tailWord_2077541
  simp only [CollatzResearch.WordTrace]
  refine ⟨75774145366431247599584477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50516096910954165066389651 75774145366431247599584477)
  ·
    refine ⟨28415304512411717849844179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75774145366431247599584477 28415304512411717849844179)
    ·
      refine ⟨42622956768617576774766269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28415304512411717849844179 42622956768617576774766269)
      ·
        refine ⟨15983608788231591290537351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42622956768617576774766269 15983608788231591290537351)
        ·
          refine ⟨23975413182347386935806027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983608788231591290537351 23975413182347386935806027)
          ·
            refine ⟨35963119773521080403709041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975413182347386935806027 35963119773521080403709041)
            ·
              refine ⟨26972339830140810302781781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35963119773521080403709041 26972339830140810302781781)
              ·
                refine ⟨79020526846115655183931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26972339830140810302781781 79020526846115655183931)
                ·
                  rfl

theorem cell22_2077541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 10].length) (baseStart_2077541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077541 prefixEnd_2077541 := by exact prefixLift 2077541
  have htrace : WordTrace (prefixWord ++ tailWord_2077541) baseStart_2077541 baseEnd_2077541 := by
    simpa [prefixWord, tailWord_2077541, baseEnd_2077541] using wordTrace_append hprefix tailTrace_2077541
  have hstable : (prefixWord ++ tailWord_2077541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077541).length < 2 ^ (prefixWord ++ tailWord_2077541).sum := by decide
  have hdescent : baseEnd_2077541 < baseStart_2077541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077543 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2077543 : Nat := 118140960795 + 2077543 * 2 ^ 59
def prefixEnd_2077543 : Nat := 4983230072969 + 3 ^ 40 * 2077543 * 2
def baseEnd_2077543 : Nat := 711185426255913558105373

theorem tailTrace_2077543 : CollatzResearch.WordTrace tailWord_2077543 prefixEnd_2077543 711185426255913558105373 := by
  unfold tailWord_2077543
  simp only [CollatzResearch.WordTrace]
  refine ⟨75774218312424001941157283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50516145541616001294104855 75774218312424001941157283)
  ·
    refine ⟨113661327468636002911735925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75774218312424001941157283 113661327468636002911735925)
    ·
      refine ⟨10655749450184625272975243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113661327468636002911735925 10655749450184625272975243)
      ·
        refine ⟨15983624175276937909462865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655749450184625272975243 15983624175276937909462865)
        ·
          refine ⟨11987718131457703432097149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15983624175276937909462865 11987718131457703432097149)
          ·
            refine ⟨4495394299296638787036431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11987718131457703432097149 4495394299296638787036431)
            ·
              refine ⟨6743091448944958180554647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495394299296638787036431 6743091448944958180554647)
              ·
                refine ⟨10114637173417437270831971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743091448944958180554647 10114637173417437270831971)
                ·
                  refine ⟨15171955760126155906247957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114637173417437270831971 15171955760126155906247957)
                  ·
                    refine ⟨711185426255913558105373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15171955760126155906247957 711185426255913558105373)
                    ·
                      rfl

theorem cell22_2077543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2077543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077543 prefixEnd_2077543 := by exact prefixLift 2077543
  have htrace : WordTrace (prefixWord ++ tailWord_2077543) baseStart_2077543 baseEnd_2077543 := by
    simpa [prefixWord, tailWord_2077543, baseEnd_2077543] using wordTrace_append hprefix tailTrace_2077543
  have hstable : (prefixWord ++ tailWord_2077543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077543).length < 2 ^ (prefixWord ++ tailWord_2077543).sum := by decide
  have hdescent : baseEnd_2077543 < baseStart_2077543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077624 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_2077624 : Nat := 118140960795 + 2077624 * 2 ^ 59
def prefixEnd_2077624 : Nat := 4983230072969 + 3 ^ 40 * 2077624 * 2
def baseEnd_2077624 : Nat := 711213154211256346830125

theorem tailTrace_2077624 : CollatzResearch.WordTrace tailWord_2077624 prefixEnd_2077624 711213154211256346830125 := by
  unfold tailWord_2077624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888586312565276387427963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50518115083420368516570617 37888586312565276387427963)
  ·
    refine ⟨56832879468847914581141945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37888586312565276387427963 56832879468847914581141945)
    ·
      refine ⟨42624659601635935935856459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56832879468847914581141945 42624659601635935935856459)
      ·
        refine ⟨63936989402453903903784689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42624659601635935935856459 63936989402453903903784689)
        ·
          refine ⟨47952742051840427927838517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63936989402453903903784689 47952742051840427927838517)
          ·
            refine ⟨4495569567360040118234861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47952742051840427927838517 4495569567360040118234861)
            ·
              refine ⟨1685838587760015044338073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495569567360040118234861 1685838587760015044338073)
              ·
                refine ⟨1264378940820011283253555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685838587760015044338073 1264378940820011283253555)
                ·
                  refine ⟨1896568411230016924880333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264378940820011283253555 1896568411230016924880333)
                  ·
                    refine ⟨711213154211256346830125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896568411230016924880333 711213154211256346830125)
                    ·
                      rfl

theorem cell22_2077624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_2077624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077624 prefixEnd_2077624 := by exact prefixLift 2077624
  have htrace : WordTrace (prefixWord ++ tailWord_2077624) baseStart_2077624 baseEnd_2077624 := by
    simpa [prefixWord, tailWord_2077624, baseEnd_2077624] using wordTrace_append hprefix tailTrace_2077624
  have hstable : (prefixWord ++ tailWord_2077624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077624).length < 2 ^ (prefixWord ++ tailWord_2077624).sum := by decide
  have hdescent : baseEnd_2077624 < baseStart_2077624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077665 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 4]
def baseStart_2077665 : Nat := 118140960795 + 2077665 * 2 ^ 59
def prefixEnd_2077665 : Nat := 4983230072969 + 3 ^ 40 * 2077665 * 2
def baseEnd_2077665 : Nat := 237075729783048635518333

theorem tailTrace_2077665 : CollatzResearch.WordTrace tailWord_2077665 prefixEnd_2077665 237075729783048635518333 := by
  unfold tailWord_2077665
  simp only [CollatzResearch.WordTrace]
  refine ⟨75778668017982016777098449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50519112011988011184732299 75778668017982016777098449)
  ·
    refine ⟨56834001013486512582823837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75778668017982016777098449 56834001013486512582823837)
    ·
      refine ⟨21312750380057442218558939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56834001013486512582823837 21312750380057442218558939)
      ·
        refine ⟨31969125570086163327838409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21312750380057442218558939 31969125570086163327838409)
        ·
          refine ⟨23976844177564622495878807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31969125570086163327838409 23976844177564622495878807)
          ·
            refine ⟨35965266266346933743818211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23976844177564622495878807 35965266266346933743818211)
            ·
              refine ⟨53947899399520400615727317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35965266266346933743818211 53947899399520400615727317)
              ·
                refine ⟨1264403892176259389431109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53947899399520400615727317 1264403892176259389431109)
                ·
                  refine ⟨237075729783048635518333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264403892176259389431109 237075729783048635518333)
                  ·
                    rfl

theorem cell22_2077665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_2077665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077665 prefixEnd_2077665 := by exact prefixLift 2077665
  have htrace : WordTrace (prefixWord ++ tailWord_2077665) baseStart_2077665 baseEnd_2077665 := by
    simpa [prefixWord, tailWord_2077665, baseEnd_2077665] using wordTrace_append hprefix tailTrace_2077665
  have hstable : (prefixWord ++ tailWord_2077665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077665).length < 2 ^ (prefixWord ++ tailWord_2077665).sum := by decide
  have hdescent : baseEnd_2077665 < baseStart_2077665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077667 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 1, 4]
def baseStart_2077667 : Nat := 118140960795 + 2077667 * 2 ^ 59
def prefixEnd_2077667 : Nat := 4983230072969 + 3 ^ 40 * 2077667 * 2
def baseEnd_2077667 : Nat := 711227873990018568004993

theorem tailTrace_2077667 : CollatzResearch.WordTrace tailWord_2077667 prefixEnd_2077667 711227873990018568004993 := by
  unfold tailWord_2077667
  simp only [CollatzResearch.WordTrace]
  refine ⟨75778740963974771118671255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50519160642649847412447503 75778740963974771118671255)
  ·
    refine ⟨113668111445962156678006883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75778740963974771118671255 113668111445962156678006883)
    ·
      refine ⟨170502167168943235017010325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113668111445962156678006883 170502167168943235017010325)
      ·
        refine ⟨7992289086044214141422359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170502167168943235017010325 7992289086044214141422359)
        ·
          refine ⟨11988433629066321212133539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992289086044214141422359 11988433629066321212133539)
          ·
            refine ⟨17982650443599481818200309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988433629066321212133539 17982650443599481818200309)
            ·
              refine ⟨1685873479087451420456279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17982650443599481818200309 1685873479087451420456279)
              ·
                refine ⟨2528810218631177130684419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685873479087451420456279 2528810218631177130684419)
                ·
                  refine ⟨3793215327946765696026629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528810218631177130684419 3793215327946765696026629)
                  ·
                    refine ⟨711227873990018568004993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793215327946765696026629 711227873990018568004993)
                    ·
                      rfl

theorem cell22_2077667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 4].length) (baseStart_2077667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077667 prefixEnd_2077667 := by exact prefixLift 2077667
  have htrace : WordTrace (prefixWord ++ tailWord_2077667) baseStart_2077667 baseEnd_2077667 := by
    simpa [prefixWord, tailWord_2077667, baseEnd_2077667] using wordTrace_append hprefix tailTrace_2077667
  have hstable : (prefixWord ++ tailWord_2077667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077667).length < 2 ^ (prefixWord ++ tailWord_2077667).sum := by decide
  have hdescent : baseEnd_2077667 < baseStart_2077667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077697 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2077697 : Nat := 118140960795 + 2077697 * 2 ^ 59
def prefixEnd_2077697 : Nat := 4983230072969 + 3 ^ 40 * 2077697 * 2
def baseEnd_2077697 : Nat := 711238143603108489754901

theorem tailTrace_2077697 : CollatzResearch.WordTrace tailWord_2077697 prefixEnd_2077697 711238143603108489754901 := by
  unfold tailWord_2077697
  simp only [CollatzResearch.WordTrace]
  refine ⟨75779835153866086242263345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50519890102577390828175563 75779835153866086242263345)
  ·
    refine ⟨56834876365399564681697509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75779835153866086242263345 56834876365399564681697509)
    ·
      refine ⟨10656539318512418377818283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56834876365399564681697509 10656539318512418377818283)
      ·
        refine ⟨15984808977768627566727425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656539318512418377818283 15984808977768627566727425)
        ·
          refine ⟨11988606733326470675045569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15984808977768627566727425 11988606733326470675045569)
          ·
            refine ⟨8991455049994853006284177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11988606733326470675045569 8991455049994853006284177)
            ·
              refine ⟨6743591287496139754713133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991455049994853006284177 6743591287496139754713133)
              ·
                refine ⟨2528846732811052408017425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6743591287496139754713133 2528846732811052408017425)
                ·
                  refine ⟨1896635049608289306013069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528846732811052408017425 1896635049608289306013069)
                  ·
                    refine ⟨711238143603108489754901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896635049608289306013069 711238143603108489754901)
                    ·
                      rfl

theorem cell22_2077697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2077697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077697 prefixEnd_2077697 := by exact prefixLift 2077697
  have htrace : WordTrace (prefixWord ++ tailWord_2077697) baseStart_2077697 baseEnd_2077697 := by
    simpa [prefixWord, tailWord_2077697, baseEnd_2077697] using wordTrace_append hprefix tailTrace_2077697
  have hstable : (prefixWord ++ tailWord_2077697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077697).length < 2 ^ (prefixWord ++ tailWord_2077697).sum := by decide
  have hdescent : baseEnd_2077697 < baseStart_2077697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077815 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_2077815 : Nat := 118140960795 + 2077815 * 2 ^ 59
def prefixEnd_2077815 : Nat := 4983230072969 + 3 ^ 40 * 2077815 * 2
def baseEnd_2077815 : Nat := 711278537414595515304539

theorem tailTrace_2077815 : CollatzResearch.WordTrace tailWord_2077815 prefixEnd_2077815 711278537414595515304539 := by
  unfold tailWord_2077815
  simp only [CollatzResearch.WordTrace]
  refine ⟨75784138967438592395058899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50522759311625728263372599 75784138967438592395058899)
  ·
    refine ⟨113676208451157888592588349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75784138967438592395058899 113676208451157888592588349)
    ·
      refine ⟨42628578169184208222220631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113676208451157888592588349 42628578169184208222220631)
      ·
        refine ⟨63942867253776312333330947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42628578169184208222220631 63942867253776312333330947)
        ·
          refine ⟨95914300880664468499996421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63942867253776312333330947 95914300880664468499996421)
          ·
            refine ⟨17983931415124587843749329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95914300880664468499996421 17983931415124587843749329)
            ·
              refine ⟨13487948561343440882811997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983931415124587843749329 13487948561343440882811997)
              ·
                refine ⟨5057980710503790331054499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13487948561343440882811997 5057980710503790331054499)
                ·
                  refine ⟨7586971065755685496581749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057980710503790331054499 7586971065755685496581749)
                  ·
                    refine ⟨711278537414595515304539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7586971065755685496581749 711278537414595515304539)
                    ·
                      rfl

theorem cell22_2077815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_2077815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077815 prefixEnd_2077815 := by exact prefixLift 2077815
  have htrace : WordTrace (prefixWord ++ tailWord_2077815) baseStart_2077815 baseEnd_2077815 := by
    simpa [prefixWord, tailWord_2077815, baseEnd_2077815] using wordTrace_append hprefix tailTrace_2077815
  have hstable : (prefixWord ++ tailWord_2077815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077815).length < 2 ^ (prefixWord ++ tailWord_2077815).sum := by decide
  have hdescent : baseEnd_2077815 < baseStart_2077815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077847 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2077847 : Nat := 118140960795 + 2077847 * 2 ^ 59
def prefixEnd_2077847 : Nat := 4983230072969 + 3 ^ 40 * 2077847 * 2
def baseEnd_2077847 : Nat := 711289491668558098504441

theorem tailTrace_2077847 : CollatzResearch.WordTrace tailWord_2077847 prefixEnd_2077847 711289491668558098504441 := by
  unfold tailWord_2077847
  simp only [CollatzResearch.WordTrace]
  refine ⟨75785306103322661860223795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50523537402215107906815863 75785306103322661860223795)
  ·
    refine ⟨113677959154983992790335693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75785306103322661860223795 113677959154983992790335693)
    ·
      refine ⟨42629234683118997296375885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113677959154983992790335693 42629234683118997296375885)
      ·
        refine ⟨15985963006169623986140957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42629234683118997296375885 15985963006169623986140957)
        ·
          refine ⟨5994736127313608994802859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15985963006169623986140957 5994736127313608994802859)
          ·
            refine ⟨8992104190970413492204289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994736127313608994802859 8992104190970413492204289)
            ·
              refine ⟨6744078143227810119153217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992104190970413492204289 6744078143227810119153217)
              ·
                refine ⟨5058058607420857589364913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744078143227810119153217 5058058607420857589364913)
                ·
                  refine ⟨3793543955565643192023685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058058607420857589364913 3793543955565643192023685)
                  ·
                    refine ⟨711289491668558098504441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793543955565643192023685 711289491668558098504441)
                    ·
                      rfl

theorem cell22_2077847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2077847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077847 prefixEnd_2077847 := by exact prefixLift 2077847
  have htrace : WordTrace (prefixWord ++ tailWord_2077847) baseStart_2077847 baseEnd_2077847 := by
    simpa [prefixWord, tailWord_2077847, baseEnd_2077847] using wordTrace_append hprefix tailTrace_2077847
  have hstable : (prefixWord ++ tailWord_2077847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077847).length < 2 ^ (prefixWord ++ tailWord_2077847).sum := by decide
  have hdescent : baseEnd_2077847 < baseStart_2077847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2077866 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2077866 : Nat := 118140960795 + 2077866 * 2 ^ 59
def prefixEnd_2077866 : Nat := 4983230072969 + 3 ^ 40 * 2077866 * 2
def baseEnd_2077866 : Nat := 711295995756848382279383

theorem tailTrace_2077866 : CollatzResearch.WordTrace tailWord_2077866 prefixEnd_2077866 711295995756848382279383 := by
  unfold tailWord_2077866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946499772563457026291363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50523999393502552070110301 18946499772563457026291363)
  ·
    refine ⟨28419749658845185539437045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18946499772563457026291363 28419749658845185539437045)
    ·
      refine ⟨2664351530516736144322223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28419749658845185539437045 2664351530516736144322223)
      ·
        refine ⟨3996527295775104216483335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664351530516736144322223 3996527295775104216483335)
        ·
          refine ⟨5994790943662656324725003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996527295775104216483335 5994790943662656324725003)
          ·
            refine ⟨8992186415493984487087505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994790943662656324725003 8992186415493984487087505)
            ·
              refine ⟨6744139811620488365315629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992186415493984487087505 6744139811620488365315629)
              ·
                refine ⟨2529052429357683136993361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744139811620488365315629 2529052429357683136993361)
                ·
                  refine ⟨1896789322018262352745021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2529052429357683136993361 1896789322018262352745021)
                  ·
                    refine ⟨711295995756848382279383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896789322018262352745021 711295995756848382279383)
                    ·
                      rfl

theorem cell22_2077866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2077866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2077866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2077866 prefixEnd_2077866 := by exact prefixLift 2077866
  have htrace : WordTrace (prefixWord ++ tailWord_2077866) baseStart_2077866 baseEnd_2077866 := by
    simpa [prefixWord, tailWord_2077866, baseEnd_2077866] using wordTrace_append hprefix tailTrace_2077866
  have hstable : (prefixWord ++ tailWord_2077866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2077866).length < 2 ^ (prefixWord ++ tailWord_2077866).sum := by decide
  have hdescent : baseEnd_2077866 < baseStart_2077866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2077866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078020 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_2078020 : Nat := 118140960795 + 2078020 * 2 ^ 59
def prefixEnd_2078020 : Nat := 4983230072969 + 3 ^ 40 * 2078020 * 2
def baseEnd_2078020 : Nat := 237116237701347771309637

theorem tailTrace_2078020 : CollatzResearch.WordTrace tailWord_2078020 prefixEnd_2078020 237116237701347771309637 := by
  unfold tailWord_2078020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895807965847956203135757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50527743954463941604181009 37895807965847956203135757)
  ·
    refine ⟨14210927987192983576175909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37895807965847956203135757 14210927987192983576175909)
    ·
      refine ⟨2664548997598684420532983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14210927987192983576175909 2664548997598684420532983)
      ·
        refine ⟨3996823496398026630799475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664548997598684420532983 3996823496398026630799475)
        ·
          refine ⟨5995235244597039946199213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996823496398026630799475 5995235244597039946199213)
          ·
            refine ⟨2248213216723889979824705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5995235244597039946199213 2248213216723889979824705)
            ·
              refine ⟨1686159912542917484868529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248213216723889979824705 1686159912542917484868529)
              ·
                refine ⟨1264619934407188113651397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686159912542917484868529 1264619934407188113651397)
                ·
                  refine ⟨237116237701347771309637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264619934407188113651397 237116237701347771309637)
                  ·
                    rfl

theorem cell22_2078020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_2078020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078020 prefixEnd_2078020 := by exact prefixLift 2078020
  have htrace : WordTrace (prefixWord ++ tailWord_2078020) baseStart_2078020 baseEnd_2078020 := by
    simpa [prefixWord, tailWord_2078020, baseEnd_2078020] using wordTrace_append hprefix tailTrace_2078020
  have hstable : (prefixWord ++ tailWord_2078020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078020).length < 2 ^ (prefixWord ++ tailWord_2078020).sum := by decide
  have hdescent : baseEnd_2078020 < baseStart_2078020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078106 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_2078106 : Nat := 118140960795 + 2078106 * 2 ^ 59
def prefixEnd_2078106 : Nat := 4983230072969 + 3 ^ 40 * 2078106 * 2
def baseEnd_2078106 : Nat := 711378152661567756278647

theorem tailTrace_2078106 : CollatzResearch.WordTrace tailWord_2078106 prefixEnd_2078106 711378152661567756278647 := by
  unfold tailWord_2078106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18948688152346087273475543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50529835072922899395934781 18948688152346087273475543)
  ·
    refine ⟨28423032228519130910213315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18948688152346087273475543 28423032228519130910213315)
    ·
      refine ⟨42634548342778696365319973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423032228519130910213315 42634548342778696365319973)
      ·
        refine ⟨7993977814271005568497495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42634548342778696365319973 7993977814271005568497495)
        ·
          refine ⟨11990966721406508352746243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993977814271005568497495 11990966721406508352746243)
          ·
            refine ⟨17986450082109762529119365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990966721406508352746243 17986450082109762529119365)
            ·
              refine ⟨3372459390395580474209881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17986450082109762529119365 3372459390395580474209881)
              ·
                refine ⟨2529344542796685355657411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372459390395580474209881 2529344542796685355657411)
                ·
                  refine ⟨3794016814195028033486117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529344542796685355657411 3794016814195028033486117)
                  ·
                    refine ⟨711378152661567756278647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3794016814195028033486117 711378152661567756278647)
                    ·
                      rfl

theorem cell22_2078106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_2078106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078106 prefixEnd_2078106 := by exact prefixLift 2078106
  have htrace : WordTrace (prefixWord ++ tailWord_2078106) baseStart_2078106 baseEnd_2078106 := by
    simpa [prefixWord, tailWord_2078106, baseEnd_2078106] using wordTrace_append hprefix tailTrace_2078106
  have hstable : (prefixWord ++ tailWord_2078106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078106).length < 2 ^ (prefixWord ++ tailWord_2078106).sum := by decide
  have hdescent : baseEnd_2078106 < baseStart_2078106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078119 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2078119 : Nat := 118140960795 + 2078119 * 2 ^ 59
def prefixEnd_2078119 : Nat := 4983230072969 + 3 ^ 40 * 2078119 * 2
def baseEnd_2078119 : Nat := 711382602827240055703607

theorem tailTrace_2078119 : CollatzResearch.WordTrace tailWord_2078119 prefixEnd_2078119 711382602827240055703607 := by
  unfold tailWord_2078119
  simp only [CollatzResearch.WordTrace]
  refine ⟨75795226758337252314125411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50530151172224834876083607 75795226758337252314125411)
  ·
    refine ⟨113692840137505878471188117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75795226758337252314125411 113692840137505878471188117)
    ·
      refine ⟨5329351881445588053336943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113692840137505878471188117 5329351881445588053336943)
      ·
        refine ⟨7994027822168382080005415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329351881445588053336943 7994027822168382080005415)
        ·
          refine ⟨11991041733252573120008123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994027822168382080005415 11991041733252573120008123)
          ·
            refine ⟨17986562599878859680012185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991041733252573120008123 17986562599878859680012185)
            ·
              refine ⟨13489921949909144760009139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17986562599878859680012185 13489921949909144760009139)
              ·
                refine ⟨20234882924863717140013709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489921949909144760009139 20234882924863717140013709)
                ·
                  refine ⟨7588081096823893927505141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20234882924863717140013709 7588081096823893927505141)
                  ·
                    refine ⟨711382602827240055703607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7588081096823893927505141 711382602827240055703607)
                    ·
                      rfl

theorem cell22_2078119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2078119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078119 prefixEnd_2078119 := by exact prefixLift 2078119
  have htrace : WordTrace (prefixWord ++ tailWord_2078119) baseStart_2078119 baseEnd_2078119 := by
    simpa [prefixWord, tailWord_2078119, baseEnd_2078119] using wordTrace_append hprefix tailTrace_2078119
  have hstable : (prefixWord ++ tailWord_2078119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078119).length < 2 ^ (prefixWord ++ tailWord_2078119).sum := by decide
  have hdescent : baseEnd_2078119 < baseStart_2078119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078166 : List Nat := [5, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2078166 : Nat := 118140960795 + 2078166 * 2 ^ 59
def prefixEnd_2078166 : Nat := 4983230072969 + 3 ^ 40 * 2078166 * 2
def baseEnd_2078166 : Nat := 79044299098638622197607

theorem tailTrace_2078166 : CollatzResearch.WordTrace tailWord_2078166 prefixEnd_2078166 79044299098638622197607 := by
  unfold tailWord_2078166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737308811822936208817897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50531293992777986227390901 4737308811822936208817897)
  ·
    refine ⟨3552981608867202156613423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4737308811822936208817897 3552981608867202156613423)
    ·
      refine ⟨5329472413300803234920135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552981608867202156613423 5329472413300803234920135)
      ·
        refine ⟨7994208619951204852380203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329472413300803234920135 7994208619951204852380203)
        ·
          refine ⟨11991312929926807278570305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994208619951204852380203 11991312929926807278570305)
          ·
            refine ⟨8993484697445105458927729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991312929926807278570305 8993484697445105458927729)
            ·
              refine ⟨6745113523083829094195797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993484697445105458927729 6745113523083829094195797)
              ·
                refine ⟨79044299098638622197607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6745113523083829094195797 79044299098638622197607)
                ·
                  rfl

theorem cell22_2078166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2078166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2078166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2078166 prefixEnd_2078166 := by exact prefixLift 2078166
  have htrace : WordTrace (prefixWord ++ tailWord_2078166) baseStart_2078166 baseEnd_2078166 := by
    simpa [prefixWord, tailWord_2078166, baseEnd_2078166] using wordTrace_append hprefix tailTrace_2078166
  have hstable : (prefixWord ++ tailWord_2078166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078166).length < 2 ^ (prefixWord ++ tailWord_2078166).sum := by decide
  have hdescent : baseEnd_2078166 < baseStart_2078166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
