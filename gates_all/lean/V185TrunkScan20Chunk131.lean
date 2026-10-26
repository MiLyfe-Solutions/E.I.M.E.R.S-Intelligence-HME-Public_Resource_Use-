import V185TrunkScan20Chunk130

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_796451 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 2]
def baseStart_796451 : Nat := 118140960795 + 796451 * 2 ^ 59
def prefixEnd_796451 : Nat := 4983230072969 + 3 ^ 40 * 796451 * 2
def baseEnd_796451 : Nat := 363521938448149880444173

theorem tailTrace_796451 : CollatzResearch.WordTrace tailWord_796451 prefixEnd_796451 363521938448149880444173 := by
  unfold tailWord_796451
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048954437601524846565207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19365969625067683231043471 29048954437601524846565207)
  ·
    refine ⟨43573431656402287269847811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048954437601524846565207 43573431656402287269847811)
    ·
      refine ⟨65360147484603430904771717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43573431656402287269847811 65360147484603430904771717)
      ·
        refine ⟨12255027653363143294644697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65360147484603430904771717 12255027653363143294644697)
        ·
          refine ⟨9191270740022357470983523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12255027653363143294644697 9191270740022357470983523)
          ·
            refine ⟨13786906110033536206475285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191270740022357470983523 13786906110033536206475285)
            ·
              refine ⟨646261223907822009678529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13786906110033536206475285 646261223907822009678529)
              ·
                refine ⟨484695917930866507258897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646261223907822009678529 484695917930866507258897)
                ·
                  refine ⟨363521938448149880444173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484695917930866507258897 363521938448149880444173)
                  ·
                    rfl

theorem cell20_796451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2].length) (baseStart_796451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796451 prefixEnd_796451 := by exact prefixLift 796451
  have htrace : WordTrace (prefixWord ++ tailWord_796451) baseStart_796451 baseEnd_796451 := by
    simpa [prefixWord, tailWord_796451, baseEnd_796451] using wordTrace_append hprefix tailTrace_796451
  have hstable : (prefixWord ++ tailWord_796451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796451).length < 2 ^ (prefixWord ++ tailWord_796451).sum := by decide
  have hdescent : baseEnd_796451 < baseStart_796451 := by decide
  rcases family_descends (prefixWord ++ tailWord_796451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796534 : List Nat := [5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_796534 : Nat := 118140960795 + 796534 * 2 ^ 59
def prefixEnd_796534 : Nat := 4983230072969 + 3 ^ 40 * 796534 * 2
def baseEnd_796534 : Nat := 121186607303256826892389

theorem tailTrace_796534 : CollatzResearch.WordTrace tailWord_796534 prefixEnd_796534 121186607303256826892389 := by
  unfold tailWord_796534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815748856018801876364791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19367987797533886681224437 1815748856018801876364791)
  ·
    refine ⟨2723623284028202814547187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815748856018801876364791 2723623284028202814547187)
    ·
      refine ⟨4085434926042304221820781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723623284028202814547187 4085434926042304221820781)
      ·
        refine ⟨1532038097265864083182793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4085434926042304221820781 1532038097265864083182793)
        ·
          refine ⟨1149028572949398062387095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532038097265864083182793 1149028572949398062387095)
          ·
            refine ⟨1723542859424097093580643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149028572949398062387095 1723542859424097093580643)
            ·
              refine ⟨2585314289136145640370965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723542859424097093580643 2585314289136145640370965)
              ·
                refine ⟨121186607303256826892389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2585314289136145640370965 121186607303256826892389)
                ·
                  rfl

theorem cell20_796534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_796534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796534 prefixEnd_796534 := by exact prefixLift 796534
  have htrace : WordTrace (prefixWord ++ tailWord_796534) baseStart_796534 baseEnd_796534 := by
    simpa [prefixWord, tailWord_796534, baseEnd_796534] using wordTrace_append hprefix tailTrace_796534
  have hstable : (prefixWord ++ tailWord_796534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796534).length < 2 ^ (prefixWord ++ tailWord_796534).sum := by decide
  have hdescent : baseEnd_796534 < baseStart_796534 := by decide
  rcases family_descends (prefixWord ++ tailWord_796534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796565 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 2]
def baseStart_796565 : Nat := 118140960795 + 796565 * 2 ^ 59
def prefixEnd_796565 : Nat := 4983230072969 + 3 ^ 40 * 796565 * 2
def baseEnd_796565 : Nat := 363573971154472150643707

theorem tailTrace_796565 : CollatzResearch.WordTrace tailWord_796565 prefixEnd_796565 363573971154472150643707 := by
  unfold tailWord_796565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053112359188522316215149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19368741572792348210810099 29053112359188522316215149)
  ·
    refine ⟨10894917134695695868580681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29053112359188522316215149 10894917134695695868580681)
    ·
      refine ⟨8171187851021771901435511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10894917134695695868580681 8171187851021771901435511)
      ·
        refine ⟨12256781776532657852153267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171187851021771901435511 12256781776532657852153267)
        ·
          refine ⟨18385172664798986778229901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256781776532657852153267 18385172664798986778229901)
          ·
            refine ⟨6894439749299620041836213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18385172664798986778229901 6894439749299620041836213)
            ·
              refine ⟨646353726496839378922145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6894439749299620041836213 646353726496839378922145)
              ·
                refine ⟨484765294872629534191609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646353726496839378922145 484765294872629534191609)
                ·
                  refine ⟨363573971154472150643707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484765294872629534191609 363573971154472150643707)
                  ·
                    rfl

theorem cell20_796565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_796565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796565 prefixEnd_796565 := by exact prefixLift 796565
  have htrace : WordTrace (prefixWord ++ tailWord_796565) baseStart_796565 baseEnd_796565 := by
    simpa [prefixWord, tailWord_796565, baseEnd_796565] using wordTrace_append hprefix tailTrace_796565
  have hstable : (prefixWord ++ tailWord_796565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796565).length < 2 ^ (prefixWord ++ tailWord_796565).sum := by decide
  have hdescent : baseEnd_796565 < baseStart_796565 := by decide
  rcases family_descends (prefixWord ++ tailWord_796565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796569 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_796569 : Nat := 118140960795 + 796569 * 2 ^ 59
def prefixEnd_796569 : Nat := 4983230072969 + 3 ^ 40 * 796569 * 2
def baseEnd_796569 : Nat := 363575796863465914510357

theorem tailTrace_796569 : CollatzResearch.WordTrace tailWord_796569 prefixEnd_796569 363575796863465914510357 := by
  unfold tailWord_796569
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053258251174030999360761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19368838834116020666240507 29053258251174030999360761)
  ·
    refine ⟨21789943688380523249520571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29053258251174030999360761 21789943688380523249520571)
    ·
      refine ⟨32684915532570784874280857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21789943688380523249520571 32684915532570784874280857)
      ·
        refine ⟨24513686649428088655710643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32684915532570784874280857 24513686649428088655710643)
        ·
          refine ⟨36770529974142132983565965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513686649428088655710643 36770529974142132983565965)
          ·
            refine ⟨13788948740303299868837237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36770529974142132983565965 13788948740303299868837237)
            ·
              refine ⟨1292713944403434362703491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13788948740303299868837237 1292713944403434362703491)
              ·
                refine ⟨1939070916605151544055237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292713944403434362703491 1939070916605151544055237)
                ·
                  refine ⟨363575796863465914510357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939070916605151544055237 363575796863465914510357)
                  ·
                    rfl

theorem cell20_796569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_796569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796569 prefixEnd_796569 := by exact prefixLift 796569
  have htrace : WordTrace (prefixWord ++ tailWord_796569) baseStart_796569 baseEnd_796569 := by
    simpa [prefixWord, tailWord_796569, baseEnd_796569] using wordTrace_append hprefix tailTrace_796569
  have hstable : (prefixWord ++ tailWord_796569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796569).length < 2 ^ (prefixWord ++ tailWord_796569).sum := by decide
  have hdescent : baseEnd_796569 < baseStart_796569 := by decide
  rcases family_descends (prefixWord ++ tailWord_796569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796575 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 3]
def baseStart_796575 : Nat := 118140960795 + 796575 * 2 ^ 59
def prefixEnd_796575 : Nat := 4983230072969 + 3 ^ 40 * 796575 * 2
def baseEnd_796575 : Nat := 363578535426956560310333

theorem tailTrace_796575 : CollatzResearch.WordTrace tailWord_796575 prefixEnd_796575 363578535426956560310333 := by
  unfold tailWord_796575
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053477089152294024079179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19368984726101529349386119 29053477089152294024079179)
  ·
    refine ⟨43580215633728441036118769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29053477089152294024079179 43580215633728441036118769)
    ·
      refine ⟨32685161725296330777089077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43580215633728441036118769 32685161725296330777089077)
      ·
        refine ⟨3064233911746531010352101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32685161725296330777089077 3064233911746531010352101)
        ·
          refine ⟨574543858452474564441019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3064233911746531010352101 574543858452474564441019)
          ·
            refine ⟨861815787678711846661529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574543858452474564441019 861815787678711846661529)
            ·
              refine ⟨646361840759033884996147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861815787678711846661529 646361840759033884996147)
              ·
                refine ⟨969542761138550827494221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646361840759033884996147 969542761138550827494221)
                ·
                  refine ⟨363578535426956560310333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969542761138550827494221 363578535426956560310333)
                  ·
                    rfl

theorem cell20_796575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3].length) (baseStart_796575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796575 prefixEnd_796575 := by exact prefixLift 796575
  have htrace : WordTrace (prefixWord ++ tailWord_796575) baseStart_796575 baseEnd_796575 := by
    simpa [prefixWord, tailWord_796575, baseEnd_796575] using wordTrace_append hprefix tailTrace_796575
  have hstable : (prefixWord ++ tailWord_796575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796575).length < 2 ^ (prefixWord ++ tailWord_796575).sum := by decide
  have hdescent : baseEnd_796575 < baseStart_796575 := by decide
  rcases family_descends (prefixWord ++ tailWord_796575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796620 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_796620 : Nat := 118140960795 + 796620 * 2 ^ 59
def prefixEnd_796620 : Nat := 4983230072969 + 3 ^ 40 * 796620 * 2
def baseEnd_796620 : Nat := 363599074653136403810149

theorem tailTrace_796620 : CollatzResearch.WordTrace tailWord_796620 prefixEnd_796620 363599074653136403810149 := by
  unfold tailWord_796620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527559186994633354733657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19370078915992844472978209 14527559186994633354733657)
  ·
    refine ⟨10895669390245975016050243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14527559186994633354733657 10895669390245975016050243)
    ·
      refine ⟨16343504085368962524075365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895669390245975016050243 16343504085368962524075365)
      ·
        refine ⟨3064407016006680473264131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16343504085368962524075365 3064407016006680473264131)
        ·
          refine ⟨4596610524010020709896197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064407016006680473264131 4596610524010020709896197)
          ·
            refine ⟨861864473251878883105537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4596610524010020709896197 861864473251878883105537)
            ·
              refine ⟨646398354938909162329153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861864473251878883105537 646398354938909162329153)
              ·
                refine ⟨484798766204181871746865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646398354938909162329153 484798766204181871746865)
                ·
                  refine ⟨363599074653136403810149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484798766204181871746865 363599074653136403810149)
                  ·
                    rfl

theorem cell20_796620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_796620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796620 prefixEnd_796620 := by exact prefixLift 796620
  have htrace : WordTrace (prefixWord ++ tailWord_796620) baseStart_796620 baseEnd_796620 := by
    simpa [prefixWord, tailWord_796620, baseEnd_796620] using wordTrace_append hprefix tailTrace_796620
  have hstable : (prefixWord ++ tailWord_796620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796620).length < 2 ^ (prefixWord ++ tailWord_796620).sum := by decide
  have hdescent : baseEnd_796620 < baseStart_796620 := by decide
  rcases family_descends (prefixWord ++ tailWord_796620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796683 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_796683 : Nat := 118140960795 + 796683 * 2 ^ 59
def prefixEnd_796683 : Nat := 4983230072969 + 3 ^ 40 * 796683 * 2
def baseEnd_796683 : Nat := 363627829569788184709891

theorem tailTrace_796683 : CollatzResearch.WordTrace tailWord_796683 prefixEnd_796683 363627829569788184709891 := by
  unfold tailWord_796683
  simp only [CollatzResearch.WordTrace]
  refine ⟨29057416172761028469010703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19371610781840685646007135 29057416172761028469010703)
  ·
    refine ⟨43586124259141542703516055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29057416172761028469010703 43586124259141542703516055)
    ·
      refine ⟨65379186388712314055274083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43586124259141542703516055 65379186388712314055274083)
      ·
        refine ⟨98068779583068471082911125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65379186388712314055274083 98068779583068471082911125)
        ·
          refine ⟨4596974042956334582011459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98068779583068471082911125 4596974042956334582011459)
          ·
            refine ⟨6895461064434501873017189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596974042956334582011459 6895461064434501873017189)
            ·
              refine ⟨1292898949581469101190723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6895461064434501873017189 1292898949581469101190723)
              ·
                refine ⟨1939348424372203651786085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292898949581469101190723 1939348424372203651786085)
                ·
                  refine ⟨363627829569788184709891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939348424372203651786085 363627829569788184709891)
                  ·
                    rfl

theorem cell20_796683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_796683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796683 prefixEnd_796683 := by exact prefixLift 796683
  have htrace : WordTrace (prefixWord ++ tailWord_796683) baseStart_796683 baseEnd_796683 := by
    simpa [prefixWord, tailWord_796683, baseEnd_796683] using wordTrace_append hprefix tailTrace_796683
  have hstable : (prefixWord ++ tailWord_796683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796683).length < 2 ^ (prefixWord ++ tailWord_796683).sum := by decide
  have hdescent : baseEnd_796683 < baseStart_796683 := by decide
  rcases family_descends (prefixWord ++ tailWord_796683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796714 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_796714 : Nat := 118140960795 + 796714 * 2 ^ 59
def prefixEnd_796714 : Nat := 4983230072969 + 3 ^ 40 * 796714 * 2
def baseEnd_796714 : Nat := 363641978814489854676431

theorem tailTrace_796714 : CollatzResearch.WordTrace tailWord_796714 prefixEnd_796714 363641978814489854676431 := by
  unfold tailWord_796714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264636708912180190847299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19372364557099147175592797 7264636708912180190847299)
  ·
    refine ⟨10896955063368270286270949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264636708912180190847299 10896955063368270286270949)
    ·
      refine ⟨2043179074381550678675803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10896955063368270286270949 2043179074381550678675803)
      ·
        refine ⟨3064768611572326018013705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043179074381550678675803 3064768611572326018013705)
        ·
          refine ⟨2298576458679244513510279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064768611572326018013705 2298576458679244513510279)
          ·
            refine ⟨3447864688018866770265419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298576458679244513510279 3447864688018866770265419)
            ·
              refine ⟨5171797032028300155398129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447864688018866770265419 5171797032028300155398129)
              ·
                refine ⟨3878847774021225116548597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171797032028300155398129 3878847774021225116548597)
                ·
                  refine ⟨363641978814489854676431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878847774021225116548597 363641978814489854676431)
                  ·
                    rfl

theorem cell20_796714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_796714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796714 prefixEnd_796714 := by exact prefixLift 796714
  have htrace : WordTrace (prefixWord ++ tailWord_796714) baseStart_796714 baseEnd_796714 := by
    simpa [prefixWord, tailWord_796714, baseEnd_796714] using wordTrace_append hprefix tailTrace_796714
  have hstable : (prefixWord ++ tailWord_796714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796714).length < 2 ^ (prefixWord ++ tailWord_796714).sum := by decide
  have hdescent : baseEnd_796714 < baseStart_796714 := by decide
  rcases family_descends (prefixWord ++ tailWord_796714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796724 : List Nat := [2, 5, 1, 2, 2, 2, 6]
def baseStart_796724 : Nat := 118140960795 + 796724 * 2 ^ 59
def prefixEnd_796724 : Nat := 4983230072969 + 3 ^ 40 * 796724 * 2
def baseEnd_796724 : Nat := 40405171454108251593673

theorem tailTrace_796724 : CollatzResearch.WordTrace tailWord_796724 prefixEnd_796724 40405171454108251593673 := by
  unfold tailWord_796724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14529455782806246235626613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19372607710408328314168817 14529455782806246235626613)
  ·
    refine ⟨1362136479638085584589995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14529455782806246235626613 1362136479638085584589995)
    ·
      refine ⟨2043204719457128376884993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362136479638085584589995 2043204719457128376884993)
      ·
        refine ⟨1532403539592846282663745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043204719457128376884993 1532403539592846282663745)
        ·
          refine ⟨1149302654694634711997809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532403539592846282663745 1149302654694634711997809)
          ·
            refine ⟨861976991020976033998357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149302654694634711997809 861976991020976033998357)
            ·
              refine ⟨40405171454108251593673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 861976991020976033998357 40405171454108251593673)
              ·
                rfl

theorem cell20_796724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_796724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796724 prefixEnd_796724 := by exact prefixLift 796724
  have htrace : WordTrace (prefixWord ++ tailWord_796724) baseStart_796724 baseEnd_796724 := by
    simpa [prefixWord, tailWord_796724, baseEnd_796724] using wordTrace_append hprefix tailTrace_796724
  have hstable : (prefixWord ++ tailWord_796724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796724).length < 2 ^ (prefixWord ++ tailWord_796724).sum := by decide
  have hdescent : baseEnd_796724 < baseStart_796724 := by decide
  rcases family_descends (prefixWord ++ tailWord_796724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796734 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_796734 : Nat := 118140960795 + 796734 * 2 ^ 59
def prefixEnd_796734 : Nat := 4983230072969 + 3 ^ 40 * 796734 * 2
def baseEnd_796734 : Nat := 363651107359458674009683

theorem tailTrace_796734 : CollatzResearch.WordTrace tailWord_796734 prefixEnd_796734 363651107359458674009683 := by
  unfold tailWord_796734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632409536947033022389657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19372850863717509452744837 3632409536947033022389657)
  ·
    refine ⟨2724307152710274766792243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632409536947033022389657 2724307152710274766792243)
    ·
      refine ⟨4086460729065412150188365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724307152710274766792243 4086460729065412150188365)
      ·
        refine ⟨1532422773399529556320637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4086460729065412150188365 1532422773399529556320637)
        ·
          refine ⟨574658540024823583620239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1532422773399529556320637 574658540024823583620239)
          ·
            refine ⟨861987810037235375430359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574658540024823583620239 861987810037235375430359)
            ·
              refine ⟨1292981715055853063145539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861987810037235375430359 1292981715055853063145539)
              ·
                refine ⟨1939472572583779594718309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292981715055853063145539 1939472572583779594718309)
                ·
                  refine ⟨363651107359458674009683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939472572583779594718309 363651107359458674009683)
                  ·
                    rfl

theorem cell20_796734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_796734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796734 prefixEnd_796734 := by exact prefixLift 796734
  have htrace : WordTrace (prefixWord ++ tailWord_796734) baseStart_796734 baseEnd_796734 := by
    simpa [prefixWord, tailWord_796734, baseEnd_796734] using wordTrace_append hprefix tailTrace_796734
  have hstable : (prefixWord ++ tailWord_796734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796734).length < 2 ^ (prefixWord ++ tailWord_796734).sum := by decide
  have hdescent : baseEnd_796734 < baseStart_796734 := by decide
  rcases family_descends (prefixWord ++ tailWord_796734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796735 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_796735 : Nat := 118140960795 + 796735 * 2 ^ 59
def prefixEnd_796735 : Nat := 4983230072969 + 3 ^ 40 * 796735 * 2
def baseEnd_796735 : Nat := 363651563786707114976345

theorem tailTrace_796735 : CollatzResearch.WordTrace tailWord_796735 prefixEnd_796735 363651563786707114976345 := by
  unfold tailWord_796735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059312768572641349903659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372875179048427566602439 29059312768572641349903659)
  ·
    refine ⟨43588969152858962024855489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29059312768572641349903659 43588969152858962024855489)
    ·
      refine ⟨32691726864644221518641617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43588969152858962024855489 32691726864644221518641617)
      ·
        refine ⟨24518795148483166138981213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32691726864644221518641617 24518795148483166138981213)
        ·
          refine ⟨9194548180681187302117955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24518795148483166138981213 9194548180681187302117955)
          ·
            refine ⟨13791822271021780953176933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194548180681187302117955 13791822271021780953176933)
            ·
              refine ⟨2585966675816583928720675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13791822271021780953176933 2585966675816583928720675)
              ·
                refine ⟨3878950013724875893081013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585966675816583928720675 3878950013724875893081013)
                ·
                  refine ⟨363651563786707114976345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3878950013724875893081013 363651563786707114976345)
                  ·
                    rfl

theorem cell20_796735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_796735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796735 prefixEnd_796735 := by exact prefixLift 796735
  have htrace : WordTrace (prefixWord ++ tailWord_796735) baseStart_796735 baseEnd_796735 := by
    simpa [prefixWord, tailWord_796735, baseEnd_796735] using wordTrace_append hprefix tailTrace_796735
  have hstable : (prefixWord ++ tailWord_796735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796735).length < 2 ^ (prefixWord ++ tailWord_796735).sum := by decide
  have hdescent : baseEnd_796735 < baseStart_796735 := by decide
  rcases family_descends (prefixWord ++ tailWord_796735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796793 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 2]
def baseStart_796793 : Nat := 118140960795 + 796793 * 2 ^ 59
def prefixEnd_796793 : Nat := 4983230072969 + 3 ^ 40 * 796793 * 2
def baseEnd_796793 : Nat := 363678036567116691042775

theorem tailTrace_796793 : CollatzResearch.WordTrace tailWord_796793 prefixEnd_796793 363678036567116691042775 := by
  unfold tailWord_796793
  simp only [CollatzResearch.WordTrace]
  refine ⟨29061428202362517255515033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19374285468241678170343355 29061428202362517255515033)
  ·
    refine ⟨21796071151771887941636275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29061428202362517255515033 21796071151771887941636275)
    ·
      refine ⟨32694106727657831912454413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21796071151771887941636275 32694106727657831912454413)
      ·
        refine ⟨12260290022871686967170405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32694106727657831912454413 12260290022871686967170405)
        ·
          refine ⟨2298804379288441306344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12260290022871686967170405 2298804379288441306344451)
          ·
            refine ⟨3448206568932661959516677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298804379288441306344451 3448206568932661959516677)
            ·
              refine ⟨646538731674874117409377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3448206568932661959516677 646538731674874117409377)
              ·
                refine ⟨484904048756155588057033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646538731674874117409377 484904048756155588057033)
                ·
                  refine ⟨363678036567116691042775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484904048756155588057033 363678036567116691042775)
                  ·
                    rfl

theorem cell20_796793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_796793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796793 prefixEnd_796793 := by exact prefixLift 796793
  have htrace : WordTrace (prefixWord ++ tailWord_796793) baseStart_796793 baseEnd_796793 := by
    simpa [prefixWord, tailWord_796793, baseEnd_796793] using wordTrace_append hprefix tailTrace_796793
  have hstable : (prefixWord ++ tailWord_796793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796793).length < 2 ^ (prefixWord ++ tailWord_796793).sum := by decide
  have hdescent : baseEnd_796793 < baseStart_796793 := by decide
  rcases family_descends (prefixWord ++ tailWord_796793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796814 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_796814 : Nat := 118140960795 + 796814 * 2 ^ 59
def prefixEnd_796814 : Nat := 4983230072969 + 3 ^ 40 * 796814 * 2
def baseEnd_796814 : Nat := 363687621539333951342689

theorem tailTrace_796814 : CollatzResearch.WordTrace tailWord_796814 prefixEnd_796814 363687621539333951342689 := by
  unfold tailWord_796814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632774266910804730253687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19374796090190958561352997 3632774266910804730253687)
  ·
    refine ⟨5449161400366207095380531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632774266910804730253687 5449161400366207095380531)
    ·
      refine ⟨8173742100549310643070797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449161400366207095380531 8173742100549310643070797)
      ·
        refine ⟨3065153287705991491151549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8173742100549310643070797 3065153287705991491151549)
        ·
          refine ⟨1149432482889746809181831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3065153287705991491151549 1149432482889746809181831)
          ·
            refine ⟨1724148724334620213772747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149432482889746809181831 1724148724334620213772747)
            ·
              refine ⟨2586223086501930320659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724148724334620213772747 2586223086501930320659121)
              ·
                refine ⟨1939667314876447740494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586223086501930320659121 1939667314876447740494341)
                ·
                  refine ⟨363687621539333951342689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939667314876447740494341 363687621539333951342689)
                  ·
                    rfl

theorem cell20_796814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_796814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796814 prefixEnd_796814 := by exact prefixLift 796814
  have htrace : WordTrace (prefixWord ++ tailWord_796814) baseStart_796814 baseEnd_796814 := by
    simpa [prefixWord, tailWord_796814, baseEnd_796814] using wordTrace_append hprefix tailTrace_796814
  have hstable : (prefixWord ++ tailWord_796814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796814).length < 2 ^ (prefixWord ++ tailWord_796814).sum := by decide
  have hdescent : baseEnd_796814 < baseStart_796814 := by decide
  rcases family_descends (prefixWord ++ tailWord_796814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796825 : List Nat := [1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_796825 : Nat := 118140960795 + 796825 * 2 ^ 59
def prefixEnd_796825 : Nat := 4983230072969 + 3 ^ 40 * 796825 * 2
def baseEnd_796825 : Nat := 121230880746355600658659

theorem tailTrace_796825 : CollatzResearch.WordTrace tailWord_796825 prefixEnd_796825 121230880746355600658659 := by
  unfold tailWord_796825
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062595338246586720679929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375063558831057813786619 29062595338246586720679929)
  ·
    refine ⟨21796946503684940040509947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29062595338246586720679929 21796946503684940040509947)
    ·
      refine ⟨32695419755527410060764921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21796946503684940040509947 32695419755527410060764921)
      ·
        refine ⟨24521564816645557545573691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32695419755527410060764921 24521564816645557545573691)
        ·
          refine ⟨36782347224968336318360537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24521564816645557545573691 36782347224968336318360537)
          ·
            refine ⟨27586760418726252238770403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36782347224968336318360537 27586760418726252238770403)
            ·
              refine ⟨41380140628089378358155605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27586760418726252238770403 41380140628089378358155605)
              ·
                refine ⟨121230880746355600658659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41380140628089378358155605 121230880746355600658659)
                ·
                  rfl

theorem cell20_796825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_796825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796825 prefixEnd_796825 := by exact prefixLift 796825
  have htrace : WordTrace (prefixWord ++ tailWord_796825) baseStart_796825 baseEnd_796825 := by
    simpa [prefixWord, tailWord_796825, baseEnd_796825] using wordTrace_append hprefix tailTrace_796825
  have hstable : (prefixWord ++ tailWord_796825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796825).length < 2 ^ (prefixWord ++ tailWord_796825).sum := by decide
  have hdescent : baseEnd_796825 < baseStart_796825 := by decide
  rcases family_descends (prefixWord ++ tailWord_796825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796831 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 2]
def baseStart_796831 : Nat := 118140960795 + 796831 * 2 ^ 59
def prefixEnd_796831 : Nat := 4983230072969 + 3 ^ 40 * 796831 * 2
def baseEnd_796831 : Nat := 363695380802557447775953

theorem tailTrace_796831 : CollatzResearch.WordTrace tailWord_796831 prefixEnd_796831 363695380802557447775953 := by
  unfold tailWord_796831
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062814176224849745398347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375209450816566496932231 29062814176224849745398347)
  ·
    refine ⟨43594221264337274618097521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29062814176224849745398347 43594221264337274618097521)
    ·
      refine ⟨32695665948252955963573141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43594221264337274618097521 32695665948252955963573141)
      ·
        refine ⟨1532609341324357310792491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32695665948252955963573141 1532609341324357310792491)
        ·
          refine ⟨2298914011986535966188737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532609341324357310792491 2298914011986535966188737)
          ·
            refine ⟨1724185508989901974641553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298914011986535966188737 1724185508989901974641553)
            ·
              refine ⟨1293139131742426480981165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724185508989901974641553 1293139131742426480981165)
              ·
                refine ⟨484927174403409930367937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293139131742426480981165 484927174403409930367937)
                ·
                  refine ⟨363695380802557447775953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484927174403409930367937 363695380802557447775953)
                  ·
                    rfl

theorem cell20_796831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2].length) (baseStart_796831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796831 prefixEnd_796831 := by exact prefixLift 796831
  have htrace : WordTrace (prefixWord ++ tailWord_796831) baseStart_796831 baseEnd_796831 := by
    simpa [prefixWord, tailWord_796831, baseEnd_796831] using wordTrace_append hprefix tailTrace_796831
  have hstable : (prefixWord ++ tailWord_796831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796831).length < 2 ^ (prefixWord ++ tailWord_796831).sum := by decide
  have hdescent : baseEnd_796831 < baseStart_796831 := by decide
  rcases family_descends (prefixWord ++ tailWord_796831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796845 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_796845 : Nat := 118140960795 + 796845 * 2 ^ 59
def prefixEnd_796845 : Nat := 4983230072969 + 3 ^ 40 * 796845 * 2
def baseEnd_796845 : Nat := 363701770784035621309229

theorem tailTrace_796845 : CollatzResearch.WordTrace tailWord_796845 prefixEnd_796845 363701770784035621309229 := by
  unfold tailWord_796845
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063324798174130136407989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375549865449420090938659 29063324798174130136407989)
  ·
    refine ⟨2724686699828824700288249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29063324798174130136407989 2724686699828824700288249)
    ·
      refine ⟨2043515024871618525216187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2724686699828824700288249 2043515024871618525216187)
      ·
        refine ⟨3065272537307427787824281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043515024871618525216187 3065272537307427787824281)
        ·
          refine ⟨2298954402980570840868211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3065272537307427787824281 2298954402980570840868211)
          ·
            refine ⟨3448431604470856261302317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298954402980570840868211 3448431604470856261302317)
            ·
              refine ⟨1293161851676571097988369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3448431604470856261302317 1293161851676571097988369)
              ·
                refine ⟨969871388757428323491277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293161851676571097988369 969871388757428323491277)
                ·
                  refine ⟨363701770784035621309229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969871388757428323491277 363701770784035621309229)
                  ·
                    rfl

theorem cell20_796845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_796845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796845 prefixEnd_796845 := by exact prefixLift 796845
  have htrace : WordTrace (prefixWord ++ tailWord_796845) baseStart_796845 baseEnd_796845 := by
    simpa [prefixWord, tailWord_796845, baseEnd_796845] using wordTrace_append hprefix tailTrace_796845
  have hstable : (prefixWord ++ tailWord_796845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796845).length < 2 ^ (prefixWord ++ tailWord_796845).sum := by decide
  have hdescent : baseEnd_796845 < baseStart_796845 := by decide
  rcases family_descends (prefixWord ++ tailWord_796845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796862 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_796862 : Nat := 118140960795 + 796862 * 2 ^ 59
def prefixEnd_796862 : Nat := 4983230072969 + 3 ^ 40 * 796862 * 2
def baseEnd_796862 : Nat := 363709530047259117742493

theorem tailTrace_796862 : CollatzResearch.WordTrace tailWord_796862 prefixEnd_796862 363709530047259117742493 := by
  unfold tailWord_796862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632993104889067754972105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19375963226075028026517893 3632993104889067754972105)
  ·
    refine ⟨2724744828666800816229079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632993104889067754972105 2724744828666800816229079)
    ·
      refine ⟨4087117243000201224343619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724744828666800816229079 4087117243000201224343619)
      ·
        refine ⟨6130675864500301836515429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087117243000201224343619 6130675864500301836515429)
        ·
          refine ⟨1149501724593806594346643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6130675864500301836515429 1149501724593806594346643)
          ·
            refine ⟨1724252586890709891519965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149501724593806594346643 1724252586890709891519965)
            ·
              refine ⟨646594720084016209319987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1724252586890709891519965 646594720084016209319987)
              ·
                refine ⟨969892080126024313979981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646594720084016209319987 969892080126024313979981)
                ·
                  refine ⟨363709530047259117742493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969892080126024313979981 363709530047259117742493)
                  ·
                    rfl

theorem cell20_796862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_796862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796862 prefixEnd_796862 := by exact prefixLift 796862
  have htrace : WordTrace (prefixWord ++ tailWord_796862) baseStart_796862 baseEnd_796862 := by
    simpa [prefixWord, tailWord_796862, baseEnd_796862] using wordTrace_append hprefix tailTrace_796862
  have hstable : (prefixWord ++ tailWord_796862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796862).length < 2 ^ (prefixWord ++ tailWord_796862).sum := by decide
  have hdescent : baseEnd_796862 < baseStart_796862 := by decide
  rcases family_descends (prefixWord ++ tailWord_796862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796863 : List Nat := [1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_796863 : Nat := 118140960795 + 796863 * 2 ^ 59
def prefixEnd_796863 : Nat := 4983230072969 + 3 ^ 40 * 796863 * 2
def baseEnd_796863 : Nat := 121236662158169186236385

theorem tailTrace_796863 : CollatzResearch.WordTrace tailWord_796863 prefixEnd_796863 121236662158169186236385 := by
  unfold tailWord_796863
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063981312108919210563243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375987541405946140375495 29063981312108919210563243)
  ·
    refine ⟨43595971968163378815844865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29063981312108919210563243 43595971968163378815844865)
    ·
      refine ⟨32696978976122534111883649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43595971968163378815844865 32696978976122534111883649)
      ·
        refine ⟨24522734232091900583912737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32696978976122534111883649 24522734232091900583912737)
        ·
          refine ⟨18392050674068925437934553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24522734232091900583912737 18392050674068925437934553)
          ·
            refine ⟨13794038005551694078450915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18392050674068925437934553 13794038005551694078450915)
            ·
              refine ⟨20691057008327541117676373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13794038005551694078450915 20691057008327541117676373)
              ·
                refine ⟨121236662158169186236385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20691057008327541117676373 121236662158169186236385)
                ·
                  rfl

theorem cell20_796863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_796863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796863 prefixEnd_796863 := by exact prefixLift 796863
  have htrace : WordTrace (prefixWord ++ tailWord_796863) baseStart_796863 baseEnd_796863 := by
    simpa [prefixWord, tailWord_796863, baseEnd_796863] using wordTrace_append hprefix tailTrace_796863
  have hstable : (prefixWord ++ tailWord_796863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796863).length < 2 ^ (prefixWord ++ tailWord_796863).sum := by decide
  have hdescent : baseEnd_796863 < baseStart_796863 := by decide
  rcases family_descends (prefixWord ++ tailWord_796863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796886 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_796886 : Nat := 118140960795 + 796886 * 2 ^ 59
def prefixEnd_796886 : Nat := 4983230072969 + 3 ^ 40 * 796886 * 2
def baseEnd_796886 : Nat := 363720484301221700942395

theorem tailTrace_796886 : CollatzResearch.WordTrace tailWord_796886 prefixEnd_796886 363720484301221700942395 := by
  unfold tailWord_796886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816551261939099633665657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19376546794017062759100341 1816551261939099633665657)
  ·
    refine ⟨1362413446454324725249243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1816551261939099633665657 1362413446454324725249243)
    ·
      refine ⟨2043620169681487087873865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362413446454324725249243 2043620169681487087873865)
      ·
        refine ⟨1532715127261115315905399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043620169681487087873865 1532715127261115315905399)
        ·
          refine ⟨2299072690891672973858099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532715127261115315905399 2299072690891672973858099)
          ·
            refine ⟨3448609036337509460787149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299072690891672973858099 3448609036337509460787149)
            ·
              refine ⟨1293228388626566047795181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3448609036337509460787149 1293228388626566047795181)
              ·
                refine ⟨484960645734962267923193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293228388626566047795181 484960645734962267923193)
                ·
                  refine ⟨363720484301221700942395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484960645734962267923193 363720484301221700942395)
                  ·
                    rfl

theorem cell20_796886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_796886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796886 prefixEnd_796886 := by exact prefixLift 796886
  have htrace : WordTrace (prefixWord ++ tailWord_796886) baseStart_796886 baseEnd_796886 := by
    simpa [prefixWord, tailWord_796886, baseEnd_796886] using wordTrace_append hprefix tailTrace_796886
  have hstable : (prefixWord ++ tailWord_796886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796886).length < 2 ^ (prefixWord ++ tailWord_796886).sum := by decide
  have hdescent : baseEnd_796886 < baseStart_796886 := by decide
  rcases family_descends (prefixWord ++ tailWord_796886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796890 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_796890 : Nat := 118140960795 + 796890 * 2 ^ 59
def prefixEnd_796890 : Nat := 4983230072969 + 3 ^ 40 * 796890 * 2
def baseEnd_796890 : Nat := 363722310010215464809045

theorem tailTrace_796890 : CollatzResearch.WordTrace tailWord_796890 prefixEnd_796890 363722310010215464809045 := by
  unfold tailWord_796890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266241520752775705449031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19376644055340735214530749 7266241520752775705449031)
  ·
    refine ⟨10899362281129163558173547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266241520752775705449031 10899362281129163558173547)
    ·
      refine ⟨16349043421693745337260321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10899362281129163558173547 16349043421693745337260321)
      ·
        refine ⟨12261782566270309002945241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16349043421693745337260321 12261782566270309002945241)
        ·
          refine ⟨9196336924702731752208931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12261782566270309002945241 9196336924702731752208931)
          ·
            refine ⟨13794505387054097628313397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196336924702731752208931 13794505387054097628313397)
            ·
              refine ⟨1293234880036321652654381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13794505387054097628313397 1293234880036321652654381)
              ·
                refine ⟨484963080013620619745393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293234880036321652654381 484963080013620619745393)
                ·
                  refine ⟨363722310010215464809045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484963080013620619745393 363722310010215464809045)
                  ·
                    rfl

theorem cell20_796890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_796890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796890 prefixEnd_796890 := by exact prefixLift 796890
  have htrace : WordTrace (prefixWord ++ tailWord_796890) baseStart_796890 baseEnd_796890 := by
    simpa [prefixWord, tailWord_796890, baseEnd_796890] using wordTrace_append hprefix tailTrace_796890
  have hstable : (prefixWord ++ tailWord_796890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796890).length < 2 ^ (prefixWord ++ tailWord_796890).sum := by decide
  have hdescent : baseEnd_796890 < baseStart_796890 := by decide
  rcases family_descends (prefixWord ++ tailWord_796890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796911 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_796911 : Nat := 118140960795 + 796911 * 2 ^ 59
def prefixEnd_796911 : Nat := 4983230072969 + 3 ^ 40 * 796911 * 2
def baseEnd_796911 : Nat := 363731894982432725108959

theorem tailTrace_796911 : CollatzResearch.WordTrace tailWord_796911 prefixEnd_796911 363731894982432725108959 := by
  unfold tailWord_796911
  simp only [CollatzResearch.WordTrace]
  refine ⟨29065732015935023408310587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19377154677290015605540391 29065732015935023408310587)
  ·
    refine ⟨43598598023902535112465881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29065732015935023408310587 43598598023902535112465881)
    ·
      refine ⟨32698948517926901334349411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43598598023902535112465881 32698948517926901334349411)
      ·
        refine ⟨49048422776890352001524117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32698948517926901334349411 49048422776890352001524117)
        ·
          refine ⟨2299144817666735250071443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49048422776890352001524117 2299144817666735250071443)
          ·
            refine ⟨3448717226500102875107165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299144817666735250071443 3448717226500102875107165)
            ·
              refine ⟨1293268959937538578165187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3448717226500102875107165 1293268959937538578165187)
              ·
                refine ⟨1939903439906307867247781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293268959937538578165187 1939903439906307867247781)
                ·
                  refine ⟨363731894982432725108959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1939903439906307867247781 363731894982432725108959)
                  ·
                    rfl

theorem cell20_796911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_796911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796911 prefixEnd_796911 := by exact prefixLift 796911
  have htrace : WordTrace (prefixWord ++ tailWord_796911) baseStart_796911 baseEnd_796911 := by
    simpa [prefixWord, tailWord_796911, baseEnd_796911] using wordTrace_append hprefix tailTrace_796911
  have hstable : (prefixWord ++ tailWord_796911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796911).length < 2 ^ (prefixWord ++ tailWord_796911).sum := by decide
  have hdescent : baseEnd_796911 < baseStart_796911 := by decide
  rcases family_descends (prefixWord ++ tailWord_796911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796918 : List Nat := [5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_796918 : Nat := 118140960795 + 796918 * 2 ^ 59
def prefixEnd_796918 : Nat := 4983230072969 + 3 ^ 40 * 796918 * 2
def baseEnd_796918 : Nat := 121245029991057270625199

theorem tailTrace_796918 : CollatzResearch.WordTrace tailWord_796918 prefixEnd_796918 121245029991057270625199 := by
  unfold tailWord_796918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816624207931853975238463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19377324884606442402543605 1816624207931853975238463)
  ·
    refine ⟨2724936311897780962857695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816624207931853975238463 2724936311897780962857695)
    ·
      refine ⟨4087404467846671444286543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724936311897780962857695 4087404467846671444286543)
      ·
        refine ⟨6131106701770007166429815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087404467846671444286543 6131106701770007166429815)
        ·
          refine ⟨9196660052655010749644723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131106701770007166429815 9196660052655010749644723)
          ·
            refine ⟨13794990078982516124467085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196660052655010749644723 13794990078982516124467085)
            ·
              refine ⟨5173121279618443546675157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13794990078982516124467085 5173121279618443546675157)
              ·
                refine ⟨121245029991057270625199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5173121279618443546675157 121245029991057270625199)
                ·
                  rfl

theorem cell20_796918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_796918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796918 prefixEnd_796918 := by exact prefixLift 796918
  have htrace : WordTrace (prefixWord ++ tailWord_796918) baseStart_796918 baseEnd_796918 := by
    simpa [prefixWord, tailWord_796918, baseEnd_796918] using wordTrace_append hprefix tailTrace_796918
  have hstable : (prefixWord ++ tailWord_796918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796918).length < 2 ^ (prefixWord ++ tailWord_796918).sum := by decide
  have hdescent : baseEnd_796918 < baseStart_796918 := by decide
  rcases family_descends (prefixWord ++ tailWord_796918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796939 : List Nat := [1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_796939 : Nat := 118140960795 + 796939 * 2 ^ 59
def prefixEnd_796939 : Nat := 4983230072969 + 3 ^ 40 * 796939 * 2
def baseEnd_796939 : Nat := 121248224981796357391837

theorem tailTrace_796939 : CollatzResearch.WordTrace tailWord_796939 prefixEnd_796939 121248224981796357391837 := by
  unfold tailWord_796939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29066753259833584190329871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19377835506555722793553247 29066753259833584190329871)
  ·
    refine ⟨43600129889750376285494807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29066753259833584190329871 43600129889750376285494807)
    ·
      refine ⟨65400194834625564428242211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43600129889750376285494807 65400194834625564428242211)
      ·
        refine ⟨98100292251938346642363317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65400194834625564428242211 98100292251938346642363317)
        ·
          refine ⟨9196902398619219997721561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98100292251938346642363317 9196902398619219997721561)
          ·
            refine ⟨6897676798964414998291171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9196902398619219997721561 6897676798964414998291171)
            ·
              refine ⟨10346515198446622497436757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897676798964414998291171 10346515198446622497436757)
              ·
                refine ⟨121248224981796357391837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10346515198446622497436757 121248224981796357391837)
                ·
                  rfl

theorem cell20_796939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_796939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796939 prefixEnd_796939 := by exact prefixLift 796939
  have htrace : WordTrace (prefixWord ++ tailWord_796939) baseStart_796939 baseEnd_796939 := by
    simpa [prefixWord, tailWord_796939, baseEnd_796939] using wordTrace_append hprefix tailTrace_796939
  have hstable : (prefixWord ++ tailWord_796939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796939).length < 2 ^ (prefixWord ++ tailWord_796939).sum := by decide
  have hdescent : baseEnd_796939 < baseStart_796939 := by decide
  rcases family_descends (prefixWord ++ tailWord_796939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796962 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_796962 : Nat := 118140960795 + 796962 * 2 ^ 59
def prefixEnd_796962 : Nat := 4983230072969 + 3 ^ 40 * 796962 * 2
def baseEnd_796962 : Nat := 363755172772103214408751

theorem tailTrace_796962 : CollatzResearch.WordTrace tailWord_796962 prefixEnd_796962 363755172772103214408751 := by
  unfold tailWord_796962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266898034687564779604285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19378394759166839412278093 7266898034687564779604285)
  ·
    refine ⟨2725086763007836792351607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7266898034687564779604285 2725086763007836792351607)
    ·
      refine ⟨4087630144511755188527411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725086763007836792351607 4087630144511755188527411)
      ·
        refine ⟨6131445216767632782791117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087630144511755188527411 6131445216767632782791117)
        ·
          refine ⟨2299291956287862293546669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6131445216767632782791117 2299291956287862293546669)
          ·
            refine ⟨862234483607948360080001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2299291956287862293546669 862234483607948360080001)
            ·
              refine ⟨646675862705961270060001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862234483607948360080001 646675862705961270060001)
              ·
                refine ⟨485006897029470952545001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646675862705961270060001 485006897029470952545001)
                ·
                  refine ⟨363755172772103214408751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485006897029470952545001 363755172772103214408751)
                  ·
                    rfl

theorem cell20_796962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_796962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796962 prefixEnd_796962 := by exact prefixLift 796962
  have htrace : WordTrace (prefixWord ++ tailWord_796962) baseStart_796962 baseEnd_796962 := by
    simpa [prefixWord, tailWord_796962, baseEnd_796962] using wordTrace_append hprefix tailTrace_796962
  have hstable : (prefixWord ++ tailWord_796962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796962).length < 2 ^ (prefixWord ++ tailWord_796962).sum := by decide
  have hdescent : baseEnd_796962 < baseStart_796962 := by decide
  rcases family_descends (prefixWord ++ tailWord_796962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797004 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_797004 : Nat := 118140960795 + 797004 * 2 ^ 59
def prefixEnd_797004 : Nat := 4983230072969 + 3 ^ 40 * 797004 * 2
def baseEnd_797004 : Nat := 363774342716537735008579

theorem tailTrace_797004 : CollatzResearch.WordTrace tailWord_797004 prefixEnd_797004 363774342716537735008579 := by
  unfold tailWord_797004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534562002299050145723033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19379416003065400194297377 14534562002299050145723033)
  ·
    refine ⟨10900921501724287609292275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14534562002299050145723033 10900921501724287609292275)
    ·
      refine ⟨16351382252586431413938413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900921501724287609292275 16351382252586431413938413)
      ·
        refine ⟨6131768344719911780226905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16351382252586431413938413 6131768344719911780226905)
        ·
          refine ⟨4598826258539933835170179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6131768344719911780226905 4598826258539933835170179)
          ·
            refine ⟨6898239387809900752755269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598826258539933835170179 6898239387809900752755269)
            ·
              refine ⟨1293419885214356391141613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6898239387809900752755269 1293419885214356391141613)
              ·
                refine ⟨485032456955383646678105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293419885214356391141613 485032456955383646678105)
                ·
                  refine ⟨363774342716537735008579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485032456955383646678105 363774342716537735008579)
                  ·
                    rfl

theorem cell20_797004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_797004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797004 prefixEnd_797004 := by exact prefixLift 797004
  have htrace : WordTrace (prefixWord ++ tailWord_797004) baseStart_797004 baseEnd_797004 := by
    simpa [prefixWord, tailWord_797004, baseEnd_797004] using wordTrace_append hprefix tailTrace_797004
  have hstable : (prefixWord ++ tailWord_797004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797004).length < 2 ^ (prefixWord ++ tailWord_797004).sum := by decide
  have hdescent : baseEnd_797004 < baseStart_797004 := by decide
  rcases family_descends (prefixWord ++ tailWord_797004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797015 : List Nat := [1, 1, 3, 2, 3, 1, 9]
def baseStart_797015 : Nat := 118140960795 + 797015 * 2 ^ 59
def prefixEnd_797015 : Nat := 4983230072969 + 3 ^ 40 * 797015 * 2
def baseEnd_797015 : Nat := 40419929268474509515763

theorem tailTrace_797015 : CollatzResearch.WordTrace tailWord_797015 prefixEnd_797015 40419929268474509515763 := by
  unfold tailWord_797015
  simp only [CollatzResearch.WordTrace]
  refine ⟨29069525207558249170096499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19379683471705499446730999 29069525207558249170096499)
  ·
    refine ⟨43604287811337373755144749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29069525207558249170096499 43604287811337373755144749)
    ·
      refine ⟨16351607929251515158179281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43604287811337373755144749 16351607929251515158179281)
      ·
        refine ⟨12263705946938636368634461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16351607929251515158179281 12263705946938636368634461)
        ·
          refine ⟨4598889730101988638237923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12263705946938636368634461 4598889730101988638237923)
          ·
            refine ⟨6898334595152982957356885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598889730101988638237923 6898334595152982957356885)
            ·
              refine ⟨40419929268474509515763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6898334595152982957356885 40419929268474509515763)
              ·
                rfl

theorem cell20_797015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_797015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797015 prefixEnd_797015 := by exact prefixLift 797015
  have htrace : WordTrace (prefixWord ++ tailWord_797015) baseStart_797015 baseEnd_797015 := by
    simpa [prefixWord, tailWord_797015, baseEnd_797015] using wordTrace_append hprefix tailTrace_797015
  have hstable : (prefixWord ++ tailWord_797015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797015).length < 2 ^ (prefixWord ++ tailWord_797015).sum := by decide
  have hdescent : baseEnd_797015 < baseStart_797015 := by decide
  rcases family_descends (prefixWord ++ tailWord_797015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797059 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 2]
def baseStart_797059 : Nat := 118140960795 + 797059 * 2 ^ 59
def prefixEnd_797059 : Nat := 4983230072969 + 3 ^ 40 * 797059 * 2
def baseEnd_797059 : Nat := 363799446215201988175021

theorem tailTrace_797059 : CollatzResearch.WordTrace tailWord_797059 prefixEnd_797059 363799446215201988175021 := by
  unfold tailWord_797059
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071130019398844684698231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380753346265896456465487 29071130019398844684698231)
  ·
    refine ⟨43606695029098267027047347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29071130019398844684698231 43606695029098267027047347)
    ·
      refine ⟨65410042543647400540571021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43606695029098267027047347 65410042543647400540571021)
      ·
        refine ⟨24528765953867775202714133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65410042543647400540571021 24528765953867775202714133)
        ·
          refine ⟨1149785904087551962627225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24528765953867775202714133 1149785904087551962627225)
          ·
            refine ⟨862339428065663971970419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149785904087551962627225 862339428065663971970419)
            ·
              refine ⟨1293509142098495957955629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862339428065663971970419 1293509142098495957955629)
              ·
                refine ⟨485065928286935984233361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293509142098495957955629 485065928286935984233361)
                ·
                  refine ⟨363799446215201988175021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485065928286935984233361 363799446215201988175021)
                  ·
                    rfl

theorem cell20_797059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2].length) (baseStart_797059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797059 prefixEnd_797059 := by exact prefixLift 797059
  have htrace : WordTrace (prefixWord ++ tailWord_797059) baseStart_797059 baseEnd_797059 := by
    simpa [prefixWord, tailWord_797059, baseEnd_797059] using wordTrace_append hprefix tailTrace_797059
  have hstable : (prefixWord ++ tailWord_797059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797059).length < 2 ^ (prefixWord ++ tailWord_797059).sum := by decide
  have hdescent : baseEnd_797059 < baseStart_797059 := by decide
  rcases family_descends (prefixWord ++ tailWord_797059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797066 : List Nat := [3, 1, 2, 5, 2, 1, 6]
def baseStart_797066 : Nat := 118140960795 + 797066 * 2 ^ 59
def prefixEnd_797066 : Nat := 4983230072969 + 3 ^ 40 * 797066 * 2
def baseEnd_797066 : Nat := 40422515689549008326851

theorem tailTrace_797066 : CollatzResearch.WordTrace tailWord_797066 prefixEnd_797066 40422515689549008326851 := by
  unfold tailWord_797066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267846332593371220050763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19380923553582323253468701 7267846332593371220050763)
  ·
    refine ⟨10901769498890056830076145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7267846332593371220050763 10901769498890056830076145)
    ·
      refine ⟨8176327124167542622557109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10901769498890056830076145 8176327124167542622557109)
      ·
        refine ⟨766530667890707120864729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8176327124167542622557109 766530667890707120864729)
        ·
          refine ⟨574898000918030340648547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766530667890707120864729 574898000918030340648547)
          ·
            refine ⟨862347001377045510972821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574898000918030340648547 862347001377045510972821)
            ·
              refine ⟨40422515689549008326851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 862347001377045510972821 40422515689549008326851)
              ·
                rfl

theorem cell20_797066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_797066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797066 prefixEnd_797066 := by exact prefixLift 797066
  have htrace : WordTrace (prefixWord ++ tailWord_797066) baseStart_797066 baseEnd_797066 := by
    simpa [prefixWord, tailWord_797066, baseEnd_797066] using wordTrace_append hprefix tailTrace_797066
  have hstable : (prefixWord ++ tailWord_797066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797066).length < 2 ^ (prefixWord ++ tailWord_797066).sum := by decide
  have hdescent : baseEnd_797066 < baseStart_797066 := by decide
  rcases family_descends (prefixWord ++ tailWord_797066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797070 : List Nat := [4, 1, 1, 4, 1, 1, 8]
def baseStart_797070 : Nat := 118140960795 + 797070 * 2 ^ 59
def prefixEnd_797070 : Nat := 4983230072969 + 3 ^ 40 * 797070 * 2
def baseEnd_797070 : Nat := 40422718546103870978701

theorem tailTrace_797070 : CollatzResearch.WordTrace tailWord_797070 prefixEnd_797070 40422718546103870978701 := by
  unfold tailWord_797070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633941402794874195418583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19381020814905995708899109 3633941402794874195418583)
  ·
    refine ⟨5450912104192311293127875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633941402794874195418583 5450912104192311293127875)
    ·
      refine ⟨8176368156288466939691813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450912104192311293127875 8176368156288466939691813)
      ·
        refine ⟨1533069029304087551192215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8176368156288466939691813 1533069029304087551192215)
        ·
          refine ⟨2299603543956131326788323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533069029304087551192215 2299603543956131326788323)
          ·
            refine ⟨3449405315934196990182485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299603543956131326788323 3449405315934196990182485)
            ·
              refine ⟨40422718546103870978701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3449405315934196990182485 40422718546103870978701)
              ·
                rfl

theorem cell20_797070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_797070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797070 prefixEnd_797070 := by exact prefixLift 797070
  have htrace : WordTrace (prefixWord ++ tailWord_797070) baseStart_797070 baseEnd_797070 := by
    simpa [prefixWord, tailWord_797070, baseEnd_797070] using wordTrace_append hprefix tailTrace_797070
  have hstable : (prefixWord ++ tailWord_797070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797070).length < 2 ^ (prefixWord ++ tailWord_797070).sum := by decide
  have hdescent : baseEnd_797070 < baseStart_797070 := by decide
  rcases family_descends (prefixWord ++ tailWord_797070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797076 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_797076 : Nat := 118140960795 + 797076 * 2 ^ 59
def prefixEnd_797076 : Nat := 4983230072969 + 3 ^ 40 * 797076 * 2
def baseEnd_797076 : Nat := 363807205478425484608285

theorem tailTrace_797076 : CollatzResearch.WordTrace tailWord_797076 prefixEnd_797076 363807205478425484608285 := by
  unfold tailWord_797076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14535875030168628294033541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19381166706891504392044721 14535875030168628294033541)
  ·
    refine ⟨2725476568156617805131289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14535875030168628294033541 2725476568156617805131289)
    ·
      refine ⟨2044107426117463353848467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2725476568156617805131289 2044107426117463353848467)
      ·
        refine ⟨3066161139176195030772701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044107426117463353848467 3066161139176195030772701)
        ·
          refine ⟨1149810427191073136539763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3066161139176195030772701 1149810427191073136539763)
          ·
            refine ⟨1724715640786609704809645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149810427191073136539763 1724715640786609704809645)
            ·
              refine ⟨646768365294978639303617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1724715640786609704809645 646768365294978639303617)
              ·
                refine ⟨485076273971233979477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646768365294978639303617 485076273971233979477713)
                ·
                  refine ⟨363807205478425484608285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485076273971233979477713 363807205478425484608285)
                  ·
                    rfl

theorem cell20_797076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_797076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797076 prefixEnd_797076 := by exact prefixLift 797076
  have htrace : WordTrace (prefixWord ++ tailWord_797076) baseStart_797076 baseEnd_797076 := by
    simpa [prefixWord, tailWord_797076, baseEnd_797076] using wordTrace_append hprefix tailTrace_797076
  have hstable : (prefixWord ++ tailWord_797076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797076).length < 2 ^ (prefixWord ++ tailWord_797076).sum := by decide
  have hdescent : baseEnd_797076 < baseStart_797076 := by decide
  rcases family_descends (prefixWord ++ tailWord_797076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797077 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_797077 : Nat := 118140960795 + 797077 * 2 ^ 59
def prefixEnd_797077 : Nat := 4983230072969 + 3 ^ 40 * 797077 * 2
def baseEnd_797077 : Nat := 363807661905673925574947

theorem tailTrace_797077 : CollatzResearch.WordTrace tailWord_797077 prefixEnd_797077 363807661905673925574947 := by
  unfold tailWord_797077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071786533333633758853485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19381191022222422505902323 29071786533333633758853485)
  ·
    refine ⟨10901919950000112659570057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29071786533333633758853485 10901919950000112659570057)
    ·
      refine ⟨8176439962500084494677543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10901919950000112659570057 8176439962500084494677543)
      ·
        refine ⟨12264659943750126742016315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8176439962500084494677543 12264659943750126742016315)
        ·
          refine ⟨18396989915625190113024473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12264659943750126742016315 18396989915625190113024473)
          ·
            refine ⟨13797742436718892584768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18396989915625190113024473 13797742436718892584768355)
            ·
              refine ⟨20696613655078338877152533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13797742436718892584768355 20696613655078338877152533)
              ·
                refine ⟨970153765081797134866525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20696613655078338877152533 970153765081797134866525)
                ·
                  refine ⟨363807661905673925574947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970153765081797134866525 363807661905673925574947)
                  ·
                    rfl

theorem cell20_797077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_797077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797077 prefixEnd_797077 := by exact prefixLift 797077
  have htrace : WordTrace (prefixWord ++ tailWord_797077) baseStart_797077 baseEnd_797077 := by
    simpa [prefixWord, tailWord_797077, baseEnd_797077] using wordTrace_append hprefix tailTrace_797077
  have hstable : (prefixWord ++ tailWord_797077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797077).length < 2 ^ (prefixWord ++ tailWord_797077).sum := by decide
  have hdescent : baseEnd_797077 < baseStart_797077 := by decide
  rcases family_descends (prefixWord ++ tailWord_797077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797080 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_797080 : Nat := 118140960795 + 797080 * 2 ^ 59
def prefixEnd_797080 : Nat := 4983230072969 + 3 ^ 40 * 797080 * 2
def baseEnd_797080 : Nat := 363809031187419248474935

theorem tailTrace_797080 : CollatzResearch.WordTrace tailWord_797080 prefixEnd_797080 363809031187419248474935 := by
  unfold tailWord_797080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14535947976161382635606347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19381263968215176847475129 14535947976161382635606347)
  ·
    refine ⟨21803921964242073953409521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14535947976161382635606347 21803921964242073953409521)
    ·
      refine ⟨16352941473181555465057141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21803921964242073953409521 16352941473181555465057141)
      ·
        refine ⟨1533088263110770824849107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16352941473181555465057141 1533088263110770824849107)
        ·
          refine ⟨2299632394666156237273661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533088263110770824849107 2299632394666156237273661)
          ·
            refine ⟨862362147999808588977623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2299632394666156237273661 862362147999808588977623)
            ·
              refine ⟨1293543221999712883466435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862362147999808588977623 1293543221999712883466435)
              ·
                refine ⟨1940314832999569325199653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293543221999712883466435 1940314832999569325199653)
                ·
                  refine ⟨363809031187419248474935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1940314832999569325199653 363809031187419248474935)
                  ·
                    rfl

theorem cell20_797080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_797080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797080 prefixEnd_797080 := by exact prefixLift 797080
  have htrace : WordTrace (prefixWord ++ tailWord_797080) baseStart_797080 baseEnd_797080 := by
    simpa [prefixWord, tailWord_797080, baseEnd_797080] using wordTrace_append hprefix tailTrace_797080
  have hstable : (prefixWord ++ tailWord_797080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797080).length < 2 ^ (prefixWord ++ tailWord_797080).sum := by decide
  have hdescent : baseEnd_797080 < baseStart_797080 := by decide
  rcases family_descends (prefixWord ++ tailWord_797080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797091 : List Nat := [1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_797091 : Nat := 118140960795 + 797091 * 2 ^ 59
def prefixEnd_797091 : Nat := 4983230072969 + 3 ^ 40 * 797091 * 2
def baseEnd_797091 : Nat := 121271350629050699702741

theorem tailTrace_797091 : CollatzResearch.WordTrace tailWord_797091 prefixEnd_797091 121271350629050699702741 := by
  unfold tailWord_797091
  simp only [CollatzResearch.WordTrace]
  refine ⟨29072297155282914149863127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19381531436855276099908751 29072297155282914149863127)
  ·
    refine ⟨43608445732924371224794691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29072297155282914149863127 43608445732924371224794691)
    ·
      refine ⟨65412668599386556837192037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43608445732924371224794691 65412668599386556837192037)
      ·
        refine ⟨12264875362384979406973507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65412668599386556837192037 12264875362384979406973507)
        ·
          refine ⟨18397313043577469110460261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12264875362384979406973507 18397313043577469110460261)
          ·
            refine ⟨3449496195670775458211299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18397313043577469110460261 3449496195670775458211299)
            ·
              refine ⟨5174244293506163187316949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449496195670775458211299 5174244293506163187316949)
              ·
                refine ⟨121271350629050699702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5174244293506163187316949 121271350629050699702741)
                ·
                  rfl

theorem cell20_797091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_797091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797091 prefixEnd_797091 := by exact prefixLift 797091
  have htrace : WordTrace (prefixWord ++ tailWord_797091) baseStart_797091 baseEnd_797091 := by
    simpa [prefixWord, tailWord_797091, baseEnd_797091] using wordTrace_append hprefix tailTrace_797091
  have hstable : (prefixWord ++ tailWord_797091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797091).length < 2 ^ (prefixWord ++ tailWord_797091).sum := by decide
  have hdescent : baseEnd_797091 < baseStart_797091 := by decide
  rcases family_descends (prefixWord ++ tailWord_797091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797153 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_797153 : Nat := 118140960795 + 797153 * 2 ^ 59
def prefixEnd_797153 : Nat := 4983230072969 + 3 ^ 40 * 797153 * 2
def baseEnd_797153 : Nat := 363842350376555439041303

theorem tailTrace_797153 : CollatzResearch.WordTrace tailWord_797153 prefixEnd_797153 363842350376555439041303 := by
  unfold tailWord_797153
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074558481058298738620113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19383038987372199159080075 29074558481058298738620113)
  ·
    refine ⟨21805918860793724053965085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29074558481058298738620113 21805918860793724053965085)
    ·
      refine ⟨8177219572797646520236907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21805918860793724053965085 8177219572797646520236907)
      ·
        refine ⟨12265829359196469780355361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177219572797646520236907 12265829359196469780355361)
        ·
          refine ⟨9199372019397352335266521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12265829359196469780355361 9199372019397352335266521)
          ·
            refine ⟨6899529014548014251449891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9199372019397352335266521 6899529014548014251449891)
            ·
              refine ⟨10349293521822021377174837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899529014548014251449891 10349293521822021377174837)
              ·
                refine ⟨970246267670814504110141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10349293521822021377174837 970246267670814504110141)
                ·
                  refine ⟨363842350376555439041303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970246267670814504110141 363842350376555439041303)
                  ·
                    rfl

theorem cell20_797153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_797153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797153 prefixEnd_797153 := by exact prefixLift 797153
  have htrace : WordTrace (prefixWord ++ tailWord_797153) baseStart_797153 baseEnd_797153 := by
    simpa [prefixWord, tailWord_797153, baseEnd_797153] using wordTrace_append hprefix tailTrace_797153
  have hstable : (prefixWord ++ tailWord_797153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797153).length < 2 ^ (prefixWord ++ tailWord_797153).sum := by decide
  have hdescent : baseEnd_797153 < baseStart_797153 := by decide
  rcases family_descends (prefixWord ++ tailWord_797153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797160 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_797160 : Nat := 118140960795 + 797160 * 2 ^ 59
def prefixEnd_797160 : Nat := 4983230072969 + 3 ^ 40 * 797160 * 2
def baseEnd_797160 : Nat := 363845545367294525807941

theorem tailTrace_797160 : CollatzResearch.WordTrace tailWord_797160 prefixEnd_797160 363845545367294525807941 := by
  unfold tailWord_797160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537406896016469467062467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19383209194688625956083289 14537406896016469467062467)
  ·
    refine ⟨21806110344024704200593701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537406896016469467062467 21806110344024704200593701)
    ·
      refine ⟨4088645689504632037611319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21806110344024704200593701 4088645689504632037611319)
      ·
        refine ⟨6132968534256948056416979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088645689504632037611319 6132968534256948056416979)
        ·
          refine ⟨9199452801385422084625469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132968534256948056416979 9199452801385422084625469)
          ·
            refine ⟨3449794800519533281734551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9199452801385422084625469 3449794800519533281734551)
            ·
              refine ⟨5174692200779299922601827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449794800519533281734551 5174692200779299922601827)
              ·
                refine ⟨7762038301168949883902741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5174692200779299922601827 7762038301168949883902741)
                ·
                  refine ⟨363845545367294525807941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7762038301168949883902741 363845545367294525807941)
                  ·
                    rfl

theorem cell20_797160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_797160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797160 prefixEnd_797160 := by exact prefixLift 797160
  have htrace : WordTrace (prefixWord ++ tailWord_797160) baseStart_797160 baseEnd_797160 := by
    simpa [prefixWord, tailWord_797160, baseEnd_797160] using wordTrace_append hprefix tailTrace_797160
  have hstable : (prefixWord ++ tailWord_797160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797160).length < 2 ^ (prefixWord ++ tailWord_797160).sum := by decide
  have hdescent : baseEnd_797160 < baseStart_797160 := by decide
  rcases family_descends (prefixWord ++ tailWord_797160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797177 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 2]
def baseStart_797177 : Nat := 118140960795 + 797177 * 2 ^ 59
def prefixEnd_797177 : Nat := 4983230072969 + 3 ^ 40 * 797177 * 2
def baseEnd_797177 : Nat := 363853304630518022241205

theorem tailTrace_797177 : CollatzResearch.WordTrace tailWord_797177 prefixEnd_797177 363853304630518022241205 := by
  unfold tailWord_797177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29075433832971350837493785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19383622555314233891662523 29075433832971350837493785)
  ·
    refine ⟨21806575374728513128120339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29075433832971350837493785 21806575374728513128120339)
    ·
      refine ⟨32709863062092769692180509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21806575374728513128120339 32709863062092769692180509)
      ·
        refine ⟨12266198648284788634567691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32709863062092769692180509 12266198648284788634567691)
        ·
          refine ⟨18399297972427182951851537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12266198648284788634567691 18399297972427182951851537)
          ·
            refine ⟨13799473479320387213888653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18399297972427182951851537 13799473479320387213888653)
            ·
              refine ⟨5174802554745145205208245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13799473479320387213888653 5174802554745145205208245)
              ·
                refine ⟨485137739507357362988273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5174802554745145205208245 485137739507357362988273)
                ·
                  refine ⟨363853304630518022241205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485137739507357362988273 363853304630518022241205)
                  ·
                    rfl

theorem cell20_797177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_797177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797177 prefixEnd_797177 := by exact prefixLift 797177
  have htrace : WordTrace (prefixWord ++ tailWord_797177) baseStart_797177 baseEnd_797177 := by
    simpa [prefixWord, tailWord_797177, baseEnd_797177] using wordTrace_append hprefix tailTrace_797177
  have hstable : (prefixWord ++ tailWord_797177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797177).length < 2 ^ (prefixWord ++ tailWord_797177).sum := by decide
  have hdescent : baseEnd_797177 < baseStart_797177 := by decide
  rcases family_descends (prefixWord ++ tailWord_797177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797190 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_797190 : Nat := 118140960795 + 797190 * 2 ^ 59
def prefixEnd_797190 : Nat := 4983230072969 + 3 ^ 40 * 797190 * 2
def baseEnd_797190 : Nat := 363859238184747754807819

theorem tailTrace_797190 : CollatzResearch.WordTrace tailWord_797190 prefixEnd_797190 363859238184747754807819 := by
  unfold tailWord_797190
  simp only [CollatzResearch.WordTrace]
  refine ⟨908622124435132939303657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19383938654616169371811349 908622124435132939303657)
  ·
    refine ⟨681466593326349704477743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 908622124435132939303657 681466593326349704477743)
    ·
      refine ⟨1022199889989524556716615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681466593326349704477743 1022199889989524556716615)
      ·
        refine ⟨1533299834984286835074923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022199889989524556716615 1533299834984286835074923)
        ·
          refine ⟨2299949752476430252612385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533299834984286835074923 2299949752476430252612385)
          ·
            refine ⟨1724962314357322689459289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299949752476430252612385 1724962314357322689459289)
            ·
              refine ⟨1293721735767992017094467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724962314357322689459289 1293721735767992017094467)
              ·
                refine ⟨1940582603651988025641701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293721735767992017094467 1940582603651988025641701)
                ·
                  refine ⟨363859238184747754807819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1940582603651988025641701 363859238184747754807819)
                  ·
                    rfl

theorem cell20_797190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_797190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797190 prefixEnd_797190 := by exact prefixLift 797190
  have htrace : WordTrace (prefixWord ++ tailWord_797190) baseStart_797190 baseEnd_797190 := by
    simpa [prefixWord, tailWord_797190, baseEnd_797190] using wordTrace_append hprefix tailTrace_797190
  have hstable : (prefixWord ++ tailWord_797190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797190).length < 2 ^ (prefixWord ++ tailWord_797190).sum := by decide
  have hdescent : baseEnd_797190 < baseStart_797190 := by decide
  rcases family_descends (prefixWord ++ tailWord_797190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797204 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_797204 : Nat := 118140960795 + 797204 * 2 ^ 59
def prefixEnd_797204 : Nat := 4983230072969 + 3 ^ 40 * 797204 * 2
def baseEnd_797204 : Nat := 363865628166225928341095

theorem tailTrace_797204 : CollatzResearch.WordTrace tailWord_797204 prefixEnd_797204 363865628166225928341095 := by
  unfold tailWord_797204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538209301936767224363333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19384279069249022965817777 14538209301936767224363333)
  ·
    refine ⟨2725914244113143854568125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14538209301936767224363333 2725914244113143854568125)
    ·
      refine ⟨1022217841542428945463047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2725914244113143854568125 1022217841542428945463047)
      ·
        refine ⟨1533326762313643418194571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022217841542428945463047 1533326762313643418194571)
        ·
          refine ⟨2299990143470465127291857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533326762313643418194571 2299990143470465127291857)
          ·
            refine ⟨1724992607602848845468893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299990143470465127291857 1724992607602848845468893)
            ·
              refine ⟨646872227851068317050835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1724992607602848845468893 646872227851068317050835)
              ·
                refine ⟨970308341776602475576253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646872227851068317050835 970308341776602475576253)
                ·
                  refine ⟨363865628166225928341095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970308341776602475576253 363865628166225928341095)
                  ·
                    rfl

theorem cell20_797204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_797204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797204 prefixEnd_797204 := by exact prefixLift 797204
  have htrace : WordTrace (prefixWord ++ tailWord_797204) baseStart_797204 baseEnd_797204 := by
    simpa [prefixWord, tailWord_797204, baseEnd_797204] using wordTrace_append hprefix tailTrace_797204
  have hstable : (prefixWord ++ tailWord_797204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797204).length < 2 ^ (prefixWord ++ tailWord_797204).sum := by decide
  have hdescent : baseEnd_797204 < baseStart_797204 := by decide
  rcases family_descends (prefixWord ++ tailWord_797204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797205 : List Nat := [1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_797205 : Nat := 118140960795 + 797205 * 2 ^ 59
def prefixEnd_797205 : Nat := 4983230072969 + 3 ^ 40 * 797205 * 2
def baseEnd_797205 : Nat := 121288694864491456435919

theorem tailTrace_797205 : CollatzResearch.WordTrace tailWord_797205 prefixEnd_797205 121288694864491456435919 := by
  unfold tailWord_797205
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076455076869911619513069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19384303384579941079675379 29076455076869911619513069)
  ·
    refine ⟨10903670653826216857317401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29076455076869911619513069 10903670653826216857317401)
    ·
      refine ⟨8177752990369662642988051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10903670653826216857317401 8177752990369662642988051)
      ·
        refine ⟨12266629485554493964482077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177752990369662642988051 12266629485554493964482077)
        ·
          refine ⟨4599986057082935236680779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12266629485554493964482077 4599986057082935236680779)
          ·
            refine ⟨6899979085624402855021169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599986057082935236680779 6899979085624402855021169)
            ·
              refine ⟨5174984314218302141265877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899979085624402855021169 5174984314218302141265877)
              ·
                refine ⟨121288694864491456435919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5174984314218302141265877 121288694864491456435919)
                ·
                  rfl

theorem cell20_797205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_797205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797205 prefixEnd_797205 := by exact prefixLift 797205
  have htrace : WordTrace (prefixWord ++ tailWord_797205) baseStart_797205 baseEnd_797205 := by
    simpa [prefixWord, tailWord_797205, baseEnd_797205] using wordTrace_append hprefix tailTrace_797205
  have hstable : (prefixWord ++ tailWord_797205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797205).length < 2 ^ (prefixWord ++ tailWord_797205).sum := by decide
  have hdescent : baseEnd_797205 < baseStart_797205 := by decide
  rcases family_descends (prefixWord ++ tailWord_797205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797249 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 2]
def baseStart_797249 : Nat := 118140960795 + 797249 * 2 ^ 59
def prefixEnd_797249 : Nat := 4983230072969 + 3 ^ 40 * 797249 * 2
def baseEnd_797249 : Nat := 363886167392405771840911

theorem tailTrace_797249 : CollatzResearch.WordTrace tailWord_797249 prefixEnd_797249 363886167392405771840911 := by
  unfold tailWord_797249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078059888710507134114801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385373259140338089409867 29078059888710507134114801)
  ·
    refine ⟨21808544916532880350586101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29078059888710507134114801 21808544916532880350586101)
    ·
      refine ⟨2044551085924957532867447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21808544916532880350586101 2044551085924957532867447)
      ·
        refine ⟨3066826628887436299301171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044551085924957532867447 3066826628887436299301171)
        ·
          refine ⟨4600239943331154448951757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066826628887436299301171 4600239943331154448951757)
          ·
            refine ⟨1725089978749182918356909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4600239943331154448951757 1725089978749182918356909)
            ·
              refine ⟨646908742030943594383841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725089978749182918356909 646908742030943594383841)
              ·
                refine ⟨485181556523207695787881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646908742030943594383841 485181556523207695787881)
                ·
                  refine ⟨363886167392405771840911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485181556523207695787881 363886167392405771840911)
                  ·
                    rfl

theorem cell20_797249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_797249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797249 prefixEnd_797249 := by exact prefixLift 797249
  have htrace : WordTrace (prefixWord ++ tailWord_797249) baseStart_797249 baseEnd_797249 := by
    simpa [prefixWord, tailWord_797249, baseEnd_797249] using wordTrace_append hprefix tailTrace_797249
  have hstable : (prefixWord ++ tailWord_797249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797249).length < 2 ^ (prefixWord ++ tailWord_797249).sum := by decide
  have hdescent : baseEnd_797249 < baseStart_797249 := by decide
  rcases family_descends (prefixWord ++ tailWord_797249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797253 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_797253 : Nat := 118140960795 + 797253 * 2 ^ 59
def prefixEnd_797253 : Nat := 4983230072969 + 3 ^ 40 * 797253 * 2
def baseEnd_797253 : Nat := 363887993101399535707561

theorem tailTrace_797253 : CollatzResearch.WordTrace tailWord_797253 prefixEnd_797253 363887993101399535707561 := by
  unfold tailWord_797253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078205780696015817260413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385470520464010544840275 29078205780696015817260413)
  ·
    refine ⟨10904327167761005931472655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29078205780696015817260413 10904327167761005931472655)
    ·
      refine ⟨16356490751641508897208983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10904327167761005931472655 16356490751641508897208983)
      ·
        refine ⟨24534736127462263345813475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16356490751641508897208983 24534736127462263345813475)
        ·
          refine ⟨36802104191193395018720213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24534736127462263345813475 36802104191193395018720213)
          ·
            refine ⟨862549316981095195751255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36802104191193395018720213 862549316981095195751255)
            ·
              refine ⟨1293823975471642793626883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862549316981095195751255 1293823975471642793626883)
              ·
                refine ⟨1940735963207464190440325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293823975471642793626883 1940735963207464190440325)
                ·
                  refine ⟨363887993101399535707561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1940735963207464190440325 363887993101399535707561)
                  ·
                    rfl

theorem cell20_797253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_797253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797253 prefixEnd_797253 := by exact prefixLift 797253
  have htrace : WordTrace (prefixWord ++ tailWord_797253) baseStart_797253 baseEnd_797253 := by
    simpa [prefixWord, tailWord_797253, baseEnd_797253] using wordTrace_append hprefix tailTrace_797253
  have hstable : (prefixWord ++ tailWord_797253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797253).length < 2 ^ (prefixWord ++ tailWord_797253).sum := by decide
  have hdescent : baseEnd_797253 < baseStart_797253 := by decide
  rcases family_descends (prefixWord ++ tailWord_797253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797281 : List Nat := [1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_797281 : Nat := 118140960795 + 797281 * 2 ^ 59
def prefixEnd_797281 : Nat := 4983230072969 + 3 ^ 40 * 797281 * 2
def baseEnd_797281 : Nat := 121300257688118627591371

theorem tailTrace_797281 : CollatzResearch.WordTrace tailWord_797281 prefixEnd_797281 121300257688118627591371 := by
  unfold tailWord_797281
  simp only [CollatzResearch.WordTrace]
  refine ⟨29079227024594576599279697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19386151349729717732853131 29079227024594576599279697)
  ·
    refine ⟨21809420268445932449459773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29079227024594576599279697 21809420268445932449459773)
    ·
      refine ⟨8178532600667224668547415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21809420268445932449459773 8178532600667224668547415)
      ·
        refine ⟨12267798901000837002821123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178532600667224668547415 12267798901000837002821123)
        ·
          refine ⟨18401698351501255504231685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12267798901000837002821123 18401698351501255504231685)
          ·
            refine ⟨3450318440906485407043441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18401698351501255504231685 3450318440906485407043441)
            ·
              refine ⟨2587738830679864055282581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450318440906485407043441 2587738830679864055282581)
              ·
                refine ⟨121300257688118627591371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2587738830679864055282581 121300257688118627591371)
                ·
                  rfl

theorem cell20_797281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_797281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797281 prefixEnd_797281 := by exact prefixLift 797281
  have htrace : WordTrace (prefixWord ++ tailWord_797281) baseStart_797281 baseEnd_797281 := by
    simpa [prefixWord, tailWord_797281, baseEnd_797281] using wordTrace_append hprefix tailTrace_797281
  have hstable : (prefixWord ++ tailWord_797281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797281).length < 2 ^ (prefixWord ++ tailWord_797281).sum := by decide
  have hdescent : baseEnd_797281 < baseStart_797281 := by decide
  rcases family_descends (prefixWord ++ tailWord_797281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797298 : List Nat := [3, 2, 1, 2, 5, 7]
def baseStart_797298 : Nat := 118140960795 + 797298 * 2 ^ 59
def prefixEnd_797298 : Nat := 4983230072969 + 3 ^ 40 * 797298 * 2
def baseEnd_797298 : Nat := 13478093789910347378051

theorem tailTrace_797298 : CollatzResearch.WordTrace tailWord_797298 prefixEnd_797298 13478093789910347378051 := by
  unfold tailWord_797298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269961766383247125662137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19386564710355325668432365 7269961766383247125662137)
  ·
    refine ⟨5452471324787435344246603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7269961766383247125662137 5452471324787435344246603)
    ·
      refine ⟨8178706987181153016369905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452471324787435344246603 8178706987181153016369905)
      ·
        refine ⟨6134030240385864762277429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8178706987181153016369905 6134030240385864762277429)
        ·
          refine ⟨575065335036174821463509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6134030240385864762277429 575065335036174821463509)
          ·
            refine ⟨13478093789910347378051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 575065335036174821463509 13478093789910347378051)
            ·
              rfl

theorem cell20_797298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 7].length) (baseStart_797298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797298 prefixEnd_797298 := by exact prefixLift 797298
  have htrace : WordTrace (prefixWord ++ tailWord_797298) baseStart_797298 baseEnd_797298 := by
    simpa [prefixWord, tailWord_797298, baseEnd_797298] using wordTrace_append hprefix tailTrace_797298
  have hstable : (prefixWord ++ tailWord_797298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797298).length < 2 ^ (prefixWord ++ tailWord_797298).sum := by decide
  have hdescent : baseEnd_797298 < baseStart_797298 := by decide
  rcases family_descends (prefixWord ++ tailWord_797298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797301 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_797301 : Nat := 118140960795 + 797301 * 2 ^ 59
def prefixEnd_797301 : Nat := 4983230072969 + 3 ^ 40 * 797301 * 2
def baseEnd_797301 : Nat := 363909901609324702107365

theorem tailTrace_797301 : CollatzResearch.WordTrace tailWord_797301 prefixEnd_797301 363909901609324702107365 := by
  unfold tailWord_797301
  simp only [CollatzResearch.WordTrace]
  refine ⟨29079956484522120015007757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19386637656348080010005171 29079956484522120015007757)
  ·
    refine ⟨10904983681695795005627909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29079956484522120015007757 10904983681695795005627909)
    ·
      refine ⟨2044684440317961563555233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10904983681695795005627909 2044684440317961563555233)
      ·
        refine ⟨1533513330238471172666425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044684440317961563555233 1533513330238471172666425)
        ·
          refine ⟨1150134997678853379499819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1533513330238471172666425 1150134997678853379499819)
          ·
            refine ⟨1725202496518280069249729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150134997678853379499819 1725202496518280069249729)
            ·
              refine ⟨1293901872388710051937297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725202496518280069249729 1293901872388710051937297)
              ·
                refine ⟨970426404291532538952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293901872388710051937297 970426404291532538952973)
                ·
                  refine ⟨363909901609324702107365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970426404291532538952973 363909901609324702107365)
                  ·
                    rfl

theorem cell20_797301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_797301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797301 prefixEnd_797301 := by exact prefixLift 797301
  have htrace : WordTrace (prefixWord ++ tailWord_797301) baseStart_797301 baseEnd_797301 := by
    simpa [prefixWord, tailWord_797301, baseEnd_797301] using wordTrace_append hprefix tailTrace_797301
  have hstable : (prefixWord ++ tailWord_797301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797301).length < 2 ^ (prefixWord ++ tailWord_797301).sum := by decide
  have hdescent : baseEnd_797301 < baseStart_797301 := by decide
  rcases family_descends (prefixWord ++ tailWord_797301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797305 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_797305 : Nat := 118140960795 + 797305 * 2 ^ 59
def prefixEnd_797305 : Nat := 4983230072969 + 3 ^ 40 * 797305 * 2
def baseEnd_797305 : Nat := 363911727318318465974015

theorem tailTrace_797305 : CollatzResearch.WordTrace tailWord_797305 prefixEnd_797305 363911727318318465974015 := by
  unfold tailWord_797305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080102376507628698153369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19386734917671752465435579 29080102376507628698153369)
  ·
    refine ⟨21810076782380721523615027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29080102376507628698153369 21810076782380721523615027)
    ·
      refine ⟨32715115173571082285422541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21810076782380721523615027 32715115173571082285422541)
      ·
        refine ⟨12268168190089155857033453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32715115173571082285422541 12268168190089155857033453)
        ·
          refine ⟨4600563071283433446387545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268168190089155857033453 4600563071283433446387545)
          ·
            refine ⟨3450422303462575084790659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600563071283433446387545 3450422303462575084790659)
            ·
              refine ⟨5175633455193862627185989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450422303462575084790659 5175633455193862627185989)
              ·
                refine ⟨970431272848849242597373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5175633455193862627185989 970431272848849242597373)
                ·
                  refine ⟨363911727318318465974015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970431272848849242597373 363911727318318465974015)
                  ·
                    rfl

theorem cell20_797305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_797305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797305 prefixEnd_797305 := by exact prefixLift 797305
  have htrace : WordTrace (prefixWord ++ tailWord_797305) baseStart_797305 baseEnd_797305 := by
    simpa [prefixWord, tailWord_797305, baseEnd_797305] using wordTrace_append hprefix tailTrace_797305
  have hstable : (prefixWord ++ tailWord_797305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797305).length < 2 ^ (prefixWord ++ tailWord_797305).sum := by decide
  have hdescent : baseEnd_797305 < baseStart_797305 := by decide
  rcases family_descends (prefixWord ++ tailWord_797305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797308 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_797308 : Nat := 118140960795 + 797308 * 2 ^ 59
def prefixEnd_797308 : Nat := 4983230072969 + 3 ^ 40 * 797308 * 2
def baseEnd_797308 : Nat := 363913096600063788874003

theorem tailTrace_797308 : CollatzResearch.WordTrace tailWord_797308 prefixEnd_797308 363913096600063788874003 := by
  unfold tailWord_797308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540105897748380105256289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19386807863664506807008385 14540105897748380105256289)
  ·
    refine ⟨10905079423311285078942217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14540105897748380105256289 10905079423311285078942217)
    ·
      refine ⟨8178809567483463809206663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10905079423311285078942217 8178809567483463809206663)
      ·
        refine ⟨12268214351225195713809995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178809567483463809206663 12268214351225195713809995)
        ·
          refine ⟨18402321526837793570714993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268214351225195713809995 18402321526837793570714993)
          ·
            refine ⟨13801741145128345178036245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18402321526837793570714993 13801741145128345178036245)
            ·
              refine ⟨646956616177891180220449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13801741145128345178036245 646956616177891180220449)
              ·
                refine ⟨485217462133418385165337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646956616177891180220449 485217462133418385165337)
                ·
                  refine ⟨363913096600063788874003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485217462133418385165337 363913096600063788874003)
                  ·
                    rfl

theorem cell20_797308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_797308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797308 prefixEnd_797308 := by exact prefixLift 797308
  have htrace : WordTrace (prefixWord ++ tailWord_797308) baseStart_797308 baseEnd_797308 := by
    simpa [prefixWord, tailWord_797308, baseEnd_797308] using wordTrace_append hprefix tailTrace_797308
  have hstable : (prefixWord ++ tailWord_797308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797308).length < 2 ^ (prefixWord ++ tailWord_797308).sum := by decide
  have hdescent : baseEnd_797308 < baseStart_797308 := by decide
  rcases family_descends (prefixWord ++ tailWord_797308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797336 : List Nat := [2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_797336 : Nat := 118140960795 + 797336 * 2 ^ 59
def prefixEnd_797336 : Nat := 4983230072969 + 3 ^ 40 * 797336 * 2
def baseEnd_797336 : Nat := 121308625521006711980185

theorem tailTrace_797336 : CollatzResearch.WordTrace tailWord_797336 prefixEnd_797336 121308625521006711980185 := by
  unfold tailWord_797336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540616519697660496265931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19387488692930213995021241 14540616519697660496265931)
  ·
    refine ⟨21810924779546490744398897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14540616519697660496265931 21810924779546490744398897)
    ·
      refine ⟨16358193584659868058299173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21810924779546490744398897 16358193584659868058299173)
      ·
        refine ⟨3067161297123725260931095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16358193584659868058299173 3067161297123725260931095)
        ·
          refine ⟨4600741945685587891396643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067161297123725260931095 4600741945685587891396643)
          ·
            refine ⟨6901112918528381837094965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600741945685587891396643 6901112918528381837094965)
            ·
              refine ⟨646979336112035797227653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6901112918528381837094965 646979336112035797227653)
              ·
                refine ⟨121308625521006711980185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646979336112035797227653 121308625521006711980185)
                ·
                  rfl

theorem cell20_797336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_797336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797336 prefixEnd_797336 := by exact prefixLift 797336
  have htrace : WordTrace (prefixWord ++ tailWord_797336) baseStart_797336 baseEnd_797336 := by
    simpa [prefixWord, tailWord_797336, baseEnd_797336] using wordTrace_append hprefix tailTrace_797336
  have hstable : (prefixWord ++ tailWord_797336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797336).length < 2 ^ (prefixWord ++ tailWord_797336).sum := by decide
  have hdescent : baseEnd_797336 < baseStart_797336 := by decide
  rcases family_descends (prefixWord ++ tailWord_797336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797367 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_797367 : Nat := 118140960795 + 797367 * 2 ^ 59
def prefixEnd_797367 : Nat := 4983230072969 + 3 ^ 40 * 797367 * 2
def baseEnd_797367 : Nat := 363940025807721805907095

theorem tailTrace_797367 : CollatzResearch.WordTrace tailWord_797367 prefixEnd_797367 363940025807721805907095 := by
  unfold tailWord_797367
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082363702283013286910355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19388242468188675524606903 29082363702283013286910355)
  ·
    refine ⟨43623545553424519930365533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29082363702283013286910355 43623545553424519930365533)
    ·
      refine ⟨16358829582534194973887075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43623545553424519930365533 16358829582534194973887075)
      ·
        refine ⟨24538244373801292460830613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16358829582534194973887075 24538244373801292460830613)
        ·
          refine ⟨1150230205021935584101435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24538244373801292460830613 1150230205021935584101435)
          ·
            refine ⟨1725345307532903376152153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150230205021935584101435 1725345307532903376152153)
            ·
              refine ⟨1294008980649677532114115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725345307532903376152153 1294008980649677532114115)
              ·
                refine ⟨1941013470974516298171173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294008980649677532114115 1941013470974516298171173)
                ·
                  refine ⟨363940025807721805907095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941013470974516298171173 363940025807721805907095)
                  ·
                    rfl

theorem cell20_797367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_797367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797367 prefixEnd_797367 := by exact prefixLift 797367
  have htrace : WordTrace (prefixWord ++ tailWord_797367) baseStart_797367 baseEnd_797367 := by
    simpa [prefixWord, tailWord_797367, baseEnd_797367] using wordTrace_append hprefix tailTrace_797367
  have hstable : (prefixWord ++ tailWord_797367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797367).length < 2 ^ (prefixWord ++ tailWord_797367).sum := by decide
  have hdescent : baseEnd_797367 < baseStart_797367 := by decide
  rcases family_descends (prefixWord ++ tailWord_797367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797402 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_797402 : Nat := 118140960795 + 797402 * 2 ^ 59
def prefixEnd_797402 : Nat := 4983230072969 + 3 ^ 40 * 797402 * 2
def baseEnd_797402 : Nat := 363956000761417239740285

theorem tailTrace_797402 : CollatzResearch.WordTrace tailWord_797402 prefixEnd_797402 363956000761417239740285 := by
  unfold tailWord_797402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270910064289053566108615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19389093504770809509622973 7270910064289053566108615)
  ·
    refine ⟨10906365096433580349162923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270910064289053566108615 10906365096433580349162923)
    ·
      refine ⟨16359547644650370523744385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10906365096433580349162923 16359547644650370523744385)
      ·
        refine ⟨12269660733487777892808289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16359547644650370523744385 12269660733487777892808289)
        ·
          refine ⟨9202245550115833419606217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12269660733487777892808289 9202245550115833419606217)
          ·
            refine ⟨6901684162586875064704663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202245550115833419606217 6901684162586875064704663)
            ·
              refine ⟨10352526243880312597056995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901684162586875064704663 10352526243880312597056995)
              ·
                refine ⟨15528789365820468895585493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352526243880312597056995 15528789365820468895585493)
                ·
                  refine ⟨363956000761417239740285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15528789365820468895585493 363956000761417239740285)
                  ·
                    rfl

theorem cell20_797402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_797402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797402 prefixEnd_797402 := by exact prefixLift 797402
  have htrace : WordTrace (prefixWord ++ tailWord_797402) baseStart_797402 baseEnd_797402 := by
    simpa [prefixWord, tailWord_797402, baseEnd_797402] using wordTrace_append hprefix tailTrace_797402
  have hstable : (prefixWord ++ tailWord_797402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797402).length < 2 ^ (prefixWord ++ tailWord_797402).sum := by decide
  have hdescent : baseEnd_797402 < baseStart_797402 := by decide
  rcases family_descends (prefixWord ++ tailWord_797402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797428 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_797428 : Nat := 118140960795 + 797428 * 2 ^ 59
def prefixEnd_797428 : Nat := 4983230072969 + 3 ^ 40 * 797428 * 2
def baseEnd_797428 : Nat := 363967867869876704873513

theorem tailTrace_797428 : CollatzResearch.WordTrace tailWord_797428 prefixEnd_797428 363967867869876704873513 := by
  unfold tailWord_797428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542294277531010352440469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19389725703374680469920625 14542294277531010352440469)
  ·
    refine ⟨681670044259266110270647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14542294277531010352440469 681670044259266110270647)
    ·
      refine ⟨1022505066388899165405971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681670044259266110270647 1022505066388899165405971)
      ·
        refine ⟨1533757599583348748108957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022505066388899165405971 1533757599583348748108957)
        ·
          refine ⟨575159099843755780540859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1533757599583348748108957 575159099843755780540859)
          ·
            refine ⟨862738649765633670811289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575159099843755780540859 862738649765633670811289)
            ·
              refine ⟨647053987324225253108467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862738649765633670811289 647053987324225253108467)
              ·
                refine ⟨970580980986337879662701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647053987324225253108467 970580980986337879662701)
                ·
                  refine ⟨363967867869876704873513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970580980986337879662701 363967867869876704873513)
                  ·
                    rfl

theorem cell20_797428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_797428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797428 prefixEnd_797428 := by exact prefixLift 797428
  have htrace : WordTrace (prefixWord ++ tailWord_797428) baseStart_797428 baseEnd_797428 := by
    simpa [prefixWord, tailWord_797428, baseEnd_797428] using wordTrace_append hprefix tailTrace_797428
  have hstable : (prefixWord ++ tailWord_797428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797428).length < 2 ^ (prefixWord ++ tailWord_797428).sum := by decide
  have hdescent : baseEnd_797428 < baseStart_797428 := by decide
  rcases family_descends (prefixWord ++ tailWord_797428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797436 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_797436 : Nat := 118140960795 + 797436 * 2 ^ 59
def prefixEnd_797436 : Nat := 4983230072969 + 3 ^ 40 * 797436 * 2
def baseEnd_797436 : Nat := 363971519287864232606813

theorem tailTrace_797436 : CollatzResearch.WordTrace tailWord_797436 prefixEnd_797436 363971519287864232606813 := by
  unfold tailWord_797436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542440169516519035586081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19389920226022025380781441 14542440169516519035586081)
  ·
    refine ⟨10906830127137389276689561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14542440169516519035586081 10906830127137389276689561)
    ·
      refine ⟨8180122595353041957517171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10906830127137389276689561 8180122595353041957517171)
      ·
        refine ⟨12270183893029562936275757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8180122595353041957517171 12270183893029562936275757)
        ·
          refine ⟨4601318959886086101103409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12270183893029562936275757 4601318959886086101103409)
          ·
            refine ⟨3450989219914564575827557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601318959886086101103409 3450989219914564575827557)
            ·
              refine ⟨647060478733980857967667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3450989219914564575827557 647060478733980857967667)
              ·
                refine ⟨970590718100971286951501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647060478733980857967667 970590718100971286951501)
                ·
                  refine ⟨363971519287864232606813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970590718100971286951501 363971519287864232606813)
                  ·
                    rfl

theorem cell20_797436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_797436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797436 prefixEnd_797436 := by exact prefixLift 797436
  have htrace : WordTrace (prefixWord ++ tailWord_797436) baseStart_797436 baseEnd_797436 := by
    simpa [prefixWord, tailWord_797436, baseEnd_797436] using wordTrace_append hprefix tailTrace_797436
  have hstable : (prefixWord ++ tailWord_797436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797436).length < 2 ^ (prefixWord ++ tailWord_797436).sum := by decide
  have hdescent : baseEnd_797436 < baseStart_797436 := by decide
  rcases family_descends (prefixWord ++ tailWord_797436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797474 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_797474 : Nat := 118140960795 + 797474 * 2 ^ 59
def prefixEnd_797474 : Nat := 4983230072969 + 3 ^ 40 * 797474 * 2
def baseEnd_797474 : Nat := 363988863523304989339991

theorem tailTrace_797474 : CollatzResearch.WordTrace tailWord_797474 prefixEnd_797474 363988863523304989339991 := by
  unfold tailWord_797474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271566578223842640263869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19390844208596913707370317 7271566578223842640263869)
  ·
    refine ⟨2726837466833940990098951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7271566578223842640263869 2726837466833940990098951)
    ·
      refine ⟨4090256200250911485148427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726837466833940990098951 4090256200250911485148427)
      ·
        refine ⟨6135384300376367227722641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090256200250911485148427 6135384300376367227722641)
        ·
          refine ⟨4601538225282275420791981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135384300376367227722641 4601538225282275420791981)
          ·
            refine ⟨1725576834480853282796993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4601538225282275420791981 1725576834480853282796993)
            ·
              refine ⟨1294182625860639962097745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725576834480853282796993 1294182625860639962097745)
              ·
                refine ⟨970636969395479971573309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294182625860639962097745 970636969395479971573309)
                ·
                  refine ⟨363988863523304989339991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970636969395479971573309 363988863523304989339991)
                  ·
                    rfl

theorem cell20_797474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_797474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797474 prefixEnd_797474 := by exact prefixLift 797474
  have htrace : WordTrace (prefixWord ++ tailWord_797474) baseStart_797474 baseEnd_797474 := by
    simpa [prefixWord, tailWord_797474, baseEnd_797474] using wordTrace_append hprefix tailTrace_797474
  have hstable : (prefixWord ++ tailWord_797474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797474).length < 2 ^ (prefixWord ++ tailWord_797474).sum := by decide
  have hdescent : baseEnd_797474 < baseStart_797474 := by decide
  rcases family_descends (prefixWord ++ tailWord_797474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797540 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_797540 : Nat := 118140960795 + 797540 * 2 ^ 59
def prefixEnd_797540 : Nat := 4983230072969 + 3 ^ 40 * 797540 * 2
def baseEnd_797540 : Nat := 364018987721702093139721

theorem tailTrace_797540 : CollatzResearch.WordTrace tailWord_797540 prefixEnd_797540 364018987721702093139721 := by
  unfold tailWord_797540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544336765328131916479037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19392449020437509221972049 14544336765328131916479037)
  ·
    refine ⟨5454126286998049468679639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14544336765328131916479037 5454126286998049468679639)
    ·
      refine ⟨8181189430497074203019459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454126286998049468679639 8181189430497074203019459)
      ·
        refine ⟨12271784145745611304529189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181189430497074203019459 12271784145745611304529189)
        ·
          refine ⟨2300959527327302119599223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12271784145745611304529189 2300959527327302119599223)
          ·
            refine ⟨3451439290990953179398835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300959527327302119599223 3451439290990953179398835)
            ·
              refine ⟨5177158936486429769098253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451439290990953179398835 5177158936486429769098253)
              ·
                refine ⟨1941434601182411163411845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177158936486429769098253 1941434601182411163411845)
                ·
                  refine ⟨364018987721702093139721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941434601182411163411845 364018987721702093139721)
                  ·
                    rfl

theorem cell20_797540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_797540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797540 prefixEnd_797540 := by exact prefixLift 797540
  have htrace : WordTrace (prefixWord ++ tailWord_797540) baseStart_797540 baseEnd_797540 := by
    simpa [prefixWord, tailWord_797540, baseEnd_797540] using wordTrace_append hprefix tailTrace_797540
  have hstable : (prefixWord ++ tailWord_797540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797540).length < 2 ^ (prefixWord ++ tailWord_797540).sum := by decide
  have hdescent : baseEnd_797540 < baseStart_797540 := by decide
  rcases family_descends (prefixWord ++ tailWord_797540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797602 : List Nat := [3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_797602 : Nat := 118140960795 + 797602 * 2 ^ 59
def prefixEnd_797602 : Nat := 4983230072969 + 3 ^ 40 * 797602 * 2
def baseEnd_797602 : Nat := 121349095403701811024267

theorem tailTrace_797602 : CollatzResearch.WordTrace tailWord_797602 prefixEnd_797602 121349095403701811024267 := by
  unfold tailWord_797602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272733714107912105428765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19393956570954432281143373 7272733714107912105428765)
  ·
    refine ⟨2727275142790467039535787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7272733714107912105428765 2727275142790467039535787)
    ·
      refine ⟨4090912714185700559303681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727275142790467039535787 4090912714185700559303681)
      ·
        refine ⟨3068184535639275419477761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090912714185700559303681 3068184535639275419477761)
        ·
          refine ⟨2301138401729456564608321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068184535639275419477761 2301138401729456564608321)
          ·
            refine ⟨1725853801297092423456241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301138401729456564608321 1725853801297092423456241)
            ·
              refine ⟨1294390350972819317592181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725853801297092423456241 1294390350972819317592181)
              ·
                refine ⟨121349095403701811024267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294390350972819317592181 121349095403701811024267)
                ·
                  rfl

theorem cell20_797602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_797602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797602 prefixEnd_797602 := by exact prefixLift 797602
  have htrace : WordTrace (prefixWord ++ tailWord_797602) baseStart_797602 baseEnd_797602 := by
    simpa [prefixWord, tailWord_797602, baseEnd_797602] using wordTrace_append hprefix tailTrace_797602
  have hstable : (prefixWord ++ tailWord_797602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797602).length < 2 ^ (prefixWord ++ tailWord_797602).sum := by decide
  have hdescent : baseEnd_797602 < baseStart_797602 := by decide
  rcases family_descends (prefixWord ++ tailWord_797602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797647 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_797647 : Nat := 118140960795 + 797647 * 2 ^ 59
def prefixEnd_797647 : Nat := 4983230072969 + 3 ^ 40 * 797647 * 2
def baseEnd_797647 : Nat := 364067825437285276572617

theorem tailTrace_797647 : CollatzResearch.WordTrace tailWord_797647 prefixEnd_797647 364067825437285276572617 := by
  unfold tailWord_797647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092576141268621107103195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19395050760845747404735463 29092576141268621107103195)
  ·
    refine ⟨43638864211902931660654793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29092576141268621107103195 43638864211902931660654793)
    ·
      refine ⟨32729148158927198745491095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43638864211902931660654793 32729148158927198745491095)
      ·
        refine ⟨49093722238390798118236643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32729148158927198745491095 49093722238390798118236643)
        ·
          refine ⟨73640583357586197177354965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49093722238390798118236643 73640583357586197177354965)
          ·
            refine ⟨1725951172443426496344257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73640583357586197177354965 1725951172443426496344257)
            ·
              refine ⟨1294463379332569872258193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725951172443426496344257 1294463379332569872258193)
              ·
                refine ⟨970847534499427404193645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294463379332569872258193 970847534499427404193645)
                ·
                  refine ⟨364067825437285276572617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970847534499427404193645 364067825437285276572617)
                  ·
                    rfl

theorem cell20_797647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_797647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797647 prefixEnd_797647 := by exact prefixLift 797647
  have htrace : WordTrace (prefixWord ++ tailWord_797647) baseStart_797647 baseEnd_797647 := by
    simpa [prefixWord, tailWord_797647, baseEnd_797647] using wordTrace_append hprefix tailTrace_797647
  have hstable : (prefixWord ++ tailWord_797647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797647).length < 2 ^ (prefixWord ++ tailWord_797647).sum := by decide
  have hdescent : baseEnd_797647 < baseStart_797647 := by decide
  rcases family_descends (prefixWord ++ tailWord_797647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797650 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_797650 : Nat := 118140960795 + 797650 * 2 ^ 59
def prefixEnd_797650 : Nat := 4983230072969 + 3 ^ 40 * 797650 * 2
def baseEnd_797650 : Nat := 364069194719030599472605

theorem tailTrace_797650 : CollatzResearch.WordTrace tailWord_797650 prefixEnd_797650 364069194719030599472605 := by
  unfold tailWord_797650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273171390064438154865601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19395123706838501746308269 7273171390064438154865601)
  ·
    refine ⟨5454878542548328616149201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7273171390064438154865601 5454878542548328616149201)
    ·
      refine ⟨4091158906911246462111901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454878542548328616149201 4091158906911246462111901)
      ·
        refine ⟨1534184590091717423291963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4091158906911246462111901 1534184590091717423291963)
        ·
          refine ⟨2301276885137576134937945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534184590091717423291963 2301276885137576134937945)
          ·
            refine ⟨1725957663853182101203459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301276885137576134937945 1725957663853182101203459)
            ·
              refine ⟨2588936495779773151805189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725957663853182101203459 2588936495779773151805189)
              ·
                refine ⟨485425592958707465963473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2588936495779773151805189 485425592958707465963473)
                ·
                  refine ⟨364069194719030599472605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485425592958707465963473 364069194719030599472605)
                  ·
                    rfl

theorem cell20_797650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_797650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797650 prefixEnd_797650 := by exact prefixLift 797650
  have htrace : WordTrace (prefixWord ++ tailWord_797650) baseStart_797650 baseEnd_797650 := by
    simpa [prefixWord, tailWord_797650, baseEnd_797650] using wordTrace_append hprefix tailTrace_797650
  have hstable : (prefixWord ++ tailWord_797650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797650).length < 2 ^ (prefixWord ++ tailWord_797650).sum := by decide
  have hdescent : baseEnd_797650 < baseStart_797650 := by decide
  rcases family_descends (prefixWord ++ tailWord_797650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797698 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_797698 : Nat := 118140960795 + 797698 * 2 ^ 59
def prefixEnd_797698 : Nat := 4983230072969 + 3 ^ 40 * 797698 * 2
def baseEnd_797698 : Nat := 364091103226955765872409

theorem tailTrace_797698 : CollatzResearch.WordTrace tailWord_797698 prefixEnd_797698 364091103226955765872409 := by
  unfold tailWord_797698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273609066020964204302437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19396290842722571211473165 7273609066020964204302437)
  ·
    refine ⟨1363801699878930788306707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7273609066020964204302437 1363801699878930788306707)
    ·
      refine ⟨2045702549818396182460061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363801699878930788306707 2045702549818396182460061)
      ·
        refine ⟨767138456181898568422523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2045702549818396182460061 767138456181898568422523)
        ·
          refine ⟨1150707684272847852633785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767138456181898568422523 1150707684272847852633785)
          ·
            refine ⟨863030763204635889475339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1150707684272847852633785 863030763204635889475339)
            ·
              refine ⟨1294546144806953834213009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863030763204635889475339 1294546144806953834213009)
              ·
                refine ⟨970909608605215375659757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294546144806953834213009 970909608605215375659757)
                ·
                  refine ⟨364091103226955765872409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970909608605215375659757 364091103226955765872409)
                  ·
                    rfl

theorem cell20_797698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_797698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797698 prefixEnd_797698 := by exact prefixLift 797698
  have htrace : WordTrace (prefixWord ++ tailWord_797698) baseStart_797698 baseEnd_797698 := by
    simpa [prefixWord, tailWord_797698, baseEnd_797698] using wordTrace_append hprefix tailTrace_797698
  have hstable : (prefixWord ++ tailWord_797698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797698).length < 2 ^ (prefixWord ++ tailWord_797698).sum := by decide
  have hdescent : baseEnd_797698 < baseStart_797698 := by decide
  rcases family_descends (prefixWord ++ tailWord_797698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797730 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_797730 : Nat := 118140960795 + 797730 * 2 ^ 59
def prefixEnd_797730 : Nat := 4983230072969 + 3 ^ 40 * 797730 * 2
def baseEnd_797730 : Nat := 364105708898905876805611

theorem tailTrace_797730 : CollatzResearch.WordTrace tailWord_797730 prefixEnd_797730 364105708898905876805611 := by
  unfold tailWord_797730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273900849991981570593661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19397068933311950854916429 7273900849991981570593661)
  ·
    refine ⟨2727712818746993088972623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7273900849991981570593661 2727712818746993088972623)
    ·
      refine ⟨4091569228120489633458935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727712818746993088972623 4091569228120489633458935)
      ·
        refine ⟨6137353842180734450188403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091569228120489633458935 6137353842180734450188403)
        ·
          refine ⟨9206030763271101675282605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137353842180734450188403 9206030763271101675282605)
          ·
            refine ⟨3452261536226663128230977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9206030763271101675282605 3452261536226663128230977)
            ·
              refine ⟨2589196152169997346173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452261536226663128230977 2589196152169997346173233)
              ·
                refine ⟨1941897114127498009629925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589196152169997346173233 1941897114127498009629925)
                ·
                  refine ⟨364105708898905876805611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941897114127498009629925 364105708898905876805611)
                  ·
                    rfl

theorem cell20_797730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_797730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797730 prefixEnd_797730 := by exact prefixLift 797730
  have htrace : WordTrace (prefixWord ++ tailWord_797730) baseStart_797730 baseEnd_797730 := by
    simpa [prefixWord, tailWord_797730, baseEnd_797730] using wordTrace_append hprefix tailTrace_797730
  have hstable : (prefixWord ++ tailWord_797730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797730).length < 2 ^ (prefixWord ++ tailWord_797730).sum := by decide
  have hdescent : baseEnd_797730 < baseStart_797730 := by decide
  rcases family_descends (prefixWord ++ tailWord_797730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797778 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_797778 : Nat := 118140960795 + 797778 * 2 ^ 59
def prefixEnd_797778 : Nat := 4983230072969 + 3 ^ 40 * 797778 * 2
def baseEnd_797778 : Nat := 364127617406831043205415

theorem tailTrace_797778 : CollatzResearch.WordTrace tailWord_797778 prefixEnd_797778 364127617406831043205415 := by
  unfold tailWord_797778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274338525948507620030497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19398236069196020320081325 7274338525948507620030497)
  ·
    refine ⟨5455753894461380715022873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7274338525948507620030497 5455753894461380715022873)
    ·
      refine ⟨4091815420846035536267155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5455753894461380715022873 4091815420846035536267155)
      ·
        refine ⟨6137723131269053304400733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091815420846035536267155 6137723131269053304400733)
        ·
          refine ⟨2301646174225894989150275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6137723131269053304400733 2301646174225894989150275)
          ·
            refine ⟨3452469261338842483725413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301646174225894989150275 3452469261338842483725413)
            ·
              refine ⟨647337986501032965698515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3452469261338842483725413 647337986501032965698515)
              ·
                refine ⟨971006979751549448547773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647337986501032965698515 971006979751549448547773)
                ·
                  refine ⟨364127617406831043205415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971006979751549448547773 364127617406831043205415)
                  ·
                    rfl

theorem cell20_797778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_797778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797778 prefixEnd_797778 := by exact prefixLift 797778
  have htrace : WordTrace (prefixWord ++ tailWord_797778) baseStart_797778 baseEnd_797778 := by
    simpa [prefixWord, tailWord_797778, baseEnd_797778] using wordTrace_append hprefix tailTrace_797778
  have hstable : (prefixWord ++ tailWord_797778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797778).length < 2 ^ (prefixWord ++ tailWord_797778).sum := by decide
  have hdescent : baseEnd_797778 < baseStart_797778 := by decide
  rcases family_descends (prefixWord ++ tailWord_797778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797813 : List Nat := [1, 3, 4, 3, 9]
def baseStart_797813 : Nat := 118140960795 + 797813 * 2 ^ 59
def prefixEnd_797813 : Nat := 4983230072969 + 3 ^ 40 * 797813 * 2
def baseEnd_797813 : Nat := 4495599905685512062205

theorem tailTrace_797813 : CollatzResearch.WordTrace tailWord_797813 prefixEnd_797813 4495599905685512062205 := by
  unfold tailWord_797813
  simp only [CollatzResearch.WordTrace]
  refine ⟨29098630658667231457646093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19399087105778154305097395 29098630658667231457646093)
  ·
    refine ⟨10911986497000211796617285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29098630658667231457646093 10911986497000211796617285)
    ·
      refine ⟨2045997468187539711865741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10911986497000211796617285 2045997468187539711865741)
      ·
        refine ⟨767249050570327391949653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2045997468187539711865741 767249050570327391949653)
        ·
          refine ⟨4495599905685512062205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 767249050570327391949653 4495599905685512062205)
          ·
            rfl

theorem cell20_797813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 9].length) (baseStart_797813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797813 prefixEnd_797813 := by exact prefixLift 797813
  have htrace : WordTrace (prefixWord ++ tailWord_797813) baseStart_797813 baseEnd_797813 := by
    simpa [prefixWord, tailWord_797813, baseEnd_797813] using wordTrace_append hprefix tailTrace_797813
  have hstable : (prefixWord ++ tailWord_797813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797813).length < 2 ^ (prefixWord ++ tailWord_797813).sum := by decide
  have hdescent : baseEnd_797813 < baseStart_797813 := by decide
  rcases family_descends (prefixWord ++ tailWord_797813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797827 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_797827 : Nat := 118140960795 + 797827 * 2 ^ 59
def prefixEnd_797827 : Nat := 4983230072969 + 3 ^ 40 * 797827 * 2
def baseEnd_797827 : Nat := 364149982342004650571881

theorem tailTrace_797827 : CollatzResearch.WordTrace tailWord_797827 prefixEnd_797827 364149982342004650571881 := by
  unfold tailWord_797827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29099141280616511848655735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19399427520411007899103823 29099141280616511848655735)
  ·
    refine ⟨43648711920924767772983603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29099141280616511848655735 43648711920924767772983603)
    ·
      refine ⟨65473067881387151659475405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43648711920924767772983603 65473067881387151659475405)
      ·
        refine ⟨24552400455520181872303277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65473067881387151659475405 24552400455520181872303277)
        ·
          refine ⟨9207150170820068202113729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24552400455520181872303277 9207150170820068202113729)
          ·
            refine ⟨6905362628115051151585297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9207150170820068202113729 6905362628115051151585297)
            ·
              refine ⟨5179021971086288363688973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6905362628115051151585297 5179021971086288363688973)
              ·
                refine ⟨1942133239157358136383365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179021971086288363688973 1942133239157358136383365)
                ·
                  refine ⟨364149982342004650571881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942133239157358136383365 364149982342004650571881)
                  ·
                    rfl

theorem cell20_797827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_797827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797827 prefixEnd_797827 := by exact prefixLift 797827
  have htrace : WordTrace (prefixWord ++ tailWord_797827) baseStart_797827 baseEnd_797827 := by
    simpa [prefixWord, tailWord_797827, baseEnd_797827] using wordTrace_append hprefix tailTrace_797827
  have hstable : (prefixWord ++ tailWord_797827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797827).length < 2 ^ (prefixWord ++ tailWord_797827).sum := by decide
  have hdescent : baseEnd_797827 < baseStart_797827 := by decide
  rcases family_descends (prefixWord ++ tailWord_797827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797861 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 2]
def baseStart_797861 : Nat := 118140960795 + 797861 * 2 ^ 59
def prefixEnd_797861 : Nat := 4983230072969 + 3 ^ 40 * 797861 * 2
def baseEnd_797861 : Nat := 364165500868451643438409

theorem tailTrace_797861 : CollatzResearch.WordTrace tailWord_797861 prefixEnd_797861 364165500868451643438409 := by
  unfold tailWord_797861
  simp only [CollatzResearch.WordTrace]
  refine ⟨29100381362493335655393437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19400254241662223770262291 29100381362493335655393437)
  ·
    refine ⟨10912643010935000870772539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29100381362493335655393437 10912643010935000870772539)
    ·
      refine ⟨16368964516402501306158809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912643010935000870772539 16368964516402501306158809)
      ·
        refine ⟨12276723387301875979619107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16368964516402501306158809 12276723387301875979619107)
        ·
          refine ⟨18415085080952813969428661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12276723387301875979619107 18415085080952813969428661)
          ·
            refine ⟨1726414226339326309633937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18415085080952813969428661 1726414226339326309633937)
            ·
              refine ⟨1294810669754494732225453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726414226339326309633937 1294810669754494732225453)
              ·
                refine ⟨485554001157935524584545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294810669754494732225453 485554001157935524584545)
                ·
                  refine ⟨364165500868451643438409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485554001157935524584545 364165500868451643438409)
                  ·
                    rfl

theorem cell20_797861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_797861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797861 prefixEnd_797861 := by exact prefixLift 797861
  have htrace : WordTrace (prefixWord ++ tailWord_797861) baseStart_797861 baseEnd_797861 := by
    simpa [prefixWord, tailWord_797861, baseEnd_797861] using wordTrace_append hprefix tailTrace_797861
  have hstable : (prefixWord ++ tailWord_797861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797861).length < 2 ^ (prefixWord ++ tailWord_797861).sum := by decide
  have hdescent : baseEnd_797861 < baseStart_797861 := by decide
  rcases family_descends (prefixWord ++ tailWord_797861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797896 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_797896 : Nat := 118140960795 + 797896 * 2 ^ 59
def prefixEnd_797896 : Nat := 4983230072969 + 3 ^ 40 * 797896 * 2
def baseEnd_797896 : Nat := 364181475822147077271599

theorem tailTrace_797896 : CollatzResearch.WordTrace tailWord_797896 prefixEnd_797896 364181475822147077271599 := by
  unfold tailWord_797896
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550828958683268316458771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19401105278244357755278361 14550828958683268316458771)
  ·
    refine ⟨21826243438024902474688157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14550828958683268316458771 21826243438024902474688157)
    ·
      refine ⟨8184841289259338428008059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21826243438024902474688157 8184841289259338428008059)
      ·
        refine ⟨12277261933889007642012089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184841289259338428008059 12277261933889007642012089)
        ·
          refine ⟨9207946450416755731509067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12277261933889007642012089 9207946450416755731509067)
          ·
            refine ⟨13811919675625133597263601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207946450416755731509067 13811919675625133597263601)
            ·
              refine ⟨10358939756718850197947701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13811919675625133597263601 10358939756718850197947701)
              ·
                refine ⟨971150602192392206057597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10358939756718850197947701 971150602192392206057597)
                ·
                  refine ⟨364181475822147077271599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971150602192392206057597 364181475822147077271599)
                  ·
                    rfl

theorem cell20_797896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_797896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797896 prefixEnd_797896 := by exact prefixLift 797896
  have htrace : WordTrace (prefixWord ++ tailWord_797896) baseStart_797896 baseEnd_797896 := by
    simpa [prefixWord, tailWord_797896, baseEnd_797896] using wordTrace_append hprefix tailTrace_797896
  have hstable : (prefixWord ++ tailWord_797896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797896).length < 2 ^ (prefixWord ++ tailWord_797896).sum := by decide
  have hdescent : baseEnd_797896 < baseStart_797896 := by decide
  rcases family_descends (prefixWord ++ tailWord_797896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797934 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_797934 : Nat := 118140960795 + 797934 * 2 ^ 59
def prefixEnd_797934 : Nat := 4983230072969 + 3 ^ 40 * 797934 * 2
def baseEnd_797934 : Nat := 364198820057587834004777

theorem tailTrace_797934 : CollatzResearch.WordTrace tailWord_797934 prefixEnd_797934 364198820057587834004777 := by
  unfold tailWord_797934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637880486403608640350107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19402029260819246081867237 3637880486403608640350107)
  ·
    refine ⟨5456820729605412960525161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3637880486403608640350107 5456820729605412960525161)
    ·
      refine ⟨4092615547204059720393871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5456820729605412960525161 4092615547204059720393871)
      ·
        refine ⟨6138923320806089580590807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092615547204059720393871 6138923320806089580590807)
        ·
          refine ⟨9208384981209134370886211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138923320806089580590807 9208384981209134370886211)
          ·
            refine ⟨13812577471813701556329317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208384981209134370886211 13812577471813701556329317)
            ·
              refine ⟨2589858275965069041811747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13812577471813701556329317 2589858275965069041811747)
              ·
                refine ⟨3884787413947603562717621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589858275965069041811747 3884787413947603562717621)
                ·
                  refine ⟨364198820057587834004777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884787413947603562717621 364198820057587834004777)
                  ·
                    rfl

theorem cell20_797934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_797934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797934 prefixEnd_797934 := by exact prefixLift 797934
  have htrace : WordTrace (prefixWord ++ tailWord_797934) baseStart_797934 baseEnd_797934 := by
    simpa [prefixWord, tailWord_797934, baseEnd_797934] using wordTrace_append hprefix tailTrace_797934
  have hstable : (prefixWord ++ tailWord_797934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797934).length < 2 ^ (prefixWord ++ tailWord_797934).sum := by decide
  have hdescent : baseEnd_797934 < baseStart_797934 := by decide
  rcases family_descends (prefixWord ++ tailWord_797934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797940 : List Nat := [2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_797940 : Nat := 118140960795 + 797940 * 2 ^ 59
def prefixEnd_797940 : Nat := 4983230072969 + 3 ^ 40 * 797940 * 2
def baseEnd_797940 : Nat := 121400519540359493268251

theorem tailTrace_797940 : CollatzResearch.WordTrace tailWord_797940 prefixEnd_797940 121400519540359493268251 := by
  unfold tailWord_797940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14551631364603566073759637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19402175152804754765012849 14551631364603566073759637)
  ·
    refine ⟨682107720215792159707483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14551631364603566073759637 682107720215792159707483)
    ·
      refine ⟨1023161580323688239561225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682107720215792159707483 1023161580323688239561225)
      ·
        refine ⟨767371185242766179670919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023161580323688239561225 767371185242766179670919)
        ·
          refine ⟨1151056777864149269506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767371185242766179670919 1151056777864149269506379)
          ·
            refine ⟨1726585166796223904259569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151056777864149269506379 1726585166796223904259569)
            ·
              refine ⟨1294938875097167928194677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726585166796223904259569 1294938875097167928194677)
              ·
                refine ⟨121400519540359493268251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294938875097167928194677 121400519540359493268251)
                ·
                  rfl

theorem cell20_797940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_797940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797940 prefixEnd_797940 := by exact prefixLift 797940
  have htrace : WordTrace (prefixWord ++ tailWord_797940) baseStart_797940 baseEnd_797940 := by
    simpa [prefixWord, tailWord_797940, baseEnd_797940] using wordTrace_append hprefix tailTrace_797940
  have hstable : (prefixWord ++ tailWord_797940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797940).length < 2 ^ (prefixWord ++ tailWord_797940).sum := by decide
  have hdescent : baseEnd_797940 < baseStart_797940 := by decide
  rcases family_descends (prefixWord ++ tailWord_797940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797951 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_797951 : Nat := 118140960795 + 797951 * 2 ^ 59
def prefixEnd_797951 : Nat := 4983230072969 + 3 ^ 40 * 797951 * 2
def baseEnd_797951 : Nat := 364206579320811330438041

theorem tailTrace_797951 : CollatzResearch.WordTrace tailWord_797951 prefixEnd_797951 364206579320811330438041 := by
  unfold tailWord_797951
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103663932167281026169707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19402442621444854017446471 29103663932167281026169707)
  ·
    refine ⟨43655495898250921539254561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29103663932167281026169707 43655495898250921539254561)
    ·
      refine ⟨32741621923688191154440921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43655495898250921539254561 32741621923688191154440921)
      ·
        refine ⟨24556216442766143365830691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32741621923688191154440921 24556216442766143365830691)
        ·
          refine ⟨36834324664149215048746037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24556216442766143365830691 36834324664149215048746037)
          ·
            refine ⟨3453217937263988910819941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36834324664149215048746037 3453217937263988910819941)
            ·
              refine ⟨647478363236997920778739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3453217937263988910819941 647478363236997920778739)
              ·
                refine ⟨971217544855496881168109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647478363236997920778739 971217544855496881168109)
                ·
                  refine ⟨364206579320811330438041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971217544855496881168109 364206579320811330438041)
                  ·
                    rfl

theorem cell20_797951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_797951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797951 prefixEnd_797951 := by exact prefixLift 797951
  have htrace : WordTrace (prefixWord ++ tailWord_797951) baseStart_797951 baseEnd_797951 := by
    simpa [prefixWord, tailWord_797951, baseEnd_797951] using wordTrace_append hprefix tailTrace_797951
  have hstable : (prefixWord ++ tailWord_797951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797951).length < 2 ^ (prefixWord ++ tailWord_797951).sum := by decide
  have hdescent : baseEnd_797951 < baseStart_797951 := by decide
  rcases family_descends (prefixWord ++ tailWord_797951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797982 : List Nat := [4, 3, 2, 1, 2, 8]
def baseStart_797982 : Nat := 118140960795 + 797982 * 2 ^ 59
def prefixEnd_797982 : Nat := 4983230072969 + 3 ^ 40 * 797982 * 2
def baseEnd_797982 : Nat := 13489656613537518533503

theorem tailTrace_797982 : CollatzResearch.WordTrace tailWord_797982 prefixEnd_797982 13489656613537518533503 := by
  unfold tailWord_797982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638099324381871665068525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19403196396703315547032133 3638099324381871665068525)
  ·
    refine ⟨1364287246643201874400697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3638099324381871665068525 1364287246643201874400697)
    ·
      refine ⟨1023215434982401405800523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364287246643201874400697 1023215434982401405800523)
      ·
        refine ⟨1534823152473602108700785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023215434982401405800523 1534823152473602108700785)
        ·
          refine ⟨1151117364355201581525589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534823152473602108700785 1151117364355201581525589)
          ·
            refine ⟨13489656613537518533503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1151117364355201581525589 13489656613537518533503)
            ·
              rfl

theorem cell20_797982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 8].length) (baseStart_797982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797982 prefixEnd_797982 := by exact prefixLift 797982
  have htrace : WordTrace (prefixWord ++ tailWord_797982) baseStart_797982 baseEnd_797982 := by
    simpa [prefixWord, tailWord_797982, baseEnd_797982] using wordTrace_append hprefix tailTrace_797982
  have hstable : (prefixWord ++ tailWord_797982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797982).length < 2 ^ (prefixWord ++ tailWord_797982).sum := by decide
  have hdescent : baseEnd_797982 < baseStart_797982 := by decide
  rcases family_descends (prefixWord ++ tailWord_797982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797986 : List Nat := [3, 3, 1, 1, 12]
def baseStart_797986 : Nat := 118140960795 + 797986 * 2 ^ 59
def prefixEnd_797986 : Nat := 4983230072969 + 3 ^ 40 * 797986 * 2
def baseEnd_797986 : Nat := 4496574744129713139151

theorem tailTrace_797986 : CollatzResearch.WordTrace tailWord_797986 prefixEnd_797986 4496574744129713139151 := by
  unfold tailWord_797986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276235121760120500923453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19403293658026988002462541 7276235121760120500923453)
  ·
    refine ⟨2728588170660045187846295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7276235121760120500923453 2728588170660045187846295)
    ·
      refine ⟨4092882255990067781769443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728588170660045187846295 4092882255990067781769443)
      ·
        refine ⟨6139323383985101672654165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092882255990067781769443 6139323383985101672654165)
        ·
          refine ⟨4496574744129713139151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6139323383985101672654165 4496574744129713139151)
          ·
            rfl

theorem cell20_797986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 12].length) (baseStart_797986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797986 prefixEnd_797986 := by exact prefixLift 797986
  have htrace : WordTrace (prefixWord ++ tailWord_797986) baseStart_797986 baseEnd_797986 := by
    simpa [prefixWord, tailWord_797986, baseEnd_797986] using wordTrace_append hprefix tailTrace_797986
  have hstable : (prefixWord ++ tailWord_797986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797986).length < 2 ^ (prefixWord ++ tailWord_797986).sum := by decide
  have hdescent : baseEnd_797986 < baseStart_797986 := by decide
  rcases family_descends (prefixWord ++ tailWord_797986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797989 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_797989 : Nat := 118140960795 + 797989 * 2 ^ 59
def prefixEnd_797989 : Nat := 4983230072969 + 3 ^ 40 * 797989 * 2
def baseEnd_797989 : Nat := 364223923556252087171219

theorem tailTrace_797989 : CollatzResearch.WordTrace tailWord_797989 prefixEnd_797989 364223923556252087171219 := by
  unfold tailWord_797989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105049906029613516053021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19403366604019742344035347 29105049906029613516053021)
  ·
    refine ⟨10914393714761105068519883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29105049906029613516053021 10914393714761105068519883)
    ·
      refine ⟨16371590572141657602779825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10914393714761105068519883 16371590572141657602779825)
      ·
        refine ⟨12278692929106243202084869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16371590572141657602779825 12278692929106243202084869)
        ·
          refine ⟨2302254924207420600390913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12278692929106243202084869 2302254924207420600390913)
          ·
            refine ⟨1726691193155565450293185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302254924207420600390913 1726691193155565450293185)
            ·
              refine ⟨1295018394866674087719889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726691193155565450293185 1295018394866674087719889)
              ·
                refine ⟨971263796150005565789917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295018394866674087719889 971263796150005565789917)
                ·
                  refine ⟨364223923556252087171219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971263796150005565789917 364223923556252087171219)
                  ·
                    rfl

theorem cell20_797989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_797989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797989 prefixEnd_797989 := by exact prefixLift 797989
  have htrace : WordTrace (prefixWord ++ tailWord_797989) baseStart_797989 baseEnd_797989 := by
    simpa [prefixWord, tailWord_797989, baseEnd_797989] using wordTrace_append hprefix tailTrace_797989
  have hstable : (prefixWord ++ tailWord_797989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797989).length < 2 ^ (prefixWord ++ tailWord_797989).sum := by decide
  have hdescent : baseEnd_797989 < baseStart_797989 := by decide
  rcases family_descends (prefixWord ++ tailWord_797989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797992 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_797992 : Nat := 118140960795 + 797992 * 2 ^ 59
def prefixEnd_797992 : Nat := 4983230072969 + 3 ^ 40 * 797992 * 2
def baseEnd_797992 : Nat := 364225292837997410071207

theorem tailTrace_797992 : CollatzResearch.WordTrace tailWord_797992 prefixEnd_797992 364225292837997410071207 := by
  unfold tailWord_797992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14552579662509372514206115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19403439550012496685608153 14552579662509372514206115)
  ·
    refine ⟨21828869493764058771309173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14552579662509372514206115 21828869493764058771309173)
    ·
      refine ⟨2046456515040380509810235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21828869493764058771309173 2046456515040380509810235)
      ·
        refine ⟨3069684772560570764715353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046456515040380509810235 3069684772560570764715353)
        ·
          refine ⟨2302263579420428073536515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3069684772560570764715353 2302263579420428073536515)
          ·
            refine ⟨3453395369130642110304773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302263579420428073536515 3453395369130642110304773)
            ·
              refine ⟨647511631711995395682145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3453395369130642110304773 647511631711995395682145)
              ·
                refine ⟨485633723783996546761609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647511631711995395682145 485633723783996546761609)
                ·
                  refine ⟨364225292837997410071207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485633723783996546761609 364225292837997410071207)
                  ·
                    rfl

theorem cell20_797992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_797992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_797992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_797992 prefixEnd_797992 := by exact prefixLift 797992
  have htrace : WordTrace (prefixWord ++ tailWord_797992) baseStart_797992 baseEnd_797992 := by
    simpa [prefixWord, tailWord_797992, baseEnd_797992] using wordTrace_append hprefix tailTrace_797992
  have hstable : (prefixWord ++ tailWord_797992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797992).length < 2 ^ (prefixWord ++ tailWord_797992).sum := by decide
  have hdescent : baseEnd_797992 < baseStart_797992 := by decide
  rcases family_descends (prefixWord ++ tailWord_797992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798003 : List Nat := [1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_798003 : Nat := 118140960795 + 798003 * 2 ^ 59
def prefixEnd_798003 : Nat := 4983230072969 + 3 ^ 40 * 798003 * 2
def baseEnd_798003 : Nat := 121410104512576753568165

theorem tailTrace_798003 : CollatzResearch.WordTrace tailWord_798003 prefixEnd_798003 121410104512576753568165 := by
  unfold tailWord_798003
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105560527978893907062663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19403707018652595938041775 29105560527978893907062663)
  ·
    refine ⟨43658340791968340860593995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29105560527978893907062663 43658340791968340860593995)
    ·
      refine ⟨65487511187952511290890993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43658340791968340860593995 65487511187952511290890993)
      ·
        refine ⟨49115633390964383468168245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65487511187952511290890993 49115633390964383468168245)
        ·
          refine ⟨4604590630402910950140773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49115633390964383468168245 4604590630402910950140773)
          ·
            refine ⟨863360743200545803151395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4604590630402910950140773 863360743200545803151395)
            ·
              refine ⟨1295041114800818704727093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863360743200545803151395 1295041114800818704727093)
              ·
                refine ⟨121410104512576753568165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1295041114800818704727093 121410104512576753568165)
                ·
                  rfl

theorem cell20_798003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_798003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798003 prefixEnd_798003 := by exact prefixLift 798003
  have htrace : WordTrace (prefixWord ++ tailWord_798003) baseStart_798003 baseEnd_798003 := by
    simpa [prefixWord, tailWord_798003, baseEnd_798003] using wordTrace_append hprefix tailTrace_798003
  have hstable : (prefixWord ++ tailWord_798003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798003).length < 2 ^ (prefixWord ++ tailWord_798003).sum := by decide
  have hdescent : baseEnd_798003 < baseStart_798003 := by decide
  rcases family_descends (prefixWord ++ tailWord_798003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798010 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_798010 : Nat := 118140960795 + 798010 * 2 ^ 59
def prefixEnd_798010 : Nat := 4983230072969 + 3 ^ 40 * 798010 * 2
def baseEnd_798010 : Nat := 364233508528469347471133

theorem tailTrace_798010 : CollatzResearch.WordTrace tailWord_798010 prefixEnd_798010 364233508528469347471133 := by
  unfold tailWord_798010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276453959738383525641871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19403877225969022735044989 7276453959738383525641871)
  ·
    refine ⟨10914680939607575288462807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7276453959738383525641871 10914680939607575288462807)
    ·
      refine ⟨16372021409411362932694211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10914680939607575288462807 16372021409411362932694211)
      ·
        refine ⟨24558032114117044399041317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16372021409411362932694211 24558032114117044399041317)
        ·
          refine ⟨4604631021396945824820247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24558032114117044399041317 4604631021396945824820247)
          ·
            refine ⟨6906946532095418737230371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604631021396945824820247 6906946532095418737230371)
            ·
              refine ⟨10360419798143128105845557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906946532095418737230371 10360419798143128105845557)
              ·
                refine ⟨971289356075918259923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10360419798143128105845557 971289356075918259923021)
                ·
                  refine ⟨364233508528469347471133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971289356075918259923021 364233508528469347471133)
                  ·
                    rfl

theorem cell20_798010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_798010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798010 prefixEnd_798010 := by exact prefixLift 798010
  have htrace : WordTrace (prefixWord ++ tailWord_798010) baseStart_798010 baseEnd_798010 := by
    simpa [prefixWord, tailWord_798010, baseEnd_798010] using wordTrace_append hprefix tailTrace_798010
  have hstable : (prefixWord ++ tailWord_798010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798010).length < 2 ^ (prefixWord ++ tailWord_798010).sum := by decide
  have hdescent : baseEnd_798010 < baseStart_798010 := by decide
  rcases family_descends (prefixWord ++ tailWord_798010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798013 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_798013 : Nat := 118140960795 + 798013 * 2 ^ 59
def prefixEnd_798013 : Nat := 4983230072969 + 3 ^ 40 * 798013 * 2
def baseEnd_798013 : Nat := 364234877810214670371121

theorem tailTrace_798013 : CollatzResearch.WordTrace tailWord_798013 prefixEnd_798013 364234877810214670371121 := by
  unfold tailWord_798013
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105925257942665614926693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19403950171961777076617795 29105925257942665614926693)
  ·
    refine ⟨5457360985864249802798755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29105925257942665614926693 5457360985864249802798755)
    ·
      refine ⟨8186041478796374704198133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457360985864249802798755 8186041478796374704198133)
      ·
        refine ⟨767441388637160128518575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8186041478796374704198133 767441388637160128518575)
        ·
          refine ⟨1151162082955740192777863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767441388637160128518575 1151162082955740192777863)
          ·
            refine ⟨1726743124433610289166795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151162082955740192777863 1726743124433610289166795)
            ·
              refine ⟨2590114686650415433750193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726743124433610289166795 2590114686650415433750193)
              ·
                refine ⟨1942586014987811575312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590114686650415433750193 1942586014987811575312645)
                ·
                  refine ⟨364234877810214670371121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942586014987811575312645 364234877810214670371121)
                  ·
                    rfl

theorem cell20_798013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_798013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798013 prefixEnd_798013 := by exact prefixLift 798013
  have htrace : WordTrace (prefixWord ++ tailWord_798013) baseStart_798013 baseEnd_798013 := by
    simpa [prefixWord, tailWord_798013, baseEnd_798013] using wordTrace_append hprefix tailTrace_798013
  have hstable : (prefixWord ++ tailWord_798013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798013).length < 2 ^ (prefixWord ++ tailWord_798013).sum := by decide
  have hdescent : baseEnd_798013 < baseStart_798013 := by decide
  rcases family_descends (prefixWord ++ tailWord_798013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798048 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_798048 : Nat := 118140960795 + 798048 * 2 ^ 59
def prefixEnd_798048 : Nat := 4983230072969 + 3 ^ 40 * 798048 * 2
def baseEnd_798048 : Nat := 364250852763910104204311

theorem tailTrace_798048 : CollatzResearch.WordTrace tailWord_798048 prefixEnd_798048 364250852763910104204311 := by
  unfold tailWord_798048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553600906407933296225399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19404801208543911061633865 14553600906407933296225399)
  ·
    refine ⟨21830401359611899944338099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14553600906407933296225399 21830401359611899944338099)
    ·
      refine ⟨32745602039417849916507149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21830401359611899944338099 32745602039417849916507149)
      ·
        refine ⟨12279600764781693718690181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32745602039417849916507149 12279600764781693718690181)
        ·
          refine ⟨2302425143396567572254409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12279600764781693718690181 2302425143396567572254409)
          ·
            refine ⟨1726818857547425679190807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302425143396567572254409 1726818857547425679190807)
            ·
              refine ⟨2590228286321138518786211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726818857547425679190807 2590228286321138518786211)
              ·
                refine ⟨3885342429481707778179317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590228286321138518786211 3885342429481707778179317)
                ·
                  refine ⟨364250852763910104204311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3885342429481707778179317 364250852763910104204311)
                  ·
                    rfl

theorem cell20_798048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_798048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798048 prefixEnd_798048 := by exact prefixLift 798048
  have htrace : WordTrace (prefixWord ++ tailWord_798048) baseStart_798048 baseEnd_798048 := by
    simpa [prefixWord, tailWord_798048, baseEnd_798048] using wordTrace_append hprefix tailTrace_798048
  have hstable : (prefixWord ++ tailWord_798048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798048).length < 2 ^ (prefixWord ++ tailWord_798048).sum := by decide
  have hdescent : baseEnd_798048 < baseStart_798048 := by decide
  rcases family_descends (prefixWord ++ tailWord_798048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798120 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_798120 : Nat := 118140960795 + 798120 * 2 ^ 59
def prefixEnd_798120 : Nat := 4983230072969 + 3 ^ 40 * 798120 * 2
def baseEnd_798120 : Nat := 364283715525797853804017

theorem tailTrace_798120 : CollatzResearch.WordTrace tailWord_798120 prefixEnd_798120 364283715525797853804017 := by
  unfold tailWord_798120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554913934277511444535907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19406551912370015259381209 14554913934277511444535907)
  ·
    refine ⟨21832370901416267166803861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554913934277511444535907 21832370901416267166803861)
    ·
      refine ⟨1023392386003887523443931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21832370901416267166803861 1023392386003887523443931)
      ·
        refine ⟨1535088579005831285165897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023392386003887523443931 1535088579005831285165897)
        ·
          refine ⟨1151316434254373463874423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535088579005831285165897 1151316434254373463874423)
          ·
            refine ⟨1726974651381560195811635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151316434254373463874423 1726974651381560195811635)
            ·
              refine ⟨2590461977072340293717453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726974651381560195811635 2590461977072340293717453)
              ·
                refine ⟨971423241402127610144045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590461977072340293717453 971423241402127610144045)
                ·
                  refine ⟨364283715525797853804017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971423241402127610144045 364283715525797853804017)
                  ·
                    rfl

theorem cell20_798120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_798120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798120 prefixEnd_798120 := by exact prefixLift 798120
  have htrace : WordTrace (prefixWord ++ tailWord_798120) baseStart_798120 baseEnd_798120 := by
    simpa [prefixWord, tailWord_798120, baseEnd_798120] using wordTrace_append hprefix tailTrace_798120
  have hstable : (prefixWord ++ tailWord_798120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798120).length < 2 ^ (prefixWord ++ tailWord_798120).sum := by decide
  have hdescent : baseEnd_798120 < baseStart_798120 := by decide
  rcases family_descends (prefixWord ++ tailWord_798120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798186 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_798186 : Nat := 118140960795 + 798186 * 2 ^ 59
def prefixEnd_798186 : Nat := 4983230072969 + 3 ^ 40 * 798186 * 2
def baseEnd_798186 : Nat := 364313839724194957603747

theorem tailTrace_798186 : CollatzResearch.WordTrace tailWord_798186 prefixEnd_798186 364313839724194957603747 := by
  unfold tailWord_798186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278058771578979040243603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19408156724210610773982941 7278058771578979040243603)
  ·
    refine ⟨10917088157368468560365405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278058771578979040243603 10917088157368468560365405)
    ·
      refine ⟨4093908059013175710137027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10917088157368468560365405 4093908059013175710137027)
      ·
        refine ⟨6140862088519763565205541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093908059013175710137027 6140862088519763565205541)
        ·
          refine ⟨1151411641597455668476039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6140862088519763565205541 1151411641597455668476039)
          ·
            refine ⟨1727117462396183502714059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151411641597455668476039 1727117462396183502714059)
            ·
              refine ⟨2590676193594275254071089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727117462396183502714059 2590676193594275254071089)
              ·
                refine ⟨1943007145195706440553317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590676193594275254071089 1943007145195706440553317)
                ·
                  refine ⟨364313839724194957603747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943007145195706440553317 364313839724194957603747)
                  ·
                    rfl

theorem cell20_798186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_798186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798186 prefixEnd_798186 := by exact prefixLift 798186
  have htrace : WordTrace (prefixWord ++ tailWord_798186) baseStart_798186 baseEnd_798186 := by
    simpa [prefixWord, tailWord_798186, baseEnd_798186] using wordTrace_append hprefix tailTrace_798186
  have hstable : (prefixWord ++ tailWord_798186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798186).length < 2 ^ (prefixWord ++ tailWord_798186).sum := by decide
  have hdescent : baseEnd_798186 < baseStart_798186 := by decide
  rcases family_descends (prefixWord ++ tailWord_798186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798193 : List Nat := [1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_798193 : Nat := 118140960795 + 798193 * 2 ^ 59
def prefixEnd_798193 : Nat := 4983230072969 + 3 ^ 40 * 798193 * 2
def baseEnd_798193 : Nat := 121439011571644681456795

theorem tailTrace_798193 : CollatzResearch.WordTrace tailWord_798193 prefixEnd_798193 121439011571644681456795 := by
  unfold tailWord_798193
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112490397290556356479233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19408326931527037570986155 29112490397290556356479233)
  ·
    refine ⟨21834367797967917267359425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29112490397290556356479233 21834367797967917267359425)
    ·
      refine ⟨16375775848475937950519569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21834367797967917267359425 16375775848475937950519569)
      ·
        refine ⟨12281831886356953462889677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16375775848475937950519569 12281831886356953462889677)
        ·
          refine ⟨4605686957383857548583629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12281831886356953462889677 4605686957383857548583629)
          ·
            refine ⟨1727132609018946580718861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4605686957383857548583629 1727132609018946580718861)
            ·
              refine ⟨647674728382104967769573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1727132609018946580718861 647674728382104967769573)
              ·
                refine ⟨121439011571644681456795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647674728382104967769573 121439011571644681456795)
                ·
                  rfl

theorem cell20_798193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_798193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798193 prefixEnd_798193 := by exact prefixLift 798193
  have htrace : WordTrace (prefixWord ++ tailWord_798193) baseStart_798193 baseEnd_798193 := by
    simpa [prefixWord, tailWord_798193, baseEnd_798193] using wordTrace_append hprefix tailTrace_798193
  have hstable : (prefixWord ++ tailWord_798193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798193).length < 2 ^ (prefixWord ++ tailWord_798193).sum := by decide
  have hdescent : baseEnd_798193 < baseStart_798193 := by decide
  rcases family_descends (prefixWord ++ tailWord_798193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798259 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_798259 : Nat := 118140960795 + 798259 * 2 ^ 59
def prefixEnd_798259 : Nat := 4983230072969 + 3 ^ 40 * 798259 * 2
def baseEnd_798259 : Nat := 364347158913331148170115

theorem tailTrace_798259 : CollatzResearch.WordTrace tailWord_798259 prefixEnd_798259 364347158913331148170115 := by
  unfold tailWord_798259
  simp only [CollatzResearch.WordTrace]
  refine ⟨29114897615051449628381831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19409931743367633085587887 29114897615051449628381831)
  ·
    refine ⟨43672346422577174442572747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29114897615051449628381831 43672346422577174442572747)
    ·
      refine ⟨65508519633865761663859121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43672346422577174442572747 65508519633865761663859121)
      ·
        refine ⟨49131389725399321247894341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65508519633865761663859121 49131389725399321247894341)
        ·
          refine ⟨9212135573512372733980189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49131389725399321247894341 9212135573512372733980189)
          ·
            refine ⟨3454550840067139775242571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9212135573512372733980189 3454550840067139775242571)
            ·
              refine ⟨5181826260100709662863857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454550840067139775242571 5181826260100709662863857)
              ·
                refine ⟨3886369695075532247147893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181826260100709662863857 3886369695075532247147893)
                ·
                  refine ⟨364347158913331148170115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886369695075532247147893 364347158913331148170115)
                  ·
                    rfl

theorem cell20_798259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_798259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798259 prefixEnd_798259 := by exact prefixLift 798259
  have htrace : WordTrace (prefixWord ++ tailWord_798259) baseStart_798259 baseEnd_798259 := by
    simpa [prefixWord, tailWord_798259, baseEnd_798259] using wordTrace_append hprefix tailTrace_798259
  have hstable : (prefixWord ++ tailWord_798259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798259).length < 2 ^ (prefixWord ++ tailWord_798259).sum := by decide
  have hdescent : baseEnd_798259 < baseStart_798259 := by decide
  rcases family_descends (prefixWord ++ tailWord_798259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798269 : List Nat := [1, 4, 1, 3, 3, 2, 6]
def baseStart_798269 : Nat := 118140960795 + 798269 * 2 ^ 59
def prefixEnd_798269 : Nat := 4983230072969 + 3 ^ 40 * 798269 * 2
def baseEnd_798269 : Nat := 40483524798423950870749

theorem tailTrace_798269 : CollatzResearch.WordTrace tailWord_798269 prefixEnd_798269 40483524798423950870749 := by
  unfold tailWord_798269
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115262345015221336245861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410174896676814224163907 29115262345015221336245861)
  ·
    refine ⟨5459111689690354000546099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29115262345015221336245861 5459111689690354000546099)
    ·
      refine ⟨8188667534535531000819149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459111689690354000546099 8188667534535531000819149)
      ·
        refine ⟨3070750325450824125307181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8188667534535531000819149 3070750325450824125307181)
        ·
          refine ⟨1151531372044059046990193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3070750325450824125307181 1151531372044059046990193)
          ·
            refine ⟨863648529033044285242645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151531372044059046990193 863648529033044285242645)
            ·
              refine ⟨40483524798423950870749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 863648529033044285242645 40483524798423950870749)
              ·
                rfl

theorem cell20_798269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_798269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798269 prefixEnd_798269 := by exact prefixLift 798269
  have htrace : WordTrace (prefixWord ++ tailWord_798269) baseStart_798269 baseEnd_798269 := by
    simpa [prefixWord, tailWord_798269, baseEnd_798269] using wordTrace_append hprefix tailTrace_798269
  have hstable : (prefixWord ++ tailWord_798269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798269).length < 2 ^ (prefixWord ++ tailWord_798269).sum := by decide
  have hdescent : baseEnd_798269 < baseStart_798269 := by decide
  rcases family_descends (prefixWord ++ tailWord_798269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798279 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 4]
def baseStart_798279 : Nat := 118140960795 + 798279 * 2 ^ 59
def prefixEnd_798279 : Nat := 4983230072969 + 3 ^ 40 * 798279 * 2
def baseEnd_798279 : Nat := 364356287458299967503367

theorem tailTrace_798279 : CollatzResearch.WordTrace tailWord_798279 prefixEnd_798279 364356287458299967503367 := by
  unfold tailWord_798279
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115627074978993044109891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410418049985995362739927 29115627074978993044109891)
  ·
    refine ⟨43673440612468489566164837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29115627074978993044109891 43673440612468489566164837)
    ·
      refine ⟨8188770114837841793655907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43673440612468489566164837 8188770114837841793655907)
      ·
        refine ⟨12283155172256762690483861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8188770114837841793655907 12283155172256762690483861)
        ·
          refine ⟨575772898699535751116431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12283155172256762690483861 575772898699535751116431)
          ·
            refine ⟨863659348049303626674647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575772898699535751116431 863659348049303626674647)
            ·
              refine ⟨1295489022073955440011971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863659348049303626674647 1295489022073955440011971)
              ·
                refine ⟨1943233533110933160017957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295489022073955440011971 1943233533110933160017957)
                ·
                  refine ⟨364356287458299967503367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943233533110933160017957 364356287458299967503367)
                  ·
                    rfl

theorem cell20_798279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4].length) (baseStart_798279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798279 prefixEnd_798279 := by exact prefixLift 798279
  have htrace : WordTrace (prefixWord ++ tailWord_798279) baseStart_798279 baseEnd_798279 := by
    simpa [prefixWord, tailWord_798279, baseEnd_798279] using wordTrace_append hprefix tailTrace_798279
  have hstable : (prefixWord ++ tailWord_798279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798279).length < 2 ^ (prefixWord ++ tailWord_798279).sum := by decide
  have hdescent : baseEnd_798279 < baseStart_798279 := by decide
  rcases family_descends (prefixWord ++ tailWord_798279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798290 : List Nat := [3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_798290 : Nat := 118140960795 + 798290 * 2 ^ 59
def prefixEnd_798290 : Nat := 4983230072969 + 3 ^ 40 * 798290 * 2
def baseEnd_798290 : Nat := 121453769386010939378885

theorem tailTrace_798290 : CollatzResearch.WordTrace tailWord_798290 prefixEnd_798290 121453769386010939378885 := by
  unfold tailWord_798290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279007069484785480690081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19410685518626094615173549 7279007069484785480690081)
  ·
    refine ⟨5459255302113589110517561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7279007069484785480690081 5459255302113589110517561)
    ·
      refine ⟨4094441476585191832888171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5459255302113589110517561 4094441476585191832888171)
      ·
        refine ⟨6141662214877787749332257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094441476585191832888171 6141662214877787749332257)
        ·
          refine ⟨4606246661158340811999193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6141662214877787749332257 4606246661158340811999193)
          ·
            refine ⟨3454684995868755608999395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606246661158340811999193 3454684995868755608999395)
            ·
              refine ⟨5182027493803133413499093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454684995868755608999395 5182027493803133413499093)
              ·
                refine ⟨121453769386010939378885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5182027493803133413499093 121453769386010939378885)
                ·
                  rfl

theorem cell20_798290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_798290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798290 prefixEnd_798290 := by exact prefixLift 798290
  have htrace : WordTrace (prefixWord ++ tailWord_798290) baseStart_798290 baseEnd_798290 := by
    simpa [prefixWord, tailWord_798290, baseEnd_798290] using wordTrace_append hprefix tailTrace_798290
  have hstable : (prefixWord ++ tailWord_798290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798290).length < 2 ^ (prefixWord ++ tailWord_798290).sum := by decide
  have hdescent : baseEnd_798290 < baseStart_798290 := by decide
  rcases family_descends (prefixWord ++ tailWord_798290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798304 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_798304 : Nat := 118140960795 + 798304 * 2 ^ 59
def prefixEnd_798304 : Nat := 4983230072969 + 3 ^ 40 * 798304 * 2
def baseEnd_798304 : Nat := 364367698139510991669931

theorem tailTrace_798304 : CollatzResearch.WordTrace tailWord_798304 prefixEnd_798304 364367698139510991669931 := by
  unfold tailWord_798304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558269449944211156884983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19411025933258948209179977 14558269449944211156884983)
  ·
    refine ⟨21837404174916316735327475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14558269449944211156884983 21837404174916316735327475)
    ·
      refine ⟨32756106262374475102991213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837404174916316735327475 32756106262374475102991213)
      ·
        refine ⟨12283539848390428163621705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32756106262374475102991213 12283539848390428163621705)
        ·
          refine ⟨9212654886292821122716279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12283539848390428163621705 9212654886292821122716279)
          ·
            refine ⟨13818982329439231684074419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212654886292821122716279 13818982329439231684074419)
            ·
              refine ⟨20728473494158847526111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818982329439231684074419 20728473494158847526111629)
              ·
                refine ⟨7773177560309567822291861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20728473494158847526111629 7773177560309567822291861)
                ·
                  refine ⟨364367698139510991669931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7773177560309567822291861 364367698139510991669931)
                  ·
                    rfl

theorem cell20_798304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_798304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798304 prefixEnd_798304 := by exact prefixLift 798304
  have htrace : WordTrace (prefixWord ++ tailWord_798304) baseStart_798304 baseEnd_798304 := by
    simpa [prefixWord, tailWord_798304, baseEnd_798304] using wordTrace_append hprefix tailTrace_798304
  have hstable : (prefixWord ++ tailWord_798304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798304).length < 2 ^ (prefixWord ++ tailWord_798304).sum := by decide
  have hdescent : baseEnd_798304 < baseStart_798304 := by decide
  rcases family_descends (prefixWord ++ tailWord_798304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798359 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_798359 : Nat := 118140960795 + 798359 * 2 ^ 59
def prefixEnd_798359 : Nat := 4983230072969 + 3 ^ 40 * 798359 * 2
def baseEnd_798359 : Nat := 364392801638175244836373

theorem tailTrace_798359 : CollatzResearch.WordTrace tailWord_798359 prefixEnd_798359 364392801638175244836373 := by
  unfold tailWord_798359
  simp only [CollatzResearch.WordTrace]
  refine ⟨29118544914689166707022131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19412363276459444471348087 29118544914689166707022131)
  ·
    refine ⟨43677817372033750060533197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29118544914689166707022131 43677817372033750060533197)
    ·
      refine ⟨16379181514512656272699949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43677817372033750060533197 16379181514512656272699949)
      ·
        refine ⟨6142193067942246102262481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16379181514512656272699949 6142193067942246102262481)
        ·
          refine ⟨4606644800956684576696861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6142193067942246102262481 4606644800956684576696861)
          ·
            refine ⟨1727491800358756716261323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4606644800956684576696861 1727491800358756716261323)
            ·
              refine ⟨2591237700538135074391985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727491800358756716261323 2591237700538135074391985)
              ·
                refine ⟨1943428275403601305793989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591237700538135074391985 1943428275403601305793989)
                ·
                  refine ⟨364392801638175244836373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943428275403601305793989 364392801638175244836373)
                  ·
                    rfl

theorem cell20_798359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_798359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798359 prefixEnd_798359 := by exact prefixLift 798359
  have htrace : WordTrace (prefixWord ++ tailWord_798359) baseStart_798359 baseEnd_798359 := by
    simpa [prefixWord, tailWord_798359, baseEnd_798359] using wordTrace_append hprefix tailTrace_798359
  have hstable : (prefixWord ++ tailWord_798359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798359).length < 2 ^ (prefixWord ++ tailWord_798359).sum := by decide
  have hdescent : baseEnd_798359 < baseStart_798359 := by decide
  rcases family_descends (prefixWord ++ tailWord_798359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798387 : List Nat := [1, 1, 1, 2, 3, 3, 9]
def baseStart_798387 : Nat := 118140960795 + 798387 * 2 ^ 59
def prefixEnd_798387 : Nat := 4983230072969 + 3 ^ 40 * 798387 * 2
def baseEnd_798387 : Nat := 40489509066792399100325

theorem tailTrace_798387 : CollatzResearch.WordTrace tailWord_798387 prefixEnd_798387 40489509066792399100325 := by
  unfold tailWord_798387
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119566158587727489041415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19413044105725151659360943 29119566158587727489041415)
  ·
    refine ⟨43679349237881591233562123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29119566158587727489041415 43679349237881591233562123)
    ·
      refine ⟨65519023856822386850343185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43679349237881591233562123 65519023856822386850343185)
      ·
        refine ⟨49139267892616790137757389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65519023856822386850343185 49139267892616790137757389)
        ·
          refine ⟨18427225459731296301659021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49139267892616790137757389 18427225459731296301659021)
          ·
            refine ⟨6910209547399236113122133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18427225459731296301659021 6910209547399236113122133)
            ·
              refine ⟨40489509066792399100325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6910209547399236113122133 40489509066792399100325)
              ·
                rfl

theorem cell20_798387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_798387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798387 prefixEnd_798387 := by exact prefixLift 798387
  have htrace : WordTrace (prefixWord ++ tailWord_798387) baseStart_798387 baseEnd_798387 := by
    simpa [prefixWord, tailWord_798387, baseEnd_798387] using wordTrace_append hprefix tailTrace_798387
  have hstable : (prefixWord ++ tailWord_798387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798387).length < 2 ^ (prefixWord ++ tailWord_798387).sum := by decide
  have hdescent : baseEnd_798387 < baseStart_798387 := by decide
  rcases family_descends (prefixWord ++ tailWord_798387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798397 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_798397 : Nat := 118140960795 + 798397 * 2 ^ 59
def prefixEnd_798397 : Nat := 4983230072969 + 3 ^ 40 * 798397 * 2
def baseEnd_798397 : Nat := 364410145873616001569551

theorem tailTrace_798397 : CollatzResearch.WordTrace tailWord_798397 prefixEnd_798397 364410145873616001569551 := by
  unfold tailWord_798397
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119930888551499196905445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19413287259034332797936963 29119930888551499196905445)
  ·
    refine ⟨5459987041603406099419771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29119930888551499196905445 5459987041603406099419771)
    ·
      refine ⟨8189980562405109149129657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459987041603406099419771 8189980562405109149129657)
      ·
        refine ⟨6142485421803831861847243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8189980562405109149129657 6142485421803831861847243)
        ·
          refine ⟨9213728132705747792770865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142485421803831861847243 9213728132705747792770865)
          ·
            refine ⟨6910296099529310844578149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9213728132705747792770865 6910296099529310844578149)
            ·
              refine ⟨1295680518661745783358403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6910296099529310844578149 1295680518661745783358403)
              ·
                refine ⟨1943520777992618675037605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295680518661745783358403 1943520777992618675037605)
                ·
                  refine ⟨364410145873616001569551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943520777992618675037605 364410145873616001569551)
                  ·
                    rfl

theorem cell20_798397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_798397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798397 prefixEnd_798397 := by exact prefixLift 798397
  have htrace : WordTrace (prefixWord ++ tailWord_798397) baseStart_798397 baseEnd_798397 := by
    simpa [prefixWord, tailWord_798397, baseEnd_798397] using wordTrace_append hprefix tailTrace_798397
  have hstable : (prefixWord ++ tailWord_798397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798397).length < 2 ^ (prefixWord ++ tailWord_798397).sum := by decide
  have hdescent : baseEnd_798397 < baseStart_798397 := by decide
  rcases family_descends (prefixWord ++ tailWord_798397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798404 : List Nat := [2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_798404 : Nat := 118140960795 + 798404 * 2 ^ 59
def prefixEnd_798404 : Nat := 4983230072969 + 3 ^ 40 * 798404 * 2
def baseEnd_798404 : Nat := 121471113621451696112063

theorem tailTrace_798404 : CollatzResearch.WordTrace tailWord_798404 prefixEnd_798404 121471113621451696112063 := by
  unfold tailWord_798404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14560093099763069696205133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19413457466350759594940177 14560093099763069696205133)
  ·
    refine ⟨5460034912411151136076925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14560093099763069696205133 5460034912411151136076925)
    ·
      refine ⟨2047513092154181676028847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5460034912411151136076925 2047513092154181676028847)
      ·
        refine ⟨3071269638231272514043271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047513092154181676028847 3071269638231272514043271)
        ·
          refine ⟨4606904457346908771064907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071269638231272514043271 4606904457346908771064907)
          ·
            refine ⟨6910356686020363156597361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606904457346908771064907 6910356686020363156597361)
            ·
              refine ⟨5182767514515272367448021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910356686020363156597361 5182767514515272367448021)
              ·
                refine ⟨121471113621451696112063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5182767514515272367448021 121471113621451696112063)
                ·
                  rfl

theorem cell20_798404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_798404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798404 prefixEnd_798404 := by exact prefixLift 798404
  have htrace : WordTrace (prefixWord ++ tailWord_798404) baseStart_798404 baseEnd_798404 := by
    simpa [prefixWord, tailWord_798404, baseEnd_798404] using wordTrace_append hprefix tailTrace_798404
  have hstable : (prefixWord ++ tailWord_798404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798404).length < 2 ^ (prefixWord ++ tailWord_798404).sum := by decide
  have hdescent : baseEnd_798404 < baseStart_798404 := by decide
  rcases family_descends (prefixWord ++ tailWord_798404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798411 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_798411 : Nat := 118140960795 + 798411 * 2 ^ 59
def prefixEnd_798411 : Nat := 4983230072969 + 3 ^ 40 * 798411 * 2
def baseEnd_798411 : Nat := 364416535855094175102827

theorem tailTrace_798411 : CollatzResearch.WordTrace tailWord_798411 prefixEnd_798411 364416535855094175102827 := by
  unfold tailWord_798411
  simp only [CollatzResearch.WordTrace]
  refine ⟨29120441510500779587915087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19413627673667186391943391 29120441510500779587915087)
  ·
    refine ⟨43680662265751169381872631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29120441510500779587915087 43680662265751169381872631)
    ·
      refine ⟨65520993398626754072808947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43680662265751169381872631 65520993398626754072808947)
      ·
        refine ⟨98281490097940131109213421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65520993398626754072808947 98281490097940131109213421)
        ·
          refine ⟨36855558786727549165955033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98281490097940131109213421 36855558786727549165955033)
          ·
            refine ⟨27641669090045661874466275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36855558786727549165955033 27641669090045661874466275)
            ·
              refine ⟨41462503635068492811699413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27641669090045661874466275 41462503635068492811699413)
              ·
                refine ⟨971777428946917800274205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41462503635068492811699413 971777428946917800274205)
                ·
                  refine ⟨364416535855094175102827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971777428946917800274205 364416535855094175102827)
                  ·
                    rfl

theorem cell20_798411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_798411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798411 prefixEnd_798411 := by exact prefixLift 798411
  have htrace : WordTrace (prefixWord ++ tailWord_798411) baseStart_798411 baseEnd_798411 := by
    simpa [prefixWord, tailWord_798411, baseEnd_798411] using wordTrace_append hprefix tailTrace_798411
  have hstable : (prefixWord ++ tailWord_798411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798411).length < 2 ^ (prefixWord ++ tailWord_798411).sum := by decide
  have hdescent : baseEnd_798411 < baseStart_798411 := by decide
  rcases family_descends (prefixWord ++ tailWord_798411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798449 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_798449 : Nat := 118140960795 + 798449 * 2 ^ 59
def prefixEnd_798449 : Nat := 4983230072969 + 3 ^ 40 * 798449 * 2
def baseEnd_798449 : Nat := 364433880090534931836005

theorem tailTrace_798449 : CollatzResearch.WordTrace tailWord_798449 prefixEnd_798449 364433880090534931836005 := by
  unfold tailWord_798449
  simp only [CollatzResearch.WordTrace]
  refine ⟨29121827484363112077798401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414551656242074718532267 29121827484363112077798401)
  ·
    refine ⟨21841370613272334058348801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29121827484363112077798401 21841370613272334058348801)
    ·
      refine ⟨16381027959954250543761601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21841370613272334058348801 16381027959954250543761601)
      ·
        refine ⟨12285770969965687907821201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16381027959954250543761601 12285770969965687907821201)
        ·
          refine ⟨9214328227474265930865901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12285770969965687907821201 9214328227474265930865901)
          ·
            refine ⟨3455373085302849724074713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9214328227474265930865901 3455373085302849724074713)
            ·
              refine ⟨2591529813977137293056035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455373085302849724074713 2591529813977137293056035)
              ·
                refine ⟨3887294720965705939584053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591529813977137293056035 3887294720965705939584053)
                ·
                  refine ⟨364433880090534931836005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3887294720965705939584053 364433880090534931836005)
                  ·
                    rfl

theorem cell20_798449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_798449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798449 prefixEnd_798449 := by exact prefixLift 798449
  have htrace : WordTrace (prefixWord ++ tailWord_798449) baseStart_798449 baseEnd_798449 := by
    simpa [prefixWord, tailWord_798449, baseEnd_798449] using wordTrace_append hprefix tailTrace_798449
  have hstable : (prefixWord ++ tailWord_798449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798449).length < 2 ^ (prefixWord ++ tailWord_798449).sum := by decide
  have hdescent : baseEnd_798449 < baseStart_798449 := by decide
  rcases family_descends (prefixWord ++ tailWord_798449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798456 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_798456 : Nat := 118140960795 + 798456 * 2 ^ 59
def prefixEnd_798456 : Nat := 4983230072969 + 3 ^ 40 * 798456 * 2
def baseEnd_798456 : Nat := 364437075081274018602643

theorem tailTrace_798456 : CollatzResearch.WordTrace tailWord_798456 prefixEnd_798456 364437075081274018602643 := by
  unfold tailWord_798456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561041397668876136651611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19414721863558501515535481 14561041397668876136651611)
  ·
    refine ⟨21841562096503314204977417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561041397668876136651611 21841562096503314204977417)
    ·
      refine ⟨16381171572377485653733063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21841562096503314204977417 16381171572377485653733063)
      ·
        refine ⟨24571757358566228480599595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16381171572377485653733063 24571757358566228480599595)
        ·
          refine ⟨36857636037849342720899393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24571757358566228480599595 36857636037849342720899393)
          ·
            refine ⟨27643227028387007040674545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36857636037849342720899393 27643227028387007040674545)
            ·
              refine ⟨20732420271290255280505909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27643227028387007040674545 20732420271290255280505909)
              ·
                refine ⟨1943664400433461432547429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20732420271290255280505909 1943664400433461432547429)
                ·
                  refine ⟨364437075081274018602643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943664400433461432547429 364437075081274018602643)
                  ·
                    rfl

theorem cell20_798456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_798456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798456 prefixEnd_798456 := by exact prefixLift 798456
  have htrace : WordTrace (prefixWord ++ tailWord_798456) baseStart_798456 baseEnd_798456 := by
    simpa [prefixWord, tailWord_798456, baseEnd_798456] using wordTrace_append hprefix tailTrace_798456
  have hstable : (prefixWord ++ tailWord_798456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798456).length < 2 ^ (prefixWord ++ tailWord_798456).sum := by decide
  have hdescent : baseEnd_798456 < baseStart_798456 := by decide
  rcases family_descends (prefixWord ++ tailWord_798456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798463 : List Nat := [1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_798463 : Nat := 118140960795 + 798463 * 2 ^ 59
def prefixEnd_798463 : Nat := 4983230072969 + 3 ^ 40 * 798463 * 2
def baseEnd_798463 : Nat := 121480090024004368456427

theorem tailTrace_798463 : CollatzResearch.WordTrace tailWord_798463 prefixEnd_798463 121480090024004368456427 := by
  unfold tailWord_798463
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122338106312392468808043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414892070874928312538695 29122338106312392468808043)
  ·
    refine ⟨43683507159468588703212065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29122338106312392468808043 43683507159468588703212065)
    ·
      refine ⟨32762630369601441527409049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43683507159468588703212065 32762630369601441527409049)
      ·
        refine ⟨24571972777201081145556787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32762630369601441527409049 24571972777201081145556787)
        ·
          refine ⟨36857959165801621718335181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24571972777201081145556787 36857959165801621718335181)
          ·
            refine ⟨13821734687175608144375693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36857959165801621718335181 13821734687175608144375693)
            ·
              refine ⟨5183150507690853054140885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13821734687175608144375693 5183150507690853054140885)
              ·
                refine ⟨121480090024004368456427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5183150507690853054140885 121480090024004368456427)
                ·
                  rfl

theorem cell20_798463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_798463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798463 prefixEnd_798463 := by exact prefixLift 798463
  have htrace : WordTrace (prefixWord ++ tailWord_798463) baseStart_798463 baseEnd_798463 := by
    simpa [prefixWord, tailWord_798463, baseEnd_798463] using wordTrace_append hprefix tailTrace_798463
  have hstable : (prefixWord ++ tailWord_798463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798463).length < 2 ^ (prefixWord ++ tailWord_798463).sum := by decide
  have hdescent : baseEnd_798463 < baseStart_798463 := by decide
  rcases family_descends (prefixWord ++ tailWord_798463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798501 : List Nat := [1, 3, 1, 2, 3, 10]
def baseStart_798501 : Nat := 118140960795 + 798501 * 2 ^ 59
def prefixEnd_798501 : Nat := 4983230072969 + 3 ^ 40 * 798501 * 2
def baseEnd_798501 : Nat := 13498430159535328226017

theorem tailTrace_798501 : CollatzResearch.WordTrace tailWord_798501 prefixEnd_798501 13498430159535328226017 := by
  unfold tailWord_798501
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123724080174724958691357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19415816053449816639127571 29123724080174724958691357)
  ·
    refine ⟨10921396530065521859509259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29123724080174724958691357 10921396530065521859509259)
    ·
      refine ⟨16382094795098282789263889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921396530065521859509259 16382094795098282789263889)
      ·
        refine ⟨12286571096323712091947917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16382094795098282789263889 12286571096323712091947917)
        ·
          refine ⟨4607464161121392034480469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12286571096323712091947917 4607464161121392034480469)
          ·
            refine ⟨13498430159535328226017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4607464161121392034480469 13498430159535328226017)
            ·
              rfl

theorem cell20_798501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_798501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798501 prefixEnd_798501 := by exact prefixLift 798501
  have htrace : WordTrace (prefixWord ++ tailWord_798501) baseStart_798501 baseEnd_798501 := by
    simpa [prefixWord, tailWord_798501, baseEnd_798501] using wordTrace_append hprefix tailTrace_798501
  have hstable : (prefixWord ++ tailWord_798501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798501).length < 2 ^ (prefixWord ++ tailWord_798501).sum := by decide
  have hdescent : baseEnd_798501 < baseStart_798501 := by decide
  rcases family_descends (prefixWord ++ tailWord_798501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798504 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_798504 : Nat := 118140960795 + 798504 * 2 ^ 59
def prefixEnd_798504 : Nat := 4983230072969 + 3 ^ 40 * 798504 * 2
def baseEnd_798504 : Nat := 364458983589199185002447

theorem tailTrace_798504 : CollatzResearch.WordTrace tailWord_798504 prefixEnd_798504 364458983589199185002447 := by
  unfold tailWord_798504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561916749581928235525283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19415888999442570980700377 14561916749581928235525283)
  ·
    refine ⟨21842875124372892353287925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561916749581928235525283 21842875124372892353287925)
    ·
      refine ⟨2047769542909958658120743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21842875124372892353287925 2047769542909958658120743)
      ·
        refine ⟨3071654314364937987181115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047769542909958658120743 3071654314364937987181115)
        ·
          refine ⟨4607481471547406980771673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071654314364937987181115 4607481471547406980771673)
          ·
            refine ⟨3455611103660555235578755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607481471547406980771673 3455611103660555235578755)
            ·
              refine ⟨5183416655490832853368133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455611103660555235578755 5183416655490832853368133)
              ·
                refine ⟨971890622904531160006525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5183416655490832853368133 971890622904531160006525)
                ·
                  refine ⟨364458983589199185002447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971890622904531160006525 364458983589199185002447)
                  ·
                    rfl

theorem cell20_798504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_798504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798504 prefixEnd_798504 := by exact prefixLift 798504
  have htrace : WordTrace (prefixWord ++ tailWord_798504) baseStart_798504 baseEnd_798504 := by
    simpa [prefixWord, tailWord_798504, baseEnd_798504] using wordTrace_append hprefix tailTrace_798504
  have hstable : (prefixWord ++ tailWord_798504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798504).length < 2 ^ (prefixWord ++ tailWord_798504).sum := by decide
  have hdescent : baseEnd_798504 < baseStart_798504 := by decide
  rcases family_descends (prefixWord ++ tailWord_798504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798511 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 2]
def baseStart_798511 : Nat := 118140960795 + 798511 * 2 ^ 59
def prefixEnd_798511 : Nat := 4983230072969 + 3 ^ 40 * 798511 * 2
def baseEnd_798511 : Nat := 364462178579938271769085

theorem tailTrace_798511 : CollatzResearch.WordTrace tailWord_798511 prefixEnd_798511 364462178579938271769085 := by
  unfold tailWord_798511
  simp only [CollatzResearch.WordTrace]
  refine ⟨29124088810138496666555387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19416059206758997777703591 29124088810138496666555387)
  ·
    refine ⟨43686133215207744999833081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29124088810138496666555387 43686133215207744999833081)
    ·
      refine ⟨32764599911405808749874811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43686133215207744999833081 32764599911405808749874811)
      ·
        refine ⟨49146899867108713124812217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32764599911405808749874811 49146899867108713124812217)
        ·
          refine ⟨36860174900331534843609163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49146899867108713124812217 36860174900331534843609163)
          ·
            refine ⟨55290262350497302265413745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36860174900331534843609163 55290262350497302265413745)
            ·
              refine ⟨41467696762872976699060309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55290262350497302265413745 41467696762872976699060309)
              ·
                refine ⟨485949571439917695692113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 41467696762872976699060309 485949571439917695692113)
                ·
                  refine ⟨364462178579938271769085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485949571439917695692113 364462178579938271769085)
                  ·
                    rfl

theorem cell20_798511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2].length) (baseStart_798511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798511 prefixEnd_798511 := by exact prefixLift 798511
  have htrace : WordTrace (prefixWord ++ tailWord_798511) baseStart_798511 baseEnd_798511 := by
    simpa [prefixWord, tailWord_798511, baseEnd_798511] using wordTrace_append hprefix tailTrace_798511
  have hstable : (prefixWord ++ tailWord_798511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798511).length < 2 ^ (prefixWord ++ tailWord_798511).sum := by decide
  have hdescent : baseEnd_798511 < baseStart_798511 := by decide
  rcases family_descends (prefixWord ++ tailWord_798511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798577 : List Nat := [1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_798577 : Nat := 118140960795 + 798577 * 2 ^ 59
def prefixEnd_798577 : Nat := 4983230072969 + 3 ^ 40 * 798577 * 2
def baseEnd_798577 : Nat := 121497434259445125189605

theorem tailTrace_798577 : CollatzResearch.WordTrace tailWord_798577 prefixEnd_798577 121497434259445125189605 := by
  unfold tailWord_798577
  simp only [CollatzResearch.WordTrace]
  refine ⟨29126496027899389938457985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19417664018599593292305323 29126496027899389938457985)
  ·
    refine ⟨21844872020924542453843489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29126496027899389938457985 21844872020924542453843489)
    ·
      refine ⟨16383654015693406840382617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21844872020924542453843489 16383654015693406840382617)
      ·
        refine ⟨12287740511770055130286963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16383654015693406840382617 12287740511770055130286963)
        ·
          refine ⟨18431610767655082695430445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12287740511770055130286963 18431610767655082695430445)
          ·
            refine ⟨6911854037870656010786417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18431610767655082695430445 6911854037870656010786417)
            ·
              refine ⟨5183890528402992008089813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911854037870656010786417 5183890528402992008089813)
              ·
                refine ⟨121497434259445125189605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5183890528402992008089813 121497434259445125189605)
                ·
                  rfl

theorem cell20_798577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_798577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798577 prefixEnd_798577 := by exact prefixLift 798577
  have htrace : WordTrace (prefixWord ++ tailWord_798577) baseStart_798577 baseEnd_798577 := by
    simpa [prefixWord, tailWord_798577, baseEnd_798577] using wordTrace_append hprefix tailTrace_798577
  have hstable : (prefixWord ++ tailWord_798577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798577).length < 2 ^ (prefixWord ++ tailWord_798577).sum := by decide
  have hdescent : baseEnd_798577 < baseStart_798577 := by decide
  rcases family_descends (prefixWord ++ tailWord_798577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798590 : List Nat := [4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_798590 : Nat := 118140960795 + 798590 * 2 ^ 59
def prefixEnd_798590 : Nat := 4983230072969 + 3 ^ 40 * 798590 * 2
def baseEnd_798590 : Nat := 121499412110855036045143

theorem tailTrace_798590 : CollatzResearch.WordTrace tailWord_798590 prefixEnd_798590 121499412110855036045143 := by
  unfold tailWord_798590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640871272106536644835153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19417980117901528772454149 3640871272106536644835153)
  ·
    refine ⟨2730653454079902483626365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3640871272106536644835153 2730653454079902483626365)
    ·
      refine ⟨1023995045279963431359887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2730653454079902483626365 1023995045279963431359887)
      ·
        refine ⟨1535992567919945147039831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023995045279963431359887 1535992567919945147039831)
        ·
          refine ⟨2303988851879917720559747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535992567919945147039831 2303988851879917720559747)
          ·
            refine ⟨3455983277819876580839621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303988851879917720559747 3455983277819876580839621)
            ·
              refine ⟨647996864591226858907429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3455983277819876580839621 647996864591226858907429)
              ·
                refine ⟨121499412110855036045143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647996864591226858907429 121499412110855036045143)
                ·
                  rfl

theorem cell20_798590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_798590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798590 prefixEnd_798590 := by exact prefixLift 798590
  have htrace : WordTrace (prefixWord ++ tailWord_798590) baseStart_798590 baseEnd_798590 := by
    simpa [prefixWord, tailWord_798590, baseEnd_798590] using wordTrace_append hprefix tailTrace_798590
  have hstable : (prefixWord ++ tailWord_798590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798590).length < 2 ^ (prefixWord ++ tailWord_798590).sum := by decide
  have hdescent : baseEnd_798590 < baseStart_798590 := by decide
  rcases family_descends (prefixWord ++ tailWord_798590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798600 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_798600 : Nat := 118140960795 + 798600 * 2 ^ 59
def prefixEnd_798600 : Nat := 4983230072969 + 3 ^ 40 * 798600 * 2
def baseEnd_798600 : Nat := 364502800605049517802055

theorem tailTrace_798600 : CollatzResearch.WordTrace tailWord_798600 prefixEnd_798600 364502800605049517802055 := by
  unfold tailWord_798600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563667453408032433272627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19418223271210709911030169 14563667453408032433272627)
  ·
    refine ⟨21845501180112048649908941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14563667453408032433272627 21845501180112048649908941)
    ·
      refine ⟨8192062942542018243715853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21845501180112048649908941 8192062942542018243715853)
      ·
        refine ⟨3072023603453256841393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8192062942542018243715853 3072023603453256841393445)
        ·
          refine ⟨576004425647485657761271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3072023603453256841393445 576004425647485657761271)
          ·
            refine ⟨864006638471228486641907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576004425647485657761271 864006638471228486641907)
            ·
              refine ⟨1296009957706842729962861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864006638471228486641907 1296009957706842729962861)
              ·
                refine ⟨486003734140066023736073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296009957706842729962861 486003734140066023736073)
                ·
                  refine ⟨364502800605049517802055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486003734140066023736073 364502800605049517802055)
                  ·
                    rfl

theorem cell20_798600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_798600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798600 prefixEnd_798600 := by exact prefixLift 798600
  have htrace : WordTrace (prefixWord ++ tailWord_798600) baseStart_798600 baseEnd_798600 := by
    simpa [prefixWord, tailWord_798600, baseEnd_798600] using wordTrace_append hprefix tailTrace_798600
  have hstable : (prefixWord ++ tailWord_798600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798600).length < 2 ^ (prefixWord ++ tailWord_798600).sum := by decide
  have hdescent : baseEnd_798600 < baseStart_798600 := by decide
  rcases family_descends (prefixWord ++ tailWord_798600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798615 : List Nat := [1, 1, 3, 3, 1, 3, 8]
def baseStart_798615 : Nat := 118140960795 + 798615 * 2 ^ 59
def prefixEnd_798615 : Nat := 4983230072969 + 3 ^ 40 * 798615 * 2
def baseEnd_798615 : Nat := 40501071890419570255777

theorem tailTrace_798615 : CollatzResearch.WordTrace tailWord_798615 prefixEnd_798615 40501071890419570255777 := by
  unfold tailWord_798615
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127882001761722428341299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19418588001174481618894199 29127882001761722428341299)
  ·
    refine ⟨43691823002642583642511949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29127882001761722428341299 43691823002642583642511949)
    ·
      refine ⟨16384433625990968865941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43691823002642583642511949 16384433625990968865941981)
      ·
        refine ⟨6144162609746613324728243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16384433625990968865941981 6144162609746613324728243)
        ·
          refine ⟨9216243914619919987092365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144162609746613324728243 9216243914619919987092365)
          ·
            refine ⟨3456091467982469995159637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9216243914619919987092365 3456091467982469995159637)
            ·
              refine ⟨40501071890419570255777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3456091467982469995159637 40501071890419570255777)
              ·
                rfl

theorem cell20_798615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_798615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798615 prefixEnd_798615 := by exact prefixLift 798615
  have htrace : WordTrace (prefixWord ++ tailWord_798615) baseStart_798615 baseEnd_798615 := by
    simpa [prefixWord, tailWord_798615, baseEnd_798615] using wordTrace_append hprefix tailTrace_798615
  have hstable : (prefixWord ++ tailWord_798615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798615).length < 2 ^ (prefixWord ++ tailWord_798615).sum := by decide
  have hdescent : baseEnd_798615 < baseStart_798615 := by decide
  rcases family_descends (prefixWord ++ tailWord_798615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798621 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 2]
def baseStart_798621 : Nat := 118140960795 + 798621 * 2 ^ 59
def prefixEnd_798621 : Nat := 4983230072969 + 3 ^ 40 * 798621 * 2
def baseEnd_798621 : Nat := 364512385577266778101969

theorem tailTrace_798621 : CollatzResearch.WordTrace tailWord_798621 prefixEnd_798621 364512385577266778101969 := by
  unfold tailWord_798621
  simp only [CollatzResearch.WordTrace]
  refine ⟨29128100839739985453059717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19418733893159990302039811 29128100839739985453059717)
  ·
    refine ⟨5461518907451247272448697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29128100839739985453059717 5461518907451247272448697)
    ·
      refine ⟨4096139180588435454336523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5461518907451247272448697 4096139180588435454336523)
      ·
        refine ⟨6144208770882653181504785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096139180588435454336523 6144208770882653181504785)
        ·
          refine ⟨4608156578161989886128589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6144208770882653181504785 4608156578161989886128589)
          ·
            refine ⟨1728058716810746207298221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4608156578161989886128589 1728058716810746207298221)
            ·
              refine ⟨648022018804029827736833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1728058716810746207298221 648022018804029827736833)
              ·
                refine ⟨486016514103022370802625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648022018804029827736833 486016514103022370802625)
                ·
                  refine ⟨364512385577266778101969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486016514103022370802625 364512385577266778101969)
                  ·
                    rfl

theorem cell20_798621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_798621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798621 prefixEnd_798621 := by exact prefixLift 798621
  have htrace : WordTrace (prefixWord ++ tailWord_798621) baseStart_798621 baseEnd_798621 := by
    simpa [prefixWord, tailWord_798621, baseEnd_798621] using wordTrace_append hprefix tailTrace_798621
  have hstable : (prefixWord ++ tailWord_798621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798621).length < 2 ^ (prefixWord ++ tailWord_798621).sum := by decide
  have hdescent : baseEnd_798621 < baseStart_798621 := by decide
  rcases family_descends (prefixWord ++ tailWord_798621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798639 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_798639 : Nat := 118140960795 + 798639 * 2 ^ 59
def prefixEnd_798639 : Nat := 4983230072969 + 3 ^ 40 * 798639 * 2
def baseEnd_798639 : Nat := 364520601267738715501895

theorem tailTrace_798639 : CollatzResearch.WordTrace tailWord_798639 prefixEnd_798639 364520601267738715501895 := by
  unfold tailWord_798639
  simp only [CollatzResearch.WordTrace]
  refine ⟨29128757353674774527214971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19419171569116516351476647 29128757353674774527214971)
  ·
    refine ⟨43693136030512161790822457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29128757353674774527214971 43693136030512161790822457)
    ·
      refine ⟨32769852022884121343116843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43693136030512161790822457 32769852022884121343116843)
      ·
        refine ⟨49154778034326182014675265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32769852022884121343116843 49154778034326182014675265)
        ·
          refine ⟨36866083525744636511006449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49154778034326182014675265 36866083525744636511006449)
          ·
            refine ⟨27649562644308477383254837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36866083525744636511006449 27649562644308477383254837)
            ·
              refine ⟨2592146497903919754680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27649562644308477383254837 2592146497903919754680141)
              ·
                refine ⟨972054936713969908005053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2592146497903919754680141 972054936713969908005053)
                ·
                  refine ⟨364520601267738715501895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972054936713969908005053 364520601267738715501895)
                  ·
                    rfl

theorem cell20_798639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_798639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798639 prefixEnd_798639 := by exact prefixLift 798639
  have htrace : WordTrace (prefixWord ++ tailWord_798639) baseStart_798639 baseEnd_798639 := by
    simpa [prefixWord, tailWord_798639, baseEnd_798639] using wordTrace_append hprefix tailTrace_798639
  have hstable : (prefixWord ++ tailWord_798639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798639).length < 2 ^ (prefixWord ++ tailWord_798639).sum := by decide
  have hdescent : baseEnd_798639 < baseStart_798639 := by decide
  rcases family_descends (prefixWord ++ tailWord_798639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798663 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 2]
def baseStart_798663 : Nat := 118140960795 + 798663 * 2 ^ 59
def prefixEnd_798663 : Nat := 4983230072969 + 3 ^ 40 * 798663 * 2
def baseEnd_798663 : Nat := 364531555521701298701797

theorem tailTrace_798663 : CollatzResearch.WordTrace tailWord_798663 prefixEnd_798663 364531555521701298701797 := by
  unfold tailWord_798663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129632705587826626088643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19419755137058551084059095 29129632705587826626088643)
  ·
    refine ⟨43694449058381739939132965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29129632705587826626088643 43694449058381739939132965)
    ·
      refine ⟨8192709198446576238587431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43694449058381739939132965 8192709198446576238587431)
      ·
        refine ⟨12289063797669864357881147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8192709198446576238587431 12289063797669864357881147)
        ·
          refine ⟨18433595696504796536821721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12289063797669864357881147 18433595696504796536821721)
          ·
            refine ⟨13825196772378597402616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18433595696504796536821721 13825196772378597402616291)
            ·
              refine ⟨20737795158567896103924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825196772378597402616291 20737795158567896103924437)
              ·
                refine ⟨486042074028935064935729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20737795158567896103924437 486042074028935064935729)
                ·
                  refine ⟨364531555521701298701797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486042074028935064935729 364531555521701298701797)
                  ·
                    rfl

theorem cell20_798663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2].length) (baseStart_798663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798663 prefixEnd_798663 := by exact prefixLift 798663
  have htrace : WordTrace (prefixWord ++ tailWord_798663) baseStart_798663 baseEnd_798663 := by
    simpa [prefixWord, tailWord_798663, baseEnd_798663] using wordTrace_append hprefix tailTrace_798663
  have hstable : (prefixWord ++ tailWord_798663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798663).length < 2 ^ (prefixWord ++ tailWord_798663).sum := by decide
  have hdescent : baseEnd_798663 < baseStart_798663 := by decide
  rcases family_descends (prefixWord ++ tailWord_798663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798736 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_798736 : Nat := 118140960795 + 798736 * 2 ^ 59
def prefixEnd_798736 : Nat := 4983230072969 + 3 ^ 40 * 798736 * 2
def baseEnd_798736 : Nat := 364564874710837489268165

theorem tailTrace_798736 : CollatzResearch.WordTrace tailWord_798736 prefixEnd_798736 364564874710837489268165 := by
  unfold tailWord_798736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14566147617161680046748031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19421530156215573395664041 14566147617161680046748031)
  ·
    refine ⟨21849221425742520070122047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14566147617161680046748031 21849221425742520070122047)
    ·
      refine ⟨32773832138613780105183071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21849221425742520070122047 32773832138613780105183071)
      ·
        refine ⟨49160748207920670157774607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32773832138613780105183071 49160748207920670157774607)
        ·
          refine ⟨73741122311881005236661911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49160748207920670157774607 73741122311881005236661911)
          ·
            refine ⟨110611683467821507854992867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73741122311881005236661911 110611683467821507854992867)
            ·
              refine ⟨165917525201732261782489301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110611683467821507854992867 165917525201732261782489301)
              ·
                refine ⟨3888691996915599885527093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165917525201732261782489301 3888691996915599885527093)
                ·
                  refine ⟨364564874710837489268165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888691996915599885527093 364564874710837489268165)
                  ·
                    rfl

theorem cell20_798736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_798736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798736 prefixEnd_798736 := by exact prefixLift 798736
  have htrace : WordTrace (prefixWord ++ tailWord_798736) baseStart_798736 baseEnd_798736 := by
    simpa [prefixWord, tailWord_798736, baseEnd_798736] using wordTrace_append hprefix tailTrace_798736
  have hstable : (prefixWord ++ tailWord_798736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798736).length < 2 ^ (prefixWord ++ tailWord_798736).sum := by decide
  have hdescent : baseEnd_798736 < baseStart_798736 := by decide
  rcases family_descends (prefixWord ++ tailWord_798736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798739 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 2]
def baseStart_798739 : Nat := 118140960795 + 798739 * 2 ^ 59
def prefixEnd_798739 : Nat := 4983230072969 + 3 ^ 40 * 798739 * 2
def baseEnd_798739 : Nat := 364566243992582812168153

theorem tailTrace_798739 : CollatzResearch.WordTrace tailWord_798739 prefixEnd_798739 364566243992582812168153 := by
  unfold tailWord_798739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132404653312491605855271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19421603102208327737236847 29132404653312491605855271)
  ·
    refine ⟨43698606979968737408782907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29132404653312491605855271 43698606979968737408782907)
    ·
      refine ⟨65547910469953106113174361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43698606979968737408782907 65547910469953106113174361)
      ·
        refine ⟨49160932852464829584880771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65547910469953106113174361 49160932852464829584880771)
        ·
          refine ⟨73741399278697244377321157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49160932852464829584880771 73741399278697244377321157)
          ·
            refine ⟨13826512364755733320747717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73741399278697244377321157 13826512364755733320747717)
            ·
              refine ⟨2592471068391699997640197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13826512364755733320747717 2592471068391699997640197)
              ·
                refine ⟨486088325323443749557537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2592471068391699997640197 486088325323443749557537)
                ·
                  refine ⟨364566243992582812168153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486088325323443749557537 364566243992582812168153)
                  ·
                    rfl

theorem cell20_798739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2].length) (baseStart_798739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798739 prefixEnd_798739 := by exact prefixLift 798739
  have htrace : WordTrace (prefixWord ++ tailWord_798739) baseStart_798739 baseEnd_798739 := by
    simpa [prefixWord, tailWord_798739, baseEnd_798739] using wordTrace_append hprefix tailTrace_798739
  have hstable : (prefixWord ++ tailWord_798739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798739).length < 2 ^ (prefixWord ++ tailWord_798739).sum := by decide
  have hdescent : baseEnd_798739 < baseStart_798739 := by decide
  rcases family_descends (prefixWord ++ tailWord_798739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798749 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_798749 : Nat := 118140960795 + 798749 * 2 ^ 59
def prefixEnd_798749 : Nat := 4983230072969 + 3 ^ 40 * 798749 * 2
def baseEnd_798749 : Nat := 364570808265067221834779

theorem tailTrace_798749 : CollatzResearch.WordTrace tailWord_798749 prefixEnd_798749 364570808265067221834779 := by
  unfold tailWord_798749
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132769383276263313719301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19421846255517508875812867 29132769383276263313719301)
  ·
    refine ⟨5462394259364299371322369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29132769383276263313719301 5462394259364299371322369)
    ·
      refine ⟨4096795694523224528491777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5462394259364299371322369 4096795694523224528491777)
      ·
        refine ⟨3072596770892418396368833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096795694523224528491777 3072596770892418396368833)
        ·
          refine ⟨2304447578169313797276625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3072596770892418396368833 2304447578169313797276625)
          ·
            refine ⟨1728335683626985347957469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304447578169313797276625 1728335683626985347957469)
            ·
              refine ⟨648125881360119505484051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1728335683626985347957469 648125881360119505484051)
              ·
                refine ⟨972188822040179258226077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648125881360119505484051 972188822040179258226077)
                ·
                  refine ⟨364570808265067221834779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972188822040179258226077 364570808265067221834779)
                  ·
                    rfl

theorem cell20_798749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_798749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798749 prefixEnd_798749 := by exact prefixLift 798749
  have htrace : WordTrace (prefixWord ++ tailWord_798749) baseStart_798749 baseEnd_798749 := by
    simpa [prefixWord, tailWord_798749, baseEnd_798749] using wordTrace_append hprefix tailTrace_798749
  have hstable : (prefixWord ++ tailWord_798749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798749).length < 2 ^ (prefixWord ++ tailWord_798749).sum := by decide
  have hdescent : baseEnd_798749 < baseStart_798749 := by decide
  rcases family_descends (prefixWord ++ tailWord_798749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798759 : List Nat := [1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_798759 : Nat := 118140960795 + 798759 * 2 ^ 59
def prefixEnd_798759 : Nat := 4983230072969 + 3 ^ 40 * 798759 * 2
def baseEnd_798759 : Nat := 121525124179183877167135

theorem tailTrace_798759 : CollatzResearch.WordTrace tailWord_798759 prefixEnd_798759 121525124179183877167135 := by
  unfold tailWord_798759
  simp only [CollatzResearch.WordTrace]
  refine ⟨29133134113240035021583331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19422089408826690014388887 29133134113240035021583331)
  ·
    refine ⟨43699701169860052532374997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29133134113240035021583331 43699701169860052532374997)
    ·
      refine ⟨1024211746168594981227539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43699701169860052532374997 1024211746168594981227539)
      ·
        refine ⟨1536317619252892471841309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024211746168594981227539 1536317619252892471841309)
        ·
          refine ⟨576119107219834676940491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536317619252892471841309 576119107219834676940491)
          ·
            refine ⟨864178660829752015410737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576119107219834676940491 864178660829752015410737)
            ·
              refine ⟨648133995622314011558053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864178660829752015410737 648133995622314011558053)
              ·
                refine ⟨121525124179183877167135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648133995622314011558053 121525124179183877167135)
                ·
                  rfl

theorem cell20_798759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_798759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798759 prefixEnd_798759 := by exact prefixLift 798759
  have htrace : WordTrace (prefixWord ++ tailWord_798759) baseStart_798759 baseEnd_798759 := by
    simpa [prefixWord, tailWord_798759, baseEnd_798759] using wordTrace_append hprefix tailTrace_798759
  have hstable : (prefixWord ++ tailWord_798759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798759).length < 2 ^ (prefixWord ++ tailWord_798759).sum := by decide
  have hdescent : baseEnd_798759 < baseStart_798759 := by decide
  rcases family_descends (prefixWord ++ tailWord_798759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798790 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_798790 : Nat := 118140960795 + 798790 * 2 ^ 59
def prefixEnd_798790 : Nat := 4983230072969 + 3 ^ 40 * 798790 * 2
def baseEnd_798790 : Nat := 364589521782253301467945

theorem tailTrace_798790 : CollatzResearch.WordTrace tailWord_798790 prefixEnd_798790 364589521782253301467945 := by
  unfold tailWord_798790
  simp only [CollatzResearch.WordTrace]
  refine ⟨910445774253991478623807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19422843184085151543974549 910445774253991478623807)
  ·
    refine ⟨1365668661380987217935711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910445774253991478623807 1365668661380987217935711)
    ·
      refine ⟨2048502992071480826903567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365668661380987217935711 2048502992071480826903567)
      ·
        refine ⟨3072754488107221240355351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048502992071480826903567 3072754488107221240355351)
        ·
          refine ⟨4609131732160831860533027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072754488107221240355351 4609131732160831860533027)
          ·
            refine ⟨6913697598241247790799541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609131732160831860533027 6913697598241247790799541)
            ·
              refine ⟨648159149835116980387457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6913697598241247790799541 648159149835116980387457)
              ·
                refine ⟨486119362376337735290593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648159149835116980387457 486119362376337735290593)
                ·
                  refine ⟨364589521782253301467945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486119362376337735290593 364589521782253301467945)
                  ·
                    rfl

theorem cell20_798790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_798790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798790 prefixEnd_798790 := by exact prefixLift 798790
  have htrace : WordTrace (prefixWord ++ tailWord_798790) baseStart_798790 baseEnd_798790 := by
    simpa [prefixWord, tailWord_798790, baseEnd_798790] using wordTrace_append hprefix tailTrace_798790
  have hstable : (prefixWord ++ tailWord_798790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798790).length < 2 ^ (prefixWord ++ tailWord_798790).sum := by decide
  have hdescent : baseEnd_798790 < baseStart_798790 := by decide
  rcases family_descends (prefixWord ++ tailWord_798790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798791 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_798791 : Nat := 118140960795 + 798791 * 2 ^ 59
def prefixEnd_798791 : Nat := 4983230072969 + 3 ^ 40 * 798791 * 2
def baseEnd_798791 : Nat := 364589978209501742434607

theorem tailTrace_798791 : CollatzResearch.WordTrace tailWord_798791 prefixEnd_798791 364589978209501742434607 := by
  unfold tailWord_798791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29134301249124104486748227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19422867499416069657832151 29134301249124104486748227)
  ·
    refine ⟨43701451873686156730122341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29134301249124104486748227 43701451873686156730122341)
    ·
      refine ⟨8194022226316154386897939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43701451873686156730122341 8194022226316154386897939)
      ·
        refine ⟨12291033339474231580346909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194022226316154386897939 12291033339474231580346909)
        ·
          refine ⟨4609137502302836842630091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12291033339474231580346909 4609137502302836842630091)
          ·
            refine ⟨6913706253454255263945137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609137502302836842630091 6913706253454255263945137)
            ·
              refine ⟨5185279690090691447958853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913706253454255263945137 5185279690090691447958853)
              ·
                refine ⟨972239941892004646492285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5185279690090691447958853 972239941892004646492285)
                ·
                  refine ⟨364589978209501742434607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972239941892004646492285 364589978209501742434607)
                  ·
                    rfl

theorem cell20_798791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_798791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798791 prefixEnd_798791 := by exact prefixLift 798791
  have htrace : WordTrace (prefixWord ++ tailWord_798791) baseStart_798791 baseEnd_798791 := by
    simpa [prefixWord, tailWord_798791, baseEnd_798791] using wordTrace_append hprefix tailTrace_798791
  have hstable : (prefixWord ++ tailWord_798791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798791).length < 2 ^ (prefixWord ++ tailWord_798791).sum := by decide
  have hdescent : baseEnd_798791 < baseStart_798791 := by decide
  rcases family_descends (prefixWord ++ tailWord_798791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798805 : List Nat := [1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_798805 : Nat := 118140960795 + 798805 * 2 ^ 59
def prefixEnd_798805 : Nat := 4983230072969 + 3 ^ 40 * 798805 * 2
def baseEnd_798805 : Nat := 121532122730326638655961

theorem tailTrace_798805 : CollatzResearch.WordTrace tailWord_798805 prefixEnd_798805 121532122730326638655961 := by
  unfold tailWord_798805
  simp only [CollatzResearch.WordTrace]
  refine ⟨29134811871073384877757869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19423207914048923251838579 29134811871073384877757869)
  ·
    refine ⟨10925554451652519329159201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29134811871073384877757869 10925554451652519329159201)
    ·
      refine ⟨8194165838739389496869401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10925554451652519329159201 8194165838739389496869401)
      ·
        refine ⟨6145624379054542122652051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8194165838739389496869401 6145624379054542122652051)
        ·
          refine ⟨9218436568581813183978077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145624379054542122652051 9218436568581813183978077)
          ·
            refine ⟨3456913713218179943991779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9218436568581813183978077 3456913713218179943991779)
            ·
              refine ⟨5185370569827269915987669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456913713218179943991779 5185370569827269915987669)
              ·
                refine ⟨121532122730326638655961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5185370569827269915987669 121532122730326638655961)
                ·
                  rfl

theorem cell20_798805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_798805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798805 prefixEnd_798805 := by exact prefixLift 798805
  have htrace : WordTrace (prefixWord ++ tailWord_798805) baseStart_798805 baseEnd_798805 := by
    simpa [prefixWord, tailWord_798805, baseEnd_798805] using wordTrace_append hprefix tailTrace_798805
  have hstable : (prefixWord ++ tailWord_798805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798805).length < 2 ^ (prefixWord ++ tailWord_798805).sum := by decide
  have hdescent : baseEnd_798805 < baseStart_798805 := by decide
  rcases family_descends (prefixWord ++ tailWord_798805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798808 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_798808 : Nat := 118140960795 + 798808 * 2 ^ 59
def prefixEnd_798808 : Nat := 4983230072969 + 3 ^ 40 * 798808 * 2
def baseEnd_798808 : Nat := 364597737472725238867871

theorem tailTrace_798808 : CollatzResearch.WordTrace tailWord_798808 prefixEnd_798808 364597737472725238867871 := by
  unfold tailWord_798808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567460645031258195058539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19423280860041677593411385 14567460645031258195058539)
  ·
    refine ⟨21851190967546887292587809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14567460645031258195058539 21851190967546887292587809)
    ·
      refine ⟨16388393225660165469440857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21851190967546887292587809 16388393225660165469440857)
      ·
        refine ⟨12291294919245124102080643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16388393225660165469440857 12291294919245124102080643)
        ·
          refine ⟨18436942378867686153120965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291294919245124102080643 18436942378867686153120965)
          ·
            refine ⟨3456926696037691153710181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18436942378867686153120965 3456926696037691153710181)
            ·
              refine ⟨648173755507067091320659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3456926696037691153710181 648173755507067091320659)
              ·
                refine ⟨972260633260600636980989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648173755507067091320659 972260633260600636980989)
                ·
                  refine ⟨364597737472725238867871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972260633260600636980989 364597737472725238867871)
                  ·
                    rfl

theorem cell20_798808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_798808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798808 prefixEnd_798808 := by exact prefixLift 798808
  have htrace : WordTrace (prefixWord ++ tailWord_798808) baseStart_798808 baseEnd_798808 := by
    simpa [prefixWord, tailWord_798808, baseEnd_798808] using wordTrace_append hprefix tailTrace_798808
  have hstable : (prefixWord ++ tailWord_798808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798808).length < 2 ^ (prefixWord ++ tailWord_798808).sum := by decide
  have hdescent : baseEnd_798808 < baseStart_798808 := by decide
  rcases family_descends (prefixWord ++ tailWord_798808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798887 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 2]
def baseStart_798887 : Nat := 118140960795 + 798887 * 2 ^ 59
def prefixEnd_798887 : Nat := 4983230072969 + 3 ^ 40 * 798887 * 2
def baseEnd_798887 : Nat := 364633795225352075234215

theorem tailTrace_798887 : CollatzResearch.WordTrace tailWord_798887 prefixEnd_798887 364633795225352075234215 := by
  unfold tailWord_798887
  simp only [CollatzResearch.WordTrace]
  refine ⟨29137802656776312882242915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19425201771184208588161943 29137802656776312882242915)
  ·
    refine ⟨43706703985164469323364373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29137802656776312882242915 43706703985164469323364373)
    ·
      refine ⟨2048751749304584499532705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43706703985164469323364373 2048751749304584499532705)
      ·
        refine ⟨1536563811978438374649529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048751749304584499532705 1536563811978438374649529)
        ·
          refine ⟨1152422858983828780987147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536563811978438374649529 1152422858983828780987147)
          ·
            refine ⟨1728634288475743171480721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152422858983828780987147 1728634288475743171480721)
            ·
              refine ⟨1296475716356807378610541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728634288475743171480721 1296475716356807378610541)
              ·
                refine ⟨486178393633802766978953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296475716356807378610541 486178393633802766978953)
                ·
                  refine ⟨364633795225352075234215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486178393633802766978953 364633795225352075234215)
                  ·
                    rfl

theorem cell20_798887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2].length) (baseStart_798887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798887 prefixEnd_798887 := by exact prefixLift 798887
  have htrace : WordTrace (prefixWord ++ tailWord_798887) baseStart_798887 baseEnd_798887 := by
    simpa [prefixWord, tailWord_798887, baseEnd_798887] using wordTrace_append hprefix tailTrace_798887
  have hstable : (prefixWord ++ tailWord_798887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798887).length < 2 ^ (prefixWord ++ tailWord_798887).sum := by decide
  have hdescent : baseEnd_798887 < baseStart_798887 := by decide
  rcases family_descends (prefixWord ++ tailWord_798887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798895 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_798895 : Nat := 118140960795 + 798895 * 2 ^ 59
def prefixEnd_798895 : Nat := 4983230072969 + 3 ^ 40 * 798895 * 2
def baseEnd_798895 : Nat := 364637446643339602967515

theorem tailTrace_798895 : CollatzResearch.WordTrace tailWord_798895 prefixEnd_798895 364637446643339602967515 := by
  unfold tailWord_798895
  simp only [CollatzResearch.WordTrace]
  refine ⟨29138094440747330248534139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19425396293831553499022759 29138094440747330248534139)
  ·
    refine ⟨43707141661120995372801209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29138094440747330248534139 43707141661120995372801209)
    ·
      refine ⟨32780356245840746529600907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43707141661120995372801209 32780356245840746529600907)
      ·
        refine ⟨49170534368761119794401361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32780356245840746529600907 49170534368761119794401361)
        ·
          refine ⟨36877900776570839845801021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49170534368761119794401361 36877900776570839845801021)
          ·
            refine ⟨13829212791214064942175383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36877900776570839845801021 13829212791214064942175383)
            ·
              refine ⟨20743819186821097413263075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829212791214064942175383 20743819186821097413263075)
              ·
                refine ⟨31115728780231646119894613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20743819186821097413263075 31115728780231646119894613)
                ·
                  refine ⟨364637446643339602967515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31115728780231646119894613 364637446643339602967515)
                  ·
                    rfl

theorem cell20_798895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_798895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798895 prefixEnd_798895 := by exact prefixLift 798895
  have htrace : WordTrace (prefixWord ++ tailWord_798895) baseStart_798895 baseEnd_798895 := by
    simpa [prefixWord, tailWord_798895, baseEnd_798895] using wordTrace_append hprefix tailTrace_798895
  have hstable : (prefixWord ++ tailWord_798895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798895).length < 2 ^ (prefixWord ++ tailWord_798895).sum := by decide
  have hdescent : baseEnd_798895 < baseStart_798895 := by decide
  rcases family_descends (prefixWord ++ tailWord_798895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798912 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_798912 : Nat := 118140960795 + 798912 * 2 ^ 59
def prefixEnd_798912 : Nat := 4983230072969 + 3 ^ 40 * 798912 * 2
def baseEnd_798912 : Nat := 364645205906563099400779

theorem tailTrace_798912 : CollatzResearch.WordTrace tailWord_798912 prefixEnd_798912 364645205906563099400779 := by
  unfold tailWord_798912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569357240842871075951495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19425809654457161434601993 14569357240842871075951495)
  ·
    refine ⟨21854035861264306613927243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14569357240842871075951495 21854035861264306613927243)
    ·
      refine ⟨32781053791896459920890865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21854035861264306613927243 32781053791896459920890865)
      ·
        refine ⟨24585790343922344940668149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32781053791896459920890865 24585790343922344940668149)
        ·
          refine ⟨2304917844742719838187639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24585790343922344940668149 2304917844742719838187639)
          ·
            refine ⟨3457376767114079757281459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304917844742719838187639 3457376767114079757281459)
            ·
              refine ⟨5186065150671119635922189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457376767114079757281459 5186065150671119635922189)
              ·
                refine ⟨1944774431501669863470821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186065150671119635922189 1944774431501669863470821)
                ·
                  refine ⟨364645205906563099400779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944774431501669863470821 364645205906563099400779)
                  ·
                    rfl

theorem cell20_798912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_798912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798912 prefixEnd_798912 := by exact prefixLift 798912
  have htrace : WordTrace (prefixWord ++ tailWord_798912) baseStart_798912 baseEnd_798912 := by
    simpa [prefixWord, tailWord_798912, baseEnd_798912] using wordTrace_append hprefix tailTrace_798912
  have hstable : (prefixWord ++ tailWord_798912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798912).length < 2 ^ (prefixWord ++ tailWord_798912).sum := by decide
  have hdescent : baseEnd_798912 < baseStart_798912 := by decide
  rcases family_descends (prefixWord ++ tailWord_798912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798922 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_798922 : Nat := 118140960795 + 798922 * 2 ^ 59
def prefixEnd_798922 : Nat := 4983230072969 + 3 ^ 40 * 798922 * 2
def baseEnd_798922 : Nat := 364649770179047509067405

theorem tailTrace_798922 : CollatzResearch.WordTrace tailWord_798922 prefixEnd_798922 364649770179047509067405 := by
  unfold tailWord_798922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284769802912378464941755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19426052807766342573178013 7284769802912378464941755)
  ·
    refine ⟨10927154704368567697412633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7284769802912378464941755 10927154704368567697412633)
    ·
      refine ⟨8195366028276425773059475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10927154704368567697412633 8195366028276425773059475)
      ·
        refine ⟨12293049042414638659589213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195366028276425773059475 12293049042414638659589213)
        ·
          refine ⟨4609893390905489497345955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12293049042414638659589213 4609893390905489497345955)
          ·
            refine ⟨6914840086358234246018933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609893390905489497345955 6914840086358234246018933)
            ·
              refine ⟨648266258096084460564275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6914840086358234246018933 648266258096084460564275)
              ·
                refine ⟨972399387144126690846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648266258096084460564275 972399387144126690846413)
                ·
                  refine ⟨364649770179047509067405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972399387144126690846413 364649770179047509067405)
                  ·
                    rfl

theorem cell20_798922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_798922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798922 prefixEnd_798922 := by exact prefixLift 798922
  have htrace : WordTrace (prefixWord ++ tailWord_798922) baseStart_798922 baseEnd_798922 := by
    simpa [prefixWord, tailWord_798922, baseEnd_798922] using wordTrace_append hprefix tailTrace_798922
  have hstable : (prefixWord ++ tailWord_798922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798922).length < 2 ^ (prefixWord ++ tailWord_798922).sum := by decide
  have hdescent : baseEnd_798922 < baseStart_798922 := by decide
  rcases family_descends (prefixWord ++ tailWord_798922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798936 : List Nat := [2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_798936 : Nat := 118140960795 + 798936 * 2 ^ 59
def prefixEnd_798936 : Nat := 4983230072969 + 3 ^ 40 * 798936 * 2
def baseEnd_798936 : Nat := 121552053386841894200227

theorem tailTrace_798936 : CollatzResearch.WordTrace tailWord_798936 prefixEnd_798936 121552053386841894200227 := by
  unfold tailWord_798936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569794916799397125388331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19426393222399196167184441 14569794916799397125388331)
  ·
    refine ⟨21854692375199095688082497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14569794916799397125388331 21854692375199095688082497)
    ·
      refine ⟨16391019281399321766061873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21854692375199095688082497 16391019281399321766061873)
      ·
        refine ⟨12293264461049491324546405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16391019281399321766061873 12293264461049491324546405)
        ·
          refine ⟨2304987086446779623352451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12293264461049491324546405 2304987086446779623352451)
          ·
            refine ⟨3457480629670169435028677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304987086446779623352451 3457480629670169435028677)
            ·
              refine ⟨648277618063156769067877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3457480629670169435028677 648277618063156769067877)
              ·
                refine ⟨121552053386841894200227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648277618063156769067877 121552053386841894200227)
                ·
                  rfl

theorem cell20_798936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_798936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798936 prefixEnd_798936 := by exact prefixLift 798936
  have htrace : WordTrace (prefixWord ++ tailWord_798936) baseStart_798936 baseEnd_798936 := by
    simpa [prefixWord, tailWord_798936, baseEnd_798936] using wordTrace_append hprefix tailTrace_798936
  have hstable : (prefixWord ++ tailWord_798936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798936).length < 2 ^ (prefixWord ++ tailWord_798936).sum := by decide
  have hdescent : baseEnd_798936 < baseStart_798936 := by decide
  rcases family_descends (prefixWord ++ tailWord_798936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798974 : List Nat := [4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_798974 : Nat := 118140960795 + 798974 * 2 ^ 59
def prefixEnd_798974 : Nat := 4983230072969 + 3 ^ 40 * 798974 * 2
def baseEnd_798974 : Nat := 121557834798655479777953

theorem tailTrace_798974 : CollatzResearch.WordTrace tailWord_798974 prefixEnd_798974 121557834798655479777953 := by
  unfold tailWord_798974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642621975932640842582497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19427317204974084493773317 3642621975932640842582497)
  ·
    refine ⟨2731966481949480631936873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3642621975932640842582497 2731966481949480631936873)
    ·
      refine ⟨2048974861462110473952655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2731966481949480631936873 2048974861462110473952655)
      ·
        refine ⟨3073462292193165710928983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048974861462110473952655 3073462292193165710928983)
        ·
          refine ⟨4610193438289748566393475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073462292193165710928983 4610193438289748566393475)
          ·
            refine ⟨6915290157434622849590213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610193438289748566393475 6915290157434622849590213)
            ·
              refine ⟨1296616904518991784298165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6915290157434622849590213 1296616904518991784298165)
              ·
                refine ⟨121557834798655479777953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1296616904518991784298165 121557834798655479777953)
                ·
                  rfl

theorem cell20_798974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_798974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_798974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_798974 prefixEnd_798974 := by exact prefixLift 798974
  have htrace : WordTrace (prefixWord ++ tailWord_798974) baseStart_798974 baseEnd_798974 := by
    simpa [prefixWord, tailWord_798974, baseEnd_798974] using wordTrace_append hprefix tailTrace_798974
  have hstable : (prefixWord ++ tailWord_798974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798974).length < 2 ^ (prefixWord ++ tailWord_798974).sum := by decide
  have hdescent : baseEnd_798974 < baseStart_798974 := by decide
  rcases family_descends (prefixWord ++ tailWord_798974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799018 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_799018 : Nat := 118140960795 + 799018 * 2 ^ 59
def prefixEnd_799018 : Nat := 4983230072969 + 3 ^ 40 * 799018 * 2
def baseEnd_799018 : Nat := 364693587194897841867013

theorem tailTrace_799018 : CollatzResearch.WordTrace tailWord_799018 prefixEnd_799018 364693587194897841867013 := by
  unfold tailWord_799018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285645154825430563815427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19428387079534481503507805 7285645154825430563815427)
  ·
    refine ⟨10928467732238145845723141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7285645154825430563815427 10928467732238145845723141)
    ·
      refine ⟨2049087699794652346073089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10928467732238145845723141 2049087699794652346073089)
      ·
        refine ⟨1536815774845989259554817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2049087699794652346073089 1536815774845989259554817)
        ·
          refine ⟨1152611831134491944666113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536815774845989259554817 1152611831134491944666113)
          ·
            refine ⟨864458873350868958499585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152611831134491944666113 864458873350868958499585)
            ·
              refine ⟨648344155013151718874689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864458873350868958499585 648344155013151718874689)
              ·
                refine ⟨486258116259863789156017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648344155013151718874689 486258116259863789156017)
                ·
                  refine ⟨364693587194897841867013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486258116259863789156017 364693587194897841867013)
                  ·
                    rfl

theorem cell20_799018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_799018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799018 prefixEnd_799018 := by exact prefixLift 799018
  have htrace : WordTrace (prefixWord ++ tailWord_799018) baseStart_799018 baseEnd_799018 := by
    simpa [prefixWord, tailWord_799018, baseEnd_799018] using wordTrace_append hprefix tailTrace_799018
  have hstable : (prefixWord ++ tailWord_799018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799018).length < 2 ^ (prefixWord ++ tailWord_799018).sum := by decide
  have hdescent : baseEnd_799018 < baseStart_799018 := by decide
  rcases family_descends (prefixWord ++ tailWord_799018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799060 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_799060 : Nat := 118140960795 + 799060 * 2 ^ 59
def prefixEnd_799060 : Nat := 4983230072969 + 3 ^ 40 * 799060 * 2
def baseEnd_799060 : Nat := 364712757139332362466841

theorem tailTrace_799060 : CollatzResearch.WordTrace tailWord_799060 prefixEnd_799060 364712757139332362466841 := by
  unfold tailWord_799060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572056242574781714145317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19429408323433042285527089 14572056242574781714145317)
  ·
    refine ⟨2732260545482771571402247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14572056242574781714145317 2732260545482771571402247)
    ·
      refine ⟨4098390818224157357103371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732260545482771571402247 4098390818224157357103371)
      ·
        refine ⟨6147586227336236035655057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098390818224157357103371 6147586227336236035655057)
        ·
          refine ⟨4610689670502177026741293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6147586227336236035655057 4610689670502177026741293)
          ·
            refine ⟨1729008626438316385027985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4610689670502177026741293 1729008626438316385027985)
            ·
              refine ⟨1296756469828737288770989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729008626438316385027985 1296756469828737288770989)
              ·
                refine ⟨486283676185776483289121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296756469828737288770989 486283676185776483289121)
                ·
                  refine ⟨364712757139332362466841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486283676185776483289121 364712757139332362466841)
                  ·
                    rfl

theorem cell20_799060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_799060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799060 prefixEnd_799060 := by exact prefixLift 799060
  have htrace : WordTrace (prefixWord ++ tailWord_799060) baseStart_799060 baseEnd_799060 := by
    simpa [prefixWord, tailWord_799060, baseEnd_799060] using wordTrace_append hprefix tailTrace_799060
  have hstable : (prefixWord ++ tailWord_799060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799060).length < 2 ^ (prefixWord ++ tailWord_799060).sum := by decide
  have hdescent : baseEnd_799060 < baseStart_799060 := by decide
  rcases family_descends (prefixWord ++ tailWord_799060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799074 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_799074 : Nat := 118140960795 + 799074 * 2 ^ 59
def prefixEnd_799074 : Nat := 4983230072969 + 3 ^ 40 * 799074 * 2
def baseEnd_799074 : Nat := 364719147120810536000117

theorem tailTrace_799074 : CollatzResearch.WordTrace tailWord_799074 prefixEnd_799074 364719147120810536000117 := by
  unfold tailWord_799074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286155776774710954825069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19429748738065895879533517 7286155776774710954825069)
  ·
    refine ⟨2732308416290516608059401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7286155776774710954825069 2732308416290516608059401)
    ·
      refine ⟨2049231312217887456044551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2732308416290516608059401 2049231312217887456044551)
      ·
        refine ⟨3073846968326831184066827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049231312217887456044551 3073846968326831184066827)
        ·
          refine ⟨4610770452490246776100241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073846968326831184066827 4610770452490246776100241)
          ·
            refine ⟨3458077839367685082075181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4610770452490246776100241 3458077839367685082075181)
            ·
              refine ⟨1296779189762881905778193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3458077839367685082075181 1296779189762881905778193)
              ·
                refine ⟨972584392322161429333645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296779189762881905778193 972584392322161429333645)
                ·
                  refine ⟨364719147120810536000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972584392322161429333645 364719147120810536000117)
                  ·
                    rfl

theorem cell20_799074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_799074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799074 prefixEnd_799074 := by exact prefixLift 799074
  have htrace : WordTrace (prefixWord ++ tailWord_799074) baseStart_799074 baseEnd_799074 := by
    simpa [prefixWord, tailWord_799074, baseEnd_799074] using wordTrace_append hprefix tailTrace_799074
  have hstable : (prefixWord ++ tailWord_799074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799074).length < 2 ^ (prefixWord ++ tailWord_799074).sum := by decide
  have hdescent : baseEnd_799074 < baseStart_799074 := by decide
  rcases family_descends (prefixWord ++ tailWord_799074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799105 : List Nat := [1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_799105 : Nat := 118140960795 + 799105 * 2 ^ 59
def prefixEnd_799105 : Nat := 4983230072969 + 3 ^ 40 * 799105 * 2
def baseEnd_799105 : Nat := 121577765455170735322219

theorem tailTrace_799105 : CollatzResearch.WordTrace tailWord_799105 prefixEnd_799105 121577765455170735322219 := by
  unfold tailWord_799105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29145753769986536113678769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19430502513324357409119179 29145753769986536113678769)
  ·
    refine ⟨21859315327489902085259077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29145753769986536113678769 21859315327489902085259077)
    ·
      refine ⟨4098621623904356640986077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21859315327489902085259077 4098621623904356640986077)
      ·
        refine ⟨1536983108964133740369779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4098621623904356640986077 1536983108964133740369779)
        ·
          refine ⟨2305474663446200610554669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536983108964133740369779 2305474663446200610554669)
          ·
            refine ⟨864552998792325228958001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2305474663446200610554669 864552998792325228958001)
            ·
              refine ⟨648414749094243921718501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864552998792325228958001 648414749094243921718501)
              ·
                refine ⟨121577765455170735322219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648414749094243921718501 121577765455170735322219)
                ·
                  rfl

theorem cell20_799105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_799105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799105 prefixEnd_799105 := by exact prefixLift 799105
  have htrace : WordTrace (prefixWord ++ tailWord_799105) baseStart_799105 baseEnd_799105 := by
    simpa [prefixWord, tailWord_799105, baseEnd_799105] using wordTrace_append hprefix tailTrace_799105
  have hstable : (prefixWord ++ tailWord_799105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799105).length < 2 ^ (prefixWord ++ tailWord_799105).sum := by decide
  have hdescent : baseEnd_799105 < baseStart_799105 := by decide
  rcases family_descends (prefixWord ++ tailWord_799105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799116 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_799116 : Nat := 118140960795 + 799116 * 2 ^ 59
def prefixEnd_799116 : Nat := 4983230072969 + 3 ^ 40 * 799116 * 2
def baseEnd_799116 : Nat := 364738317065245056599945

theorem tailTrace_799116 : CollatzResearch.WordTrace tailWord_799116 prefixEnd_799116 364738317065245056599945 := by
  unfold tailWord_799116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573077486473342496164601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19430769981964456661552801 14573077486473342496164601)
  ·
    refine ⟨10929808114855006872123451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14573077486473342496164601 10929808114855006872123451)
    ·
      refine ⟨16394712172282510308185177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929808114855006872123451 16394712172282510308185177)
      ·
        refine ⟨12296034129211882731138883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16394712172282510308185177 12296034129211882731138883)
        ·
          refine ⟨18444051193817824096708325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12296034129211882731138883 18444051193817824096708325)
          ·
            refine ⟨3458259598840842018132811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18444051193817824096708325 3458259598840842018132811)
            ·
              refine ⟨5187389398261263027199217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458259598840842018132811 5187389398261263027199217)
              ·
                refine ⟨3890542048695947270399413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187389398261263027199217 3890542048695947270399413)
                ·
                  refine ⟨364738317065245056599945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3890542048695947270399413 364738317065245056599945)
                  ·
                    rfl

theorem cell20_799116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_799116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799116 prefixEnd_799116 := by exact prefixLift 799116
  have htrace : WordTrace (prefixWord ++ tailWord_799116) baseStart_799116 baseEnd_799116 := by
    simpa [prefixWord, tailWord_799116, baseEnd_799116] using wordTrace_append hprefix tailTrace_799116
  have hstable : (prefixWord ++ tailWord_799116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799116).length < 2 ^ (prefixWord ++ tailWord_799116).sum := by decide
  have hdescent : baseEnd_799116 < baseStart_799116 := by decide
  rcases family_descends (prefixWord ++ tailWord_799116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799136 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_799136 : Nat := 118140960795 + 799136 * 2 ^ 59
def prefixEnd_799136 : Nat := 4983230072969 + 3 ^ 40 * 799136 * 2
def baseEnd_799136 : Nat := 364747445610213875933197

theorem tailTrace_799136 : CollatzResearch.WordTrace tailWord_799136 prefixEnd_799136 364747445610213875933197 := by
  unfold tailWord_799136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573442216437114204028631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19431256288582818938704841 14573442216437114204028631)
  ·
    refine ⟨21860163324655671306042947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14573442216437114204028631 21860163324655671306042947)
    ·
      refine ⟨32790244986983506959064421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21860163324655671306042947 32790244986983506959064421)
      ·
        refine ⟨6148170935059407554824579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32790244986983506959064421 6148170935059407554824579)
        ·
          refine ⟨9222256402589111332236869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148170935059407554824579 9222256402589111332236869)
          ·
            refine ⟨1729173075485458374794413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9222256402589111332236869 1729173075485458374794413)
            ·
              refine ⟨648439903307046890547905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1729173075485458374794413 648439903307046890547905)
              ·
                refine ⟨486329927480285167910929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648439903307046890547905 486329927480285167910929)
                ·
                  refine ⟨364747445610213875933197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486329927480285167910929 364747445610213875933197)
                  ·
                    rfl

theorem cell20_799136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_799136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799136 prefixEnd_799136 := by exact prefixLift 799136
  have htrace : WordTrace (prefixWord ++ tailWord_799136) baseStart_799136 baseEnd_799136 := by
    simpa [prefixWord, tailWord_799136, baseEnd_799136] using wordTrace_append hprefix tailTrace_799136
  have hstable : (prefixWord ++ tailWord_799136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799136).length < 2 ^ (prefixWord ++ tailWord_799136).sum := by decide
  have hdescent : baseEnd_799136 < baseStart_799136 := by decide
  rcases family_descends (prefixWord ++ tailWord_799136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799140 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_799140 : Nat := 118140960795 + 799140 * 2 ^ 59
def prefixEnd_799140 : Nat := 4983230072969 + 3 ^ 40 * 799140 * 2
def baseEnd_799140 : Nat := 364749271319207639799847

theorem tailTrace_799140 : CollatzResearch.WordTrace tailWord_799140 prefixEnd_799140 364749271319207639799847 := by
  unfold tailWord_799140
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573515162429868545601437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19431353549906491394135249 14573515162429868545601437)
  ·
    refine ⟨5465068185911200704600539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14573515162429868545601437 5465068185911200704600539)
    ·
      refine ⟨8197602278866801056900809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465068185911200704600539 8197602278866801056900809)
      ·
        refine ⟨6148201709150100792675607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8197602278866801056900809 6148201709150100792675607)
        ·
          refine ⟨9222302563725151189013411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148201709150100792675607 9222302563725151189013411)
          ·
            refine ⟨13833453845587726783520117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222302563725151189013411 13833453845587726783520117)
            ·
              refine ⟨1296886298023849385955011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13833453845587726783520117 1296886298023849385955011)
              ·
                refine ⟨1945329447035774078932517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296886298023849385955011 1945329447035774078932517)
                ·
                  refine ⟨364749271319207639799847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945329447035774078932517 364749271319207639799847)
                  ·
                    rfl

theorem cell20_799140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_799140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799140 prefixEnd_799140 := by exact prefixLift 799140
  have htrace : WordTrace (prefixWord ++ tailWord_799140) baseStart_799140 baseEnd_799140 := by
    simpa [prefixWord, tailWord_799140, baseEnd_799140] using wordTrace_append hprefix tailTrace_799140
  have hstable : (prefixWord ++ tailWord_799140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799140).length < 2 ^ (prefixWord ++ tailWord_799140).sum := by decide
  have hdescent : baseEnd_799140 < baseStart_799140 := by decide
  rcases family_descends (prefixWord ++ tailWord_799140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799146 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_799146 : Nat := 118140960795 + 799146 * 2 ^ 59
def prefixEnd_799146 : Nat := 4983230072969 + 3 ^ 40 * 799146 * 2
def baseEnd_799146 : Nat := 364752009882698285599823

theorem tailTrace_799146 : CollatzResearch.WordTrace tailWord_799146 prefixEnd_799146 364752009882698285599823 := by
  unfold tailWord_799146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286812290709500028980323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19431499441892000077280861 7286812290709500028980323)
  ·
    refine ⟨10930218436064250043470485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286812290709500028980323 10930218436064250043470485)
    ·
      refine ⟨512353989190511720787679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10930218436064250043470485 512353989190511720787679)
      ·
        refine ⟨768530983785767581181519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512353989190511720787679 768530983785767581181519)
        ·
          refine ⟨1152796475678651371772279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768530983785767581181519 1152796475678651371772279)
          ·
            refine ⟨1729194713517977057658419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152796475678651371772279 1729194713517977057658419)
            ·
              refine ⟨2593792070276965586487629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729194713517977057658419 2593792070276965586487629)
              ·
                refine ⟨972672026353862094932861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593792070276965586487629 972672026353862094932861)
                ·
                  refine ⟨364752009882698285599823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972672026353862094932861 364752009882698285599823)
                  ·
                    rfl

theorem cell20_799146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_799146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799146 prefixEnd_799146 := by exact prefixLift 799146
  have htrace : WordTrace (prefixWord ++ tailWord_799146) baseStart_799146 baseEnd_799146 := by
    simpa [prefixWord, tailWord_799146, baseEnd_799146] using wordTrace_append hprefix tailTrace_799146
  have hstable : (prefixWord ++ tailWord_799146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799146).length < 2 ^ (prefixWord ++ tailWord_799146).sum := by decide
  have hdescent : baseEnd_799146 < baseStart_799146 := by decide
  rcases family_descends (prefixWord ++ tailWord_799146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799188 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_799188 : Nat := 118140960795 + 799188 * 2 ^ 59
def prefixEnd_799188 : Nat := 4983230072969 + 3 ^ 40 * 799188 * 2
def baseEnd_799188 : Nat := 364771179827132806199651

theorem tailTrace_799188 : CollatzResearch.WordTrace tailWord_799188 prefixEnd_799188 364771179827132806199651 := by
  unfold tailWord_799188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574390514342920644475109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19432520685790560859300145 14574390514342920644475109)
  ·
    refine ⟨2732698221439297620839083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14574390514342920644475109 2732698221439297620839083)
    ·
      refine ⟨4099047332158946431258625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732698221439297620839083 4099047332158946431258625)
      ·
        refine ⟨3074285499119209823443969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4099047332158946431258625 3074285499119209823443969)
        ·
          refine ⟨2305714124339407367582977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074285499119209823443969 2305714124339407367582977)
          ·
            refine ⟨1729285593254555525687233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2305714124339407367582977 1729285593254555525687233)
            ·
              refine ⟨1296964194940916644265425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729285593254555525687233 1296964194940916644265425)
              ·
                refine ⟨972723146205687483199069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296964194940916644265425 972723146205687483199069)
                ·
                  refine ⟨364771179827132806199651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972723146205687483199069 364771179827132806199651)
                  ·
                    rfl

theorem cell20_799188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_799188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799188 prefixEnd_799188 := by exact prefixLift 799188
  have htrace : WordTrace (prefixWord ++ tailWord_799188) baseStart_799188 baseEnd_799188 := by
    simpa [prefixWord, tailWord_799188, baseEnd_799188] using wordTrace_append hprefix tailTrace_799188
  have hstable : (prefixWord ++ tailWord_799188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799188).length < 2 ^ (prefixWord ++ tailWord_799188).sum := by decide
  have hdescent : baseEnd_799188 < baseStart_799188 := by decide
  rcases family_descends (prefixWord ++ tailWord_799188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799233 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 2]
def baseStart_799233 : Nat := 118140960795 + 799233 * 2 ^ 59
def prefixEnd_799233 : Nat := 4983230072969 + 3 ^ 40 * 799233 * 2
def baseEnd_799233 : Nat := 364791719053312649699467

theorem tailTrace_799233 : CollatzResearch.WordTrace tailWord_799233 prefixEnd_799233 364791719053312649699467 := by
  unfold tailWord_799233
  simp only [CollatzResearch.WordTrace]
  refine ⟨29150422313522813974338353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19433614875681875982892235 29150422313522813974338353)
  ·
    refine ⟨21862816735142110480753765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29150422313522813974338353 21862816735142110480753765)
    ·
      refine ⟨4099278137839145715141331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21862816735142110480753765 4099278137839145715141331)
      ·
        refine ⟨6148917206758718572711997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099278137839145715141331 6148917206758718572711997)
        ·
          refine ⟨2305843952534519464766999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6148917206758718572711997 2305843952534519464766999)
          ·
            refine ⟨3458765928801779197150499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305843952534519464766999 3458765928801779197150499)
            ·
              refine ⟨5188148893202668795725749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458765928801779197150499 5188148893202668795725749)
              ·
                refine ⟨486388958737750199599289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5188148893202668795725749 486388958737750199599289)
                ·
                  refine ⟨364791719053312649699467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486388958737750199599289 364791719053312649699467)
                  ·
                    rfl

theorem cell20_799233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_799233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799233 prefixEnd_799233 := by exact prefixLift 799233
  have htrace : WordTrace (prefixWord ++ tailWord_799233) baseStart_799233 baseEnd_799233 := by
    simpa [prefixWord, tailWord_799233, baseEnd_799233] using wordTrace_append hprefix tailTrace_799233
  have hstable : (prefixWord ++ tailWord_799233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799233).length < 2 ^ (prefixWord ++ tailWord_799233).sum := by decide
  have hdescent : baseEnd_799233 < baseStart_799233 := by decide
  rcases family_descends (prefixWord ++ tailWord_799233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799278 : List Nat := [4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_799278 : Nat := 118140960795 + 799278 * 2 ^ 59
def prefixEnd_799278 : Nat := 4983230072969 + 3 ^ 40 * 799278 * 2
def baseEnd_799278 : Nat := 121604086093164164399761

theorem tailTrace_799278 : CollatzResearch.WordTrace tailWord_799278 prefixEnd_799278 121604086093164164399761 := by
  unfold tailWord_799278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644007949794973332465811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19434709065573191106484325 3644007949794973332465811)
  ·
    refine ⟨5466011924692459998698717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644007949794973332465811 5466011924692459998698717)
    ·
      refine ⟨2049754471759672499512019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5466011924692459998698717 2049754471759672499512019)
      ·
        refine ⟨3074631707639508749268029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049754471759672499512019 3074631707639508749268029)
        ·
          refine ⟨1152986890364815780975511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3074631707639508749268029 1152986890364815780975511)
          ·
            refine ⟨1729480335547223671463267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152986890364815780975511 1729480335547223671463267)
            ·
              refine ⟨2594220503320835507194901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729480335547223671463267 2594220503320835507194901)
              ·
                refine ⟨121604086093164164399761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2594220503320835507194901 121604086093164164399761)
                ·
                  rfl

theorem cell20_799278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_799278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799278 prefixEnd_799278 := by exact prefixLift 799278
  have htrace : WordTrace (prefixWord ++ tailWord_799278) baseStart_799278 baseEnd_799278 := by
    simpa [prefixWord, tailWord_799278, baseEnd_799278] using wordTrace_append hprefix tailTrace_799278
  have hstable : (prefixWord ++ tailWord_799278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799278).length < 2 ^ (prefixWord ++ tailWord_799278).sum := by decide
  have hdescent : baseEnd_799278 < baseStart_799278 := by decide
  rcases family_descends (prefixWord ++ tailWord_799278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799284 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_799284 : Nat := 118140960795 + 799284 * 2 ^ 59
def prefixEnd_799284 : Nat := 4983230072969 + 3 ^ 40 * 799284 * 2
def baseEnd_799284 : Nat := 364814996842983138999259

theorem tailTrace_799284 : CollatzResearch.WordTrace tailWord_799284 prefixEnd_799284 364814996842983138999259 := by
  unfold tailWord_799284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576141218169024842222453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19434854957558699789629937 14576141218169024842222453)
  ·
    refine ⟨1366513239203346078958355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14576141218169024842222453 1366513239203346078958355)
    ·
      refine ⟨2049769858805019118437533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366513239203346078958355 2049769858805019118437533)
      ·
        refine ⟨768663697051882169414075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2049769858805019118437533 768663697051882169414075)
        ·
          refine ⟨1152995545577823254121113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768663697051882169414075 1152995545577823254121113)
          ·
            refine ⟨864746659183367440590835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152995545577823254121113 864746659183367440590835)
            ·
              refine ⟨1297119988775051160886253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864746659183367440590835 1297119988775051160886253)
              ·
                refine ⟨486419995790644185332345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297119988775051160886253 486419995790644185332345)
                ·
                  refine ⟨364814996842983138999259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486419995790644185332345 364814996842983138999259)
                  ·
                    rfl

theorem cell20_799284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_799284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799284 prefixEnd_799284 := by exact prefixLift 799284
  have htrace : WordTrace (prefixWord ++ tailWord_799284) baseStart_799284 baseEnd_799284 := by
    simpa [prefixWord, tailWord_799284, baseEnd_799284] using wordTrace_append hprefix tailTrace_799284
  have hstable : (prefixWord ++ tailWord_799284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799284).length < 2 ^ (prefixWord ++ tailWord_799284).sum := by decide
  have hdescent : baseEnd_799284 < baseStart_799284 := by decide
  rcases family_descends (prefixWord ++ tailWord_799284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799302 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_799302 : Nat := 118140960795 + 799302 * 2 ^ 59
def prefixEnd_799302 : Nat := 4983230072969 + 3 ^ 40 * 799302 * 2
def baseEnd_799302 : Nat := 364823212533455076399185

theorem tailTrace_799302 : CollatzResearch.WordTrace tailWord_799302 prefixEnd_799302 364823212533455076399185 := by
  unfold tailWord_799302
  simp only [CollatzResearch.WordTrace]
  refine ⟨911029342196026211206255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19435292633515225839066773 911029342196026211206255)
  ·
    refine ⟨1366544013294039316809383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911029342196026211206255 1366544013294039316809383)
    ·
      refine ⟨2049816019941058975214075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366544013294039316809383 2049816019941058975214075)
      ·
        refine ⟨3074724029911588462821113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049816019941058975214075 3074724029911588462821113)
        ·
          refine ⟨2306043022433691347115835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074724029911588462821113 2306043022433691347115835)
          ·
            refine ⟨3459064533650537020673753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306043022433691347115835 3459064533650537020673753)
            ·
              refine ⟨2594298400237902765505315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459064533650537020673753 2594298400237902765505315)
              ·
                refine ⟨3891447600356854148257973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594298400237902765505315 3891447600356854148257973)
                ·
                  refine ⟨364823212533455076399185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3891447600356854148257973 364823212533455076399185)
                  ·
                    rfl

theorem cell20_799302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_799302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799302 prefixEnd_799302 := by exact prefixLift 799302
  have htrace : WordTrace (prefixWord ++ tailWord_799302) baseStart_799302 baseEnd_799302 := by
    simpa [prefixWord, tailWord_799302, baseEnd_799302] using wordTrace_append hprefix tailTrace_799302
  have hstable : (prefixWord ++ tailWord_799302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799302).length < 2 ^ (prefixWord ++ tailWord_799302).sum := by decide
  have hdescent : baseEnd_799302 < baseStart_799302 := by decide
  rcases family_descends (prefixWord ++ tailWord_799302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799306 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_799306 : Nat := 118140960795 + 799306 * 2 ^ 59
def prefixEnd_799306 : Nat := 4983230072969 + 3 ^ 40 * 799306 * 2
def baseEnd_799306 : Nat := 364825038242448840265835

theorem tailTrace_799306 : CollatzResearch.WordTrace tailWord_799306 prefixEnd_799306 364825038242448840265835 := by
  unfold tailWord_799306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288271210564586860436443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19435389894838898294497181 7288271210564586860436443)
  ·
    refine ⟨10932406815846880290654665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288271210564586860436443 10932406815846880290654665)
    ·
      refine ⟨8199305111885160217990999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10932406815846880290654665 8199305111885160217990999)
      ·
        refine ⟨12298957667827740326986499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199305111885160217990999 12298957667827740326986499)
        ·
          refine ⟨18448436501741610490479749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12298957667827740326986499 18448436501741610490479749)
          ·
            refine ⟨3459081844076551966964953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18448436501741610490479749 3459081844076551966964953)
            ·
              refine ⟨2594311383057413975223715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459081844076551966964953 2594311383057413975223715)
              ·
                refine ⟨3891467074586120962835573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594311383057413975223715 3891467074586120962835573)
                ·
                  refine ⟨364825038242448840265835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3891467074586120962835573 364825038242448840265835)
                  ·
                    rfl

theorem cell20_799306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_799306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799306 prefixEnd_799306 := by exact prefixLift 799306
  have htrace : WordTrace (prefixWord ++ tailWord_799306) baseStart_799306 baseEnd_799306 := by
    simpa [prefixWord, tailWord_799306, baseEnd_799306] using wordTrace_append hprefix tailTrace_799306
  have hstable : (prefixWord ++ tailWord_799306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799306).length < 2 ^ (prefixWord ++ tailWord_799306).sum := by decide
  have hdescent : baseEnd_799306 < baseStart_799306 := by decide
  rcases family_descends (prefixWord ++ tailWord_799306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799309 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_799309 : Nat := 118140960795 + 799309 * 2 ^ 59
def prefixEnd_799309 : Nat := 4983230072969 + 3 ^ 40 * 799309 * 2
def baseEnd_799309 : Nat := 364826407524194163165823

theorem tailTrace_799309 : CollatzResearch.WordTrace tailWord_799309 prefixEnd_799309 364826407524194163165823 := by
  unfold tailWord_799309
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153194261247478954104981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19435462840831652636069987 29153194261247478954104981)
  ·
    refine ⟨1366555980995975575973671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29153194261247478954104981 1366555980995975575973671)
    ·
      refine ⟨2049833971493963363960507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366555980995975575973671 2049833971493963363960507)
      ·
        refine ⟨3074750957240945045940761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049833971493963363960507 3074750957240945045940761)
        ·
          refine ⟨2306063217930708784455571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074750957240945045940761 2306063217930708784455571)
          ·
            refine ⟨3459094826896063176683357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306063217930708784455571 3459094826896063176683357)
            ·
              refine ⟨1297160560086023691256259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3459094826896063176683357 1297160560086023691256259)
              ·
                refine ⟨1945740840129035536884389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297160560086023691256259 1945740840129035536884389)
                ·
                  refine ⟨364826407524194163165823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945740840129035536884389 364826407524194163165823)
                  ·
                    rfl

theorem cell20_799309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_799309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799309 prefixEnd_799309 := by exact prefixLift 799309
  have htrace : WordTrace (prefixWord ++ tailWord_799309) baseStart_799309 baseEnd_799309 := by
    simpa [prefixWord, tailWord_799309, baseEnd_799309] using wordTrace_append hprefix tailTrace_799309
  have hstable : (prefixWord ++ tailWord_799309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799309).length < 2 ^ (prefixWord ++ tailWord_799309).sum := by decide
  have hdescent : baseEnd_799309 < baseStart_799309 := by decide
  rcases family_descends (prefixWord ++ tailWord_799309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799320 : List Nat := [2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_799320 : Nat := 118140960795 + 799320 * 2 ^ 59
def prefixEnd_799320 : Nat := 4983230072969 + 3 ^ 40 * 799320 * 2
def baseEnd_799320 : Nat := 121610476074642337933037

theorem tailTrace_799320 : CollatzResearch.WordTrace tailWord_799320 prefixEnd_799320 121610476074642337933037 := by
  unfold tailWord_799320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576797732103813916377707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19435730309471751888503609 14576797732103813916377707)
  ·
    refine ⟨21865196598155720874566561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576797732103813916377707 21865196598155720874566561)
    ·
      refine ⟨16398897448616790655924921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21865196598155720874566561 16398897448616790655924921)
      ·
        refine ⟨12299173086462592991943691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16398897448616790655924921 12299173086462592991943691)
        ·
          refine ⟨18448759629693889487915537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12299173086462592991943691 18448759629693889487915537)
          ·
            refine ⟨13836569722270417115936653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18448759629693889487915537 13836569722270417115936653)
            ·
              refine ⟨5188713645851406418476245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13836569722270417115936653 5188713645851406418476245)
              ·
                refine ⟨121610476074642337933037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5188713645851406418476245 121610476074642337933037)
                ·
                  rfl

theorem cell20_799320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_799320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799320 prefixEnd_799320 := by exact prefixLift 799320
  have htrace : WordTrace (prefixWord ++ tailWord_799320) baseStart_799320 baseEnd_799320 := by
    simpa [prefixWord, tailWord_799320, baseEnd_799320] using wordTrace_append hprefix tailTrace_799320
  have hstable : (prefixWord ++ tailWord_799320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799320).length < 2 ^ (prefixWord ++ tailWord_799320).sum := by decide
  have hdescent : baseEnd_799320 < baseStart_799320 := by decide
  rcases family_descends (prefixWord ++ tailWord_799320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799358 : List Nat := [4, 2, 14]
def baseStart_799358 : Nat := 118140960795 + 799358 * 2 ^ 59
def prefixEnd_799358 : Nat := 4983230072969 + 3 ^ 40 * 799358 * 2
def baseEnd_799358 : Nat := 500478425870188985641

theorem tailTrace_799358 : CollatzResearch.WordTrace tailWord_799358 prefixEnd_799358 500478425870188985641 := by
  unfold tailWord_799358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644372679758745040329841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19436654292046640215092485 3644372679758745040329841)
  ·
    refine ⟨2733279509819058780247381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3644372679758745040329841 2733279509819058780247381)
    ·
      refine ⟨500478425870188985641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2733279509819058780247381 500478425870188985641)
      ·
        rfl

theorem cell20_799358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 14].length) (baseStart_799358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799358 prefixEnd_799358 := by exact prefixLift 799358
  have htrace : WordTrace (prefixWord ++ tailWord_799358) baseStart_799358 baseEnd_799358 := by
    simpa [prefixWord, tailWord_799358, baseEnd_799358] using wordTrace_append hprefix tailTrace_799358
  have hstable : (prefixWord ++ tailWord_799358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799358).length < 2 ^ (prefixWord ++ tailWord_799358).sum := by decide
  have hdescent : baseEnd_799358 < baseStart_799358 := by decide
  rcases family_descends (prefixWord ++ tailWord_799358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799361 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_799361 : Nat := 118140960795 + 799361 * 2 ^ 59
def prefixEnd_799361 : Nat := 4983230072969 + 3 ^ 40 * 799361 * 2
def baseEnd_799361 : Nat := 364850141741113093432277

theorem tailTrace_799361 : CollatzResearch.WordTrace tailWord_799361 prefixEnd_799361 364850141741113093432277 := by
  unfold tailWord_799361
  simp only [CollatzResearch.WordTrace]
  refine ⟨29155090857059091834997937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19436727238039394556665291 29155090857059091834997937)
  ·
    refine ⟨21866318142794318876248453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29155090857059091834997937 21866318142794318876248453)
    ·
      refine ⟨4099934651773934789296585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21866318142794318876248453 4099934651773934789296585)
      ·
        refine ⟨3074950988830451091972439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4099934651773934789296585 3074950988830451091972439)
        ·
          refine ⟨4612426483245676637958659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074950988830451091972439 4612426483245676637958659)
          ·
            refine ⟨6918639724868514956937989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612426483245676637958659 6918639724868514956937989)
            ·
              refine ⟨1297244948412846554425873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6918639724868514956937989 1297244948412846554425873)
              ·
                refine ⟨972933711309634915819405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297244948412846554425873 972933711309634915819405)
                ·
                  refine ⟨364850141741113093432277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972933711309634915819405 364850141741113093432277)
                  ·
                    rfl

theorem cell20_799361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_799361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799361 prefixEnd_799361 := by exact prefixLift 799361
  have htrace : WordTrace (prefixWord ++ tailWord_799361) baseStart_799361 baseEnd_799361 := by
    simpa [prefixWord, tailWord_799361, baseEnd_799361] using wordTrace_append hprefix tailTrace_799361
  have hstable : (prefixWord ++ tailWord_799361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799361).length < 2 ^ (prefixWord ++ tailWord_799361).sum := by decide
  have hdescent : baseEnd_799361 < baseStart_799361 := by decide
  rcases family_descends (prefixWord ++ tailWord_799361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799364 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_799364 : Nat := 118140960795 + 799364 * 2 ^ 59
def prefixEnd_799364 : Nat := 4983230072969 + 3 ^ 40 * 799364 * 2
def baseEnd_799364 : Nat := 364851511022858416332265

theorem tailTrace_799364 : CollatzResearch.WordTrace tailWord_799364 prefixEnd_799364 364851511022858416332265 := by
  unfold tailWord_799364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577600138024111673678573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19436800184032148898238097 14577600138024111673678573)
  ·
    refine ⟨5466600051759041877629465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14577600138024111673678573 5466600051759041877629465)
    ·
      refine ⟨4099950038819281408222099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5466600051759041877629465 4099950038819281408222099)
      ·
        refine ⟨6149925058228922112333149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099950038819281408222099 6149925058228922112333149)
        ·
          refine ⟨2306221896835845792124931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6149925058228922112333149 2306221896835845792124931)
          ·
            refine ⟨3459332845253768688187397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306221896835845792124931 3459332845253768688187397)
            ·
              refine ⟨648624908485081629035137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3459332845253768688187397 648624908485081629035137)
              ·
                refine ⟨486468681363811221776353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648624908485081629035137 486468681363811221776353)
                ·
                  refine ⟨364851511022858416332265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486468681363811221776353 364851511022858416332265)
                  ·
                    rfl

theorem cell20_799364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_799364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799364 prefixEnd_799364 := by exact prefixLift 799364
  have htrace : WordTrace (prefixWord ++ tailWord_799364) baseStart_799364 baseEnd_799364 := by
    simpa [prefixWord, tailWord_799364, baseEnd_799364] using wordTrace_append hprefix tailTrace_799364
  have hstable : (prefixWord ++ tailWord_799364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799364).length < 2 ^ (prefixWord ++ tailWord_799364).sum := by decide
  have hdescent : baseEnd_799364 < baseStart_799364 := by decide
  rcases family_descends (prefixWord ++ tailWord_799364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799389 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_799389 : Nat := 118140960795 + 799389 * 2 ^ 59
def prefixEnd_799389 : Nat := 4983230072969 + 3 ^ 40 * 799389 * 2
def baseEnd_799389 : Nat := 364862921704069440498829

theorem tailTrace_799389 : CollatzResearch.WordTrace tailWord_799389 prefixEnd_799389 364862921704069440498829 := by
  unfold tailWord_799389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156112100957652617017221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19437408067305101744678147 29156112100957652617017221)
  ·
    refine ⟨5466771018929559865690729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29156112100957652617017221 5466771018929559865690729)
    ·
      refine ⟨4100078264197169899268047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5466771018929559865690729 4100078264197169899268047)
      ·
        refine ⟨6150117396295754848902071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100078264197169899268047 6150117396295754848902071)
        ·
          refine ⟨9225176094443632273353107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150117396295754848902071 9225176094443632273353107)
          ·
            refine ⟨13837764141665448410029661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225176094443632273353107 13837764141665448410029661)
            ·
              refine ⟨5189161553124543153761123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13837764141665448410029661 5189161553124543153761123)
              ·
                refine ⟨7783742329686814730641685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189161553124543153761123 7783742329686814730641685)
                ·
                  refine ⟨364862921704069440498829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7783742329686814730641685 364862921704069440498829)
                  ·
                    rfl

theorem cell20_799389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_799389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799389 prefixEnd_799389 := by exact prefixLift 799389
  have htrace : WordTrace (prefixWord ++ tailWord_799389) baseStart_799389 baseEnd_799389 := by
    simpa [prefixWord, tailWord_799389, baseEnd_799389] using wordTrace_append hprefix tailTrace_799389
  have hstable : (prefixWord ++ tailWord_799389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799389).length < 2 ^ (prefixWord ++ tailWord_799389).sum := by decide
  have hdescent : baseEnd_799389 < baseStart_799389 := by decide
  rcases family_descends (prefixWord ++ tailWord_799389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799392 : List Nat := [2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_799392 : Nat := 118140960795 + 799392 * 2 ^ 59
def prefixEnd_799392 : Nat := 4983230072969 + 3 ^ 40 * 799392 * 2
def baseEnd_799392 : Nat := 121621430328604921132939

theorem tailTrace_799392 : CollatzResearch.WordTrace tailWord_799392 prefixEnd_799392 121621430328604921132939 := by
  unfold tailWord_799392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578110759973392064688215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19437481013297856086250953 14578110759973392064688215)
  ·
    refine ⟨21867166139960088097032323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14578110759973392064688215 21867166139960088097032323)
    ·
      refine ⟨32800749209940132145548485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21867166139960088097032323 32800749209940132145548485)
      ·
        refine ⟨6150140476863774777290341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32800749209940132145548485 6150140476863774777290341)
        ·
          refine ⟨1153151339411957770741939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6150140476863774777290341 1153151339411957770741939)
          ·
            refine ⟨1729727009117936656112909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153151339411957770741939 1729727009117936656112909)
            ·
              refine ⟨648647628419226246042341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1729727009117936656112909 648647628419226246042341)
              ·
                refine ⟨121621430328604921132939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648647628419226246042341 121621430328604921132939)
                ·
                  rfl

theorem cell20_799392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_799392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799392 prefixEnd_799392 := by exact prefixLift 799392
  have htrace : WordTrace (prefixWord ++ tailWord_799392) baseStart_799392 baseEnd_799392 := by
    simpa [prefixWord, tailWord_799392, baseEnd_799392] using wordTrace_append hprefix tailTrace_799392
  have hstable : (prefixWord ++ tailWord_799392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799392).length < 2 ^ (prefixWord ++ tailWord_799392).sum := by decide
  have hdescent : baseEnd_799392 < baseStart_799392 := by decide
  rcases family_descends (prefixWord ++ tailWord_799392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799413 : List Nat := [1, 3, 3, 3, 1, 2, 7]
def baseStart_799413 : Nat := 118140960795 + 799413 * 2 ^ 59
def prefixEnd_799413 : Nat := 4983230072969 + 3 ^ 40 * 799413 * 2
def baseEnd_799413 : Nat := 40541541773114669299859

theorem tailTrace_799413 : CollatzResearch.WordTrace tailWord_799413 prefixEnd_799413 40541541773114669299859 := by
  unfold tailWord_799413
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156987452870704715890893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19437991635247136477260595 29156987452870704715890893)
  ·
    refine ⟨10933870294826514268459085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29156987452870704715890893 10933870294826514268459085)
    ·
      refine ⟨4100201360559942850672157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10933870294826514268459085 4100201360559942850672157)
      ·
        refine ⟨1537575510209978569002059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4100201360559942850672157 1537575510209978569002059)
        ·
          refine ⟨2306363265314967853503089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537575510209978569002059 2306363265314967853503089)
          ·
            refine ⟨1729772448986225890127317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306363265314967853503089 1729772448986225890127317)
            ·
              refine ⟨40541541773114669299859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1729772448986225890127317 40541541773114669299859)
              ·
                rfl

theorem cell20_799413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_799413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799413 prefixEnd_799413 := by exact prefixLift 799413
  have htrace : WordTrace (prefixWord ++ tailWord_799413) baseStart_799413 baseEnd_799413 := by
    simpa [prefixWord, tailWord_799413, baseEnd_799413] using wordTrace_append hprefix tailTrace_799413
  have hstable : (prefixWord ++ tailWord_799413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799413).length < 2 ^ (prefixWord ++ tailWord_799413).sum := by decide
  have hdescent : baseEnd_799413 < baseStart_799413 := by decide
  rcases family_descends (prefixWord ++ tailWord_799413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799420 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_799420 : Nat := 118140960795 + 799420 * 2 ^ 59
def prefixEnd_799420 : Nat := 4983230072969 + 3 ^ 40 * 799420 * 2
def baseEnd_799420 : Nat := 364877070948771110465369

theorem tailTrace_799420 : CollatzResearch.WordTrace tailWord_799420 prefixEnd_799420 364877070948771110465369 := by
  unfold tailWord_799420
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578621381922672455697857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19438161842563563274263809 14578621381922672455697857)
  ·
    refine ⟨10933966036442004341773393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14578621381922672455697857 10933966036442004341773393)
    ·
      refine ⟨8200474527331503256330045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10933966036442004341773393 8200474527331503256330045)
      ·
        refine ⟨3075177947749313721123767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8200474527331503256330045 3075177947749313721123767)
        ·
          refine ⟨4612766921623970581685651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075177947749313721123767 4612766921623970581685651)
          ·
            refine ⟨6919150382435955872528477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612766921623970581685651 6919150382435955872528477)
            ·
              refine ⟨2594681393413483452198179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6919150382435955872528477 2594681393413483452198179)
              ·
                refine ⟨3892022090120225178297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594681393413483452198179 3892022090120225178297269)
                ·
                  refine ⟨364877070948771110465369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3892022090120225178297269 364877070948771110465369)
                  ·
                    rfl

theorem cell20_799420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_799420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799420 prefixEnd_799420 := by exact prefixLift 799420
  have htrace : WordTrace (prefixWord ++ tailWord_799420) baseStart_799420 baseEnd_799420 := by
    simpa [prefixWord, tailWord_799420, baseEnd_799420] using wordTrace_append hprefix tailTrace_799420
  have hstable : (prefixWord ++ tailWord_799420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799420).length < 2 ^ (prefixWord ++ tailWord_799420).sum := by decide
  have hdescent : baseEnd_799420 < baseStart_799420 := by decide
  rcases family_descends (prefixWord ++ tailWord_799420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799461 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 2]
def baseStart_799461 : Nat := 118140960795 + 799461 * 2 ^ 59
def prefixEnd_799461 : Nat := 4983230072969 + 3 ^ 40 * 799461 * 2
def baseEnd_799461 : Nat := 364895784465957190098535

theorem tailTrace_799461 : CollatzResearch.WordTrace tailWord_799461 prefixEnd_799461 364895784465957190098535 := by
  unfold tailWord_799461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158738156696808913638237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19439158771131205942425491 29158738156696808913638237)
  ·
    refine ⟨10934526808761303342614339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29158738156696808913638237 10934526808761303342614339)
    ·
      refine ⟨16401790213141955013921509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934526808761303342614339 16401790213141955013921509)
      ·
        refine ⟨3075335664964116565110283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16401790213141955013921509 3075335664964116565110283)
        ·
          refine ⟨4613003497446174847665425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075335664964116565110283 4613003497446174847665425)
          ·
            refine ⟨3459752623084631135749069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613003497446174847665425 3459752623084631135749069)
            ·
              refine ⟨1297407233656736675905901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3459752623084631135749069 1297407233656736675905901)
              ·
                refine ⟨486527712621276253464713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297407233656736675905901 486527712621276253464713)
                ·
                  refine ⟨364895784465957190098535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486527712621276253464713 364895784465957190098535)
                  ·
                    rfl

theorem cell20_799461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_799461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799461 prefixEnd_799461 := by exact prefixLift 799461
  have htrace : WordTrace (prefixWord ++ tailWord_799461) baseStart_799461 baseEnd_799461 := by
    simpa [prefixWord, tailWord_799461, baseEnd_799461] using wordTrace_append hprefix tailTrace_799461
  have hstable : (prefixWord ++ tailWord_799461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799461).length < 2 ^ (prefixWord ++ tailWord_799461).sum := by decide
  have hdescent : baseEnd_799461 < baseStart_799461 := by decide
  rcases family_descends (prefixWord ++ tailWord_799461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799478 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_799478 : Nat := 118140960795 + 799478 * 2 ^ 59
def prefixEnd_799478 : Nat := 4983230072969 + 3 ^ 40 * 799478 * 2
def baseEnd_799478 : Nat := 364903543729180686531799

theorem tailTrace_799478 : CollatzResearch.WordTrace tailWord_799478 prefixEnd_799478 364903543729180686531799 := by
  unfold tailWord_799478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822459887352201301062943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19439572131756813878004725 1822459887352201301062943)
  ·
    refine ⟨2733689831028301951594415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822459887352201301062943 2733689831028301951594415)
    ·
      refine ⟨4100534746542452927391623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733689831028301951594415 4100534746542452927391623)
      ·
        refine ⟨6150802119813679391087435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100534746542452927391623 6150802119813679391087435)
        ·
          refine ⟨9226203179720519086631153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150802119813679391087435 9226203179720519086631153)
          ·
            refine ⟨6919652384790389314973365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9226203179720519086631153 6919652384790389314973365)
            ·
              refine ⟨648717411074098998278753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6919652384790389314973365 648717411074098998278753)
              ·
                refine ⟨486538058305574248709065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648717411074098998278753 486538058305574248709065)
                ·
                  refine ⟨364903543729180686531799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486538058305574248709065 364903543729180686531799)
                  ·
                    rfl

theorem cell20_799478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_799478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799478 prefixEnd_799478 := by exact prefixLift 799478
  have htrace : WordTrace (prefixWord ++ tailWord_799478) baseStart_799478 baseEnd_799478 := by
    simpa [prefixWord, tailWord_799478, baseEnd_799478] using wordTrace_append hprefix tailTrace_799478
  have hstable : (prefixWord ++ tailWord_799478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799478).length < 2 ^ (prefixWord ++ tailWord_799478).sum := by decide
  have hdescent : baseEnd_799478 < baseStart_799478 := by decide
  rcases family_descends (prefixWord ++ tailWord_799478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799482 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_799482 : Nat := 118140960795 + 799482 * 2 ^ 59
def prefixEnd_799482 : Nat := 4983230072969 + 3 ^ 40 * 799482 * 2
def baseEnd_799482 : Nat := 364905369438174450398449

theorem tailTrace_799482 : CollatzResearch.WordTrace tailWord_799482 prefixEnd_799482 364905369438174450398449 := by
  unfold tailWord_799482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289876022405182375038175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19439669393080486333435133 7289876022405182375038175)
  ·
    refine ⟨10934814033607773562557263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7289876022405182375038175 10934814033607773562557263)
    ·
      refine ⟨16402221050411660343835895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934814033607773562557263 16402221050411660343835895)
      ·
        refine ⟨24603331575617490515753843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16402221050411660343835895 24603331575617490515753843)
        ·
          refine ⟨36904997363426235773630765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24603331575617490515753843 36904997363426235773630765)
          ·
            refine ⟨13839374011284838415111537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36904997363426235773630765 13839374011284838415111537)
            ·
              refine ⟨10379530508463628811333653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13839374011284838415111537 10379530508463628811333653)
              ·
                refine ⟨486540492584232600531265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10379530508463628811333653 486540492584232600531265)
                ·
                  refine ⟨364905369438174450398449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486540492584232600531265 364905369438174450398449)
                  ·
                    rfl

theorem cell20_799482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_799482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799482 prefixEnd_799482 := by exact prefixLift 799482
  have htrace : WordTrace (prefixWord ++ tailWord_799482) baseStart_799482 baseEnd_799482 := by
    simpa [prefixWord, tailWord_799482, baseEnd_799482] using wordTrace_append hprefix tailTrace_799482
  have hstable : (prefixWord ++ tailWord_799482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799482).length < 2 ^ (prefixWord ++ tailWord_799482).sum := by decide
  have hdescent : baseEnd_799482 < baseStart_799482 := by decide
  rcases family_descends (prefixWord ++ tailWord_799482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799533 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 2]
def baseStart_799533 : Nat := 118140960795 + 799533 * 2 ^ 59
def prefixEnd_799533 : Nat := 4983230072969 + 3 ^ 40 * 799533 * 2
def baseEnd_799533 : Nat := 364928647227844939698241

theorem tailTrace_799533 : CollatzResearch.WordTrace tailWord_799533 prefixEnd_799533 364928647227844939698241 := by
  unfold tailWord_799533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161364212435965210259253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19440909474957310140172835 29161364212435965210259253)
  ·
    refine ⟨2733877894915871738461805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29161364212435965210259253 2733877894915871738461805)
    ·
      refine ⟨1025204210593451901923177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2733877894915871738461805 1025204210593451901923177)
      ·
        refine ⟨768903157945088926442383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025204210593451901923177 768903157945088926442383)
        ·
          refine ⟨1153354736917633389663575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768903157945088926442383 1153354736917633389663575)
          ·
            refine ⟨1730032105376450084495363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153354736917633389663575 1730032105376450084495363)
            ·
              refine ⟨2595048158064675126743045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730032105376450084495363 2595048158064675126743045)
              ·
                refine ⟨486571529637126586264321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2595048158064675126743045 486571529637126586264321)
                ·
                  refine ⟨364928647227844939698241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486571529637126586264321 364928647227844939698241)
                  ·
                    rfl

theorem cell20_799533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_799533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799533 prefixEnd_799533 := by exact prefixLift 799533
  have htrace : WordTrace (prefixWord ++ tailWord_799533) baseStart_799533 baseEnd_799533 := by
    simpa [prefixWord, tailWord_799533, baseEnd_799533] using wordTrace_append hprefix tailTrace_799533
  have hstable : (prefixWord ++ tailWord_799533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799533).length < 2 ^ (prefixWord ++ tailWord_799533).sum := by decide
  have hdescent : baseEnd_799533 < baseStart_799533 := by decide
  rcases family_descends (prefixWord ++ tailWord_799533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799575 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 2]
def baseStart_799575 : Nat := 118140960795 + 799575 * 2 ^ 59
def prefixEnd_799575 : Nat := 4983230072969 + 3 ^ 40 * 799575 * 2
def baseEnd_799575 : Nat := 364947817172279460298069

theorem tailTrace_799575 : CollatzResearch.WordTrace tailWord_799575 prefixEnd_799575 364947817172279460298069 := by
  unfold tailWord_799575
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162896078283806383288179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19441930718855870922192119 29162896078283806383288179)
  ·
    refine ⟨43744344117425709574932269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162896078283806383288179 43744344117425709574932269)
    ·
      refine ⟨16404129044034641090599601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43744344117425709574932269 16404129044034641090599601)
      ·
        refine ⟨12303096783025980817949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16404129044034641090599601 12303096783025980817949701)
        ·
          refine ⟨2306830646817371403365569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12303096783025980817949701 2306830646817371403365569)
          ·
            refine ⟨1730122985113028552524177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306830646817371403365569 1730122985113028552524177)
            ·
              refine ⟨1297592238834771414393133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730122985113028552524177 1297592238834771414393133)
              ·
                refine ⟨486597089563039280397425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297592238834771414393133 486597089563039280397425)
                ·
                  refine ⟨364947817172279460298069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486597089563039280397425 364947817172279460298069)
                  ·
                    rfl

theorem cell20_799575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2].length) (baseStart_799575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799575 prefixEnd_799575 := by exact prefixLift 799575
  have htrace : WordTrace (prefixWord ++ tailWord_799575) baseStart_799575 baseEnd_799575 := by
    simpa [prefixWord, tailWord_799575, baseEnd_799575] using wordTrace_append hprefix tailTrace_799575
  have hstable : (prefixWord ++ tailWord_799575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799575).length < 2 ^ (prefixWord ++ tailWord_799575).sum := by decide
  have hdescent : baseEnd_799575 < baseStart_799575 := by decide
  rcases family_descends (prefixWord ++ tailWord_799575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799596 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_799596 : Nat := 118140960795 + 799596 * 2 ^ 59
def prefixEnd_799596 : Nat := 4983230072969 + 3 ^ 40 * 799596 * 2
def baseEnd_799596 : Nat := 364957402144496720597983

theorem tailTrace_799596 : CollatzResearch.WordTrace tailWord_799596 prefixEnd_799596 364957402144496720597983 := by
  unfold tailWord_799596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581831005603863484901321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19442441340805151313201761 14581831005603863484901321)
  ·
    refine ⟨10936373254202897613675991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581831005603863484901321 10936373254202897613675991)
    ·
      refine ⟨16404559881304346420513987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936373254202897613675991 16404559881304346420513987)
      ·
        refine ⟨24606839821956519630770981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16404559881304346420513987 24606839821956519630770981)
        ·
          refine ⟨4613782466616847430769559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24606839821956519630770981 4613782466616847430769559)
          ·
            refine ⟨6920673699925271146154339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613782466616847430769559 6920673699925271146154339)
            ·
              refine ⟨10381010549887906719231509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920673699925271146154339 10381010549887906719231509)
              ·
                refine ⟨486609869525995627463977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10381010549887906719231509 486609869525995627463977)
                ·
                  refine ⟨364957402144496720597983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486609869525995627463977 364957402144496720597983)
                  ·
                    rfl

theorem cell20_799596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_799596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799596 prefixEnd_799596 := by exact prefixLift 799596
  have htrace : WordTrace (prefixWord ++ tailWord_799596) baseStart_799596 baseEnd_799596 := by
    simpa [prefixWord, tailWord_799596, baseEnd_799596] using wordTrace_append hprefix tailTrace_799596
  have hstable : (prefixWord ++ tailWord_799596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799596).length < 2 ^ (prefixWord ++ tailWord_799596).sum := by decide
  have hdescent : baseEnd_799596 < baseStart_799596 := by decide
  rcases family_descends (prefixWord ++ tailWord_799596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799665 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_799665 : Nat := 118140960795 + 799665 * 2 ^ 59
def prefixEnd_799665 : Nat := 4983230072969 + 3 ^ 40 * 799665 * 2
def baseEnd_799665 : Nat := 364988895624639147297701

theorem tailTrace_799665 : CollatzResearch.WordTrace tailWord_799665 prefixEnd_799665 364988895624639147297701 := by
  unfold tailWord_799665
  simp only [CollatzResearch.WordTrace]
  refine ⟨29166178647957751754064449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19444119098638501169376299 29166178647957751754064449)
  ·
    refine ⟨21874633985968313815548337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29166178647957751754064449 21874633985968313815548337)
    ·
      refine ⟨16405975489476235361661253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21874633985968313815548337 16405975489476235361661253)
      ·
        refine ⟨3076120404276794130311485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16405975489476235361661253 3076120404276794130311485)
        ·
          refine ⟨1153545151603797798866807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3076120404276794130311485 1153545151603797798866807)
          ·
            refine ⟨1730317727405696698300211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153545151603797798866807 1730317727405696698300211)
            ·
              refine ⟨2595476591108545047450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730317727405696698300211 2595476591108545047450317)
              ·
                refine ⟨973303721665704392793869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595476591108545047450317 973303721665704392793869)
                ·
                  refine ⟨364988895624639147297701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973303721665704392793869 364988895624639147297701)
                  ·
                    rfl

theorem cell20_799665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_799665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799665 prefixEnd_799665 := by exact prefixLift 799665
  have htrace : WordTrace (prefixWord ++ tailWord_799665) baseStart_799665 baseEnd_799665 := by
    simpa [prefixWord, tailWord_799665, baseEnd_799665] using wordTrace_append hprefix tailTrace_799665
  have hstable : (prefixWord ++ tailWord_799665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799665).length < 2 ^ (prefixWord ++ tailWord_799665).sum := by decide
  have hdescent : baseEnd_799665 < baseStart_799665 := by decide
  rcases family_descends (prefixWord ++ tailWord_799665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799700 : List Nat := [2, 4, 1, 2, 1, 10]
def baseStart_799700 : Nat := 118140960795 + 799700 * 2 ^ 59
def prefixEnd_799700 : Nat := 4983230072969 + 3 ^ 40 * 799700 * 2
def baseEnd_799700 : Nat := 13518698910308688190033

theorem tailTrace_799700 : CollatzResearch.WordTrace tailWord_799700 prefixEnd_799700 13518698910308688190033 := by
  unfold tailWord_799700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583727601415476365794277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19444970135220635154392369 14583727601415476365794277)
  ·
    refine ⟨2734448925265401818586427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14583727601415476365794277 2734448925265401818586427)
    ·
      refine ⟨4101673387898102727879641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734448925265401818586427 4101673387898102727879641)
      ·
        refine ⟨3076255040923577045909731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4101673387898102727879641 3076255040923577045909731)
        ·
          refine ⟨4614382561385365568864597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076255040923577045909731 4614382561385365568864597)
          ·
            refine ⟨13518698910308688190033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4614382561385365568864597 13518698910308688190033)
            ·
              rfl

theorem cell20_799700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 10].length) (baseStart_799700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799700 prefixEnd_799700 := by exact prefixLift 799700
  have htrace : WordTrace (prefixWord ++ tailWord_799700) baseStart_799700 baseEnd_799700 := by
    simpa [prefixWord, tailWord_799700, baseEnd_799700] using wordTrace_append hprefix tailTrace_799700
  have hstable : (prefixWord ++ tailWord_799700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799700).length < 2 ^ (prefixWord ++ tailWord_799700).sum := by decide
  have hdescent : baseEnd_799700 < baseStart_799700 := by decide
  rcases family_descends (prefixWord ++ tailWord_799700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799706 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_799706 : Nat := 118140960795 + 799706 * 2 ^ 59
def prefixEnd_799706 : Nat := 4983230072969 + 3 ^ 40 * 799706 * 2
def baseEnd_799706 : Nat := 365007609141825226930867

theorem tailTrace_799706 : CollatzResearch.WordTrace tailWord_799706 prefixEnd_799706 365007609141825226930867 := by
  unfold tailWord_799706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291918510202303939076743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19445116027206143837537981 7291918510202303939076743)
  ·
    refine ⟨10937877765303455908615115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291918510202303939076743 10937877765303455908615115)
    ·
      refine ⟨16406816647955183862922673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10937877765303455908615115 16406816647955183862922673)
      ·
        refine ⟨12305112485966387897192005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16406816647955183862922673 12305112485966387897192005)
        ·
          refine ⟨2307208591118697730723501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12305112485966387897192005 2307208591118697730723501)
          ·
            refine ⟨865203221669511649021313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2307208591118697730723501 865203221669511649021313)
            ·
              refine ⟨648902416252133736765985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865203221669511649021313 648902416252133736765985)
              ·
                refine ⟨486676812189100302574489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648902416252133736765985 486676812189100302574489)
                ·
                  refine ⟨365007609141825226930867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486676812189100302574489 365007609141825226930867)
                  ·
                    rfl

theorem cell20_799706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_799706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799706 prefixEnd_799706 := by exact prefixLift 799706
  have htrace : WordTrace (prefixWord ++ tailWord_799706) baseStart_799706 baseEnd_799706 := by
    simpa [prefixWord, tailWord_799706, baseEnd_799706] using wordTrace_append hprefix tailTrace_799706
  have hstable : (prefixWord ++ tailWord_799706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799706).length < 2 ^ (prefixWord ++ tailWord_799706).sum := by decide
  have hdescent : baseEnd_799706 < baseStart_799706 := by decide
  rcases family_descends (prefixWord ++ tailWord_799706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799734 : List Nat := [5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_799734 : Nat := 118140960795 + 799734 * 2 ^ 59
def prefixEnd_799734 : Nat := 4983230072969 + 3 ^ 40 * 799734 * 2
def baseEnd_799734 : Nat := 121673463034927191332473

theorem tailTrace_799734 : CollatzResearch.WordTrace tailWord_799734 prefixEnd_799734 121673463034927191332473 := by
  unfold tailWord_799734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823043455294236033645391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19445796856471851025550837 1823043455294236033645391)
  ·
    refine ⟨2734565182941354050468087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1823043455294236033645391 2734565182941354050468087)
    ·
      refine ⟨4101847774412031075702131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734565182941354050468087 4101847774412031075702131)
      ·
        refine ⟨6152771661618046613553197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101847774412031075702131 6152771661618046613553197)
        ·
          refine ⟨2307289373106767480082449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6152771661618046613553197 2307289373106767480082449)
          ·
            refine ⟨1730467029830075610061837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307289373106767480082449 1730467029830075610061837)
            ·
              refine ⟨648925136186278353773189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730467029830075610061837 648925136186278353773189)
              ·
                refine ⟨121673463034927191332473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648925136186278353773189 121673463034927191332473)
                ·
                  rfl

theorem cell20_799734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_799734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799734 prefixEnd_799734 := by exact prefixLift 799734
  have htrace : WordTrace (prefixWord ++ tailWord_799734) baseStart_799734 baseEnd_799734 := by
    simpa [prefixWord, tailWord_799734, baseEnd_799734] using wordTrace_append hprefix tailTrace_799734
  have hstable : (prefixWord ++ tailWord_799734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799734).length < 2 ^ (prefixWord ++ tailWord_799734).sum := by decide
  have hdescent : baseEnd_799734 < baseStart_799734 := by decide
  rcases family_descends (prefixWord ++ tailWord_799734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799779 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_799779 : Nat := 118140960795 + 799779 * 2 ^ 59
def prefixEnd_799779 : Nat := 4983230072969 + 3 ^ 40 * 799779 * 2
def baseEnd_799779 : Nat := 365040928330961417497235

theorem tailTrace_799779 : CollatzResearch.WordTrace tailWord_799779 prefixEnd_799779 365040928330961417497235 := by
  unfold tailWord_799779
  simp only [CollatzResearch.WordTrace]
  refine ⟨29170336569544749223714391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19446891046363166149142927 29170336569544749223714391)
  ·
    refine ⟨43755504854317123835571587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29170336569544749223714391 43755504854317123835571587)
    ·
      refine ⟨65633257281475685753357381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43755504854317123835571587 65633257281475685753357381)
      ·
        refine ⟨12306235740276691078754509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65633257281475685753357381 12306235740276691078754509)
        ·
          refine ⟨4614838402603759154532941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12306235740276691078754509 4614838402603759154532941)
          ·
            refine ⟨1730564400976409682949853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4614838402603759154532941 1730564400976409682949853)
            ·
              refine ⟨648961650366153631106195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730564400976409682949853 648961650366153631106195)
              ·
                refine ⟨973442475549230446659293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648961650366153631106195 973442475549230446659293)
                ·
                  refine ⟨365040928330961417497235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973442475549230446659293 365040928330961417497235)
                  ·
                    rfl

theorem cell20_799779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_799779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799779 prefixEnd_799779 := by exact prefixLift 799779
  have htrace : WordTrace (prefixWord ++ tailWord_799779) baseStart_799779 baseEnd_799779 := by
    simpa [prefixWord, tailWord_799779, baseEnd_799779] using wordTrace_append hprefix tailTrace_799779
  have hstable : (prefixWord ++ tailWord_799779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799779).length < 2 ^ (prefixWord ++ tailWord_799779).sum := by decide
  have hdescent : baseEnd_799779 < baseStart_799779 := by decide
  rcases family_descends (prefixWord ++ tailWord_799779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799830 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_799830 : Nat := 118140960795 + 799830 * 2 ^ 59
def prefixEnd_799830 : Nat := 4983230072969 + 3 ^ 40 * 799830 * 2
def baseEnd_799830 : Nat := 365064206120631906797027

theorem tailTrace_799830 : CollatzResearch.WordTrace tailWord_799830 prefixEnd_799830 365064206120631906797027 := by
  unfold tailWord_799830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823262293272499058363809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19448131128239989955880629 1823262293272499058363809)
  ·
    refine ⟨1367446719954374293772857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1823262293272499058363809 1367446719954374293772857)
    ·
      refine ⟨1025585039965780720329643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1367446719954374293772857 1025585039965780720329643)
      ·
        refine ⟨1538377559948671080494465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025585039965780720329643 1538377559948671080494465)
        ·
          refine ⟨1153783169961503310370849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538377559948671080494465 1153783169961503310370849)
          ·
            refine ⟨865337377471127482778137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153783169961503310370849 865337377471127482778137)
            ·
              refine ⟨649003033103345612083603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865337377471127482778137 649003033103345612083603)
              ·
                refine ⟨973504549655018418125405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649003033103345612083603 973504549655018418125405)
                ·
                  refine ⟨365064206120631906797027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973504549655018418125405 365064206120631906797027)
                  ·
                    rfl

theorem cell20_799830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_799830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799830 prefixEnd_799830 := by exact prefixLift 799830
  have htrace : WordTrace (prefixWord ++ tailWord_799830) baseStart_799830 baseEnd_799830 := by
    simpa [prefixWord, tailWord_799830, baseEnd_799830] using wordTrace_append hprefix tailTrace_799830
  have hstable : (prefixWord ++ tailWord_799830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799830).length < 2 ^ (prefixWord ++ tailWord_799830).sum := by decide
  have hdescent : baseEnd_799830 < baseStart_799830 := by decide
  rcases family_descends (prefixWord ++ tailWord_799830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799876 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_799876 : Nat := 118140960795 + 799876 * 2 ^ 59
def prefixEnd_799876 : Nat := 4983230072969 + 3 ^ 40 * 799876 * 2
def baseEnd_799876 : Nat := 365085201774060191263505

theorem tailTrace_799876 : CollatzResearch.WordTrace tailWord_799876 prefixEnd_799876 365085201774060191263505 := by
  unfold tailWord_799876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14586937225096667394997741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19449249633462223193330321 14586937225096667394997741)
  ·
    refine ⟨5470101459411250273124153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14586937225096667394997741 5470101459411250273124153)
    ·
      refine ⟨4102576094558437704843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470101459411250273124153 4102576094558437704843115)
      ·
        refine ⟨6153864141837656557264673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102576094558437704843115 6153864141837656557264673)
        ·
          refine ⟨4615398106378242417948505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153864141837656557264673 4615398106378242417948505)
          ·
            refine ⟨3461548579783681813461379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615398106378242417948505 3461548579783681813461379)
            ·
              refine ⟨5192322869675522720192069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461548579783681813461379 5192322869675522720192069)
              ·
                refine ⟨973560538064160510036013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5192322869675522720192069 973560538064160510036013)
                ·
                  refine ⟨365085201774060191263505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973560538064160510036013 365085201774060191263505)
                  ·
                    rfl

theorem cell20_799876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_799876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799876 prefixEnd_799876 := by exact prefixLift 799876
  have htrace : WordTrace (prefixWord ++ tailWord_799876) baseStart_799876 baseEnd_799876 := by
    simpa [prefixWord, tailWord_799876, baseEnd_799876] using wordTrace_append hprefix tailTrace_799876
  have hstable : (prefixWord ++ tailWord_799876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799876).length < 2 ^ (prefixWord ++ tailWord_799876).sum := by decide
  have hdescent : baseEnd_799876 < baseStart_799876 := by decide
  rcases family_descends (prefixWord ++ tailWord_799876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799958 : List Nat := [5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_799958 : Nat := 118140960795 + 799958 * 2 ^ 59
def prefixEnd_799958 : Nat := 4983230072969 + 3 ^ 40 * 799958 * 2
def baseEnd_799958 : Nat := 121707542936144116843279

theorem tailTrace_799958 : CollatzResearch.WordTrace tailWord_799958 prefixEnd_799958 121707542936144116843279 := by
  unfold tailWord_799958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823554077243516424655033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19451243490597508529653685 1823554077243516424655033)
  ·
    refine ⟨1367665557932637318491275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1823554077243516424655033 1367665557932637318491275)
    ·
      refine ⟨2051498336898955977736913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367665557932637318491275 2051498336898955977736913)
      ·
        refine ⟨1538623752674216983302685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051498336898955977736913 1538623752674216983302685)
        ·
          refine ⟨576983907252831368738507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1538623752674216983302685 576983907252831368738507)
          ·
            refine ⟨865475860879247053107761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576983907252831368738507 865475860879247053107761)
            ·
              refine ⟨649106895659435289830821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865475860879247053107761 649106895659435289830821)
              ·
                refine ⟨121707542936144116843279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649106895659435289830821 121707542936144116843279)
                ·
                  rfl

theorem cell20_799958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_799958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799958 prefixEnd_799958 := by exact prefixLift 799958
  have htrace : WordTrace (prefixWord ++ tailWord_799958) baseStart_799958 baseEnd_799958 := by
    simpa [prefixWord, tailWord_799958, baseEnd_799958] using wordTrace_append hprefix tailTrace_799958
  have hstable : (prefixWord ++ tailWord_799958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799958).length < 2 ^ (prefixWord ++ tailWord_799958).sum := by decide
  have hdescent : baseEnd_799958 < baseStart_799958 := by decide
  rcases family_descends (prefixWord ++ tailWord_799958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799983 : List Nat := [1, 1, 2, 1, 8, 1, 6]
def baseStart_799983 : Nat := 118140960795 + 799983 * 2 ^ 59
def prefixEnd_799983 : Nat := 4983230072969 + 3 ^ 40 * 799983 * 2
def baseEnd_799983 : Nat := 40570448832182597188489

theorem tailTrace_799983 : CollatzResearch.WordTrace tailWord_799983 prefixEnd_799983 40570448832182597188489 := by
  unfold tailWord_799983
  simp only [CollatzResearch.WordTrace]
  refine ⟨29177777060805692064140603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19451851373870461376093735 29177777060805692064140603)
  ·
    refine ⟨43766665591208538096210905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29177777060805692064140603 43766665591208538096210905)
    ·
      refine ⟨32824999193406403572158179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43766665591208538096210905 32824999193406403572158179)
      ·
        refine ⟨49237498790109605358237269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32824999193406403572158179 49237498790109605358237269)
        ·
          refine ⟨577001938946596937791843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 49237498790109605358237269 577001938946596937791843)
          ·
            refine ⟨865502908419895406687765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577001938946596937791843 865502908419895406687765)
            ·
              refine ⟨40570448832182597188489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 865502908419895406687765 40570448832182597188489)
              ·
                rfl

theorem cell20_799983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_799983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799983 prefixEnd_799983 := by exact prefixLift 799983
  have htrace : WordTrace (prefixWord ++ tailWord_799983) baseStart_799983 baseEnd_799983 := by
    simpa [prefixWord, tailWord_799983, baseEnd_799983] using wordTrace_append hprefix tailTrace_799983
  have hstable : (prefixWord ++ tailWord_799983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799983).length < 2 ^ (prefixWord ++ tailWord_799983).sum := by decide
  have hdescent : baseEnd_799983 < baseStart_799983 := by decide
  rcases family_descends (prefixWord ++ tailWord_799983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799987 : List Nat := [1, 1, 1, 2, 2, 5, 8]
def baseStart_799987 : Nat := 118140960795 + 799987 * 2 ^ 59
def prefixEnd_799987 : Nat := 4983230072969 + 3 ^ 40 * 799987 * 2
def baseEnd_799987 : Nat := 40570651688737459840339

theorem tailTrace_799987 : CollatzResearch.WordTrace tailWord_799987 prefixEnd_799987 40570651688737459840339 := by
  unfold tailWord_799987
  simp only [CollatzResearch.WordTrace]
  refine ⟨29177922952791200747286215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19451948635194133831524143 29177922952791200747286215)
  ·
    refine ⟨43766884429186801120929323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29177922952791200747286215 43766884429186801120929323)
    ·
      refine ⟨65650326643780201681393985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43766884429186801120929323 65650326643780201681393985)
      ·
        refine ⟨49237744982835151261045489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65650326643780201681393985 49237744982835151261045489)
        ·
          refine ⟨36928308737126363445784117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49237744982835151261045489 36928308737126363445784117)
          ·
            refine ⟨3462028944105596573042261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36928308737126363445784117 3462028944105596573042261)
            ·
              refine ⟨40570651688737459840339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3462028944105596573042261 40570651688737459840339)
              ·
                rfl

theorem cell20_799987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_799987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799987 prefixEnd_799987 := by exact prefixLift 799987
  have htrace : WordTrace (prefixWord ++ tailWord_799987) baseStart_799987 baseEnd_799987 := by
    simpa [prefixWord, tailWord_799987, baseEnd_799987] using wordTrace_append hprefix tailTrace_799987
  have hstable : (prefixWord ++ tailWord_799987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799987).length < 2 ^ (prefixWord ++ tailWord_799987).sum := by decide
  have hdescent : baseEnd_799987 < baseStart_799987 := by decide
  rcases family_descends (prefixWord ++ tailWord_799987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799990 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_799990 : Nat := 118140960795 + 799990 * 2 ^ 59
def prefixEnd_799990 : Nat := 4983230072969 + 3 ^ 40 * 799990 * 2
def baseEnd_799990 : Nat := 365137234480382461463039

theorem tailTrace_799990 : CollatzResearch.WordTrace tailWord_799990 prefixEnd_799990 365137234480382461463039 := by
  unfold tailWord_799990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823627023236270766227839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19452021581186888173096949 1823627023236270766227839)
  ·
    refine ⟨2735440534854406149341759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1823627023236270766227839 2735440534854406149341759)
    ·
      refine ⟨4103160802281609224012639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735440534854406149341759 4103160802281609224012639)
      ·
        refine ⟨6154741203422413836018959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103160802281609224012639 6154741203422413836018959)
        ·
          refine ⟨9232111805133620754028439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154741203422413836018959 9232111805133620754028439)
          ·
            refine ⟨13848167707700431131042659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232111805133620754028439 13848167707700431131042659)
            ·
              refine ⟨20772251561550646696563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848167707700431131042659 20772251561550646696563989)
              ·
                refine ⟨973699291947686563901437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20772251561550646696563989 973699291947686563901437)
                ·
                  refine ⟨365137234480382461463039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973699291947686563901437 365137234480382461463039)
                  ·
                    rfl

theorem cell20_799990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_799990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_799990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_799990 prefixEnd_799990 := by exact prefixLift 799990
  have htrace : WordTrace (prefixWord ++ tailWord_799990) baseStart_799990 baseEnd_799990 := by
    simpa [prefixWord, tailWord_799990, baseEnd_799990] using wordTrace_append hprefix tailTrace_799990
  have hstable : (prefixWord ++ tailWord_799990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799990).length < 2 ^ (prefixWord ++ tailWord_799990).sum := by decide
  have hdescent : baseEnd_799990 < baseStart_799990 := by decide
  rcases family_descends (prefixWord ++ tailWord_799990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800004 : List Nat := [2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_800004 : Nat := 118140960795 + 800004 * 2 ^ 59
def prefixEnd_800004 : Nat := 4983230072969 + 3 ^ 40 * 800004 * 2
def baseEnd_800004 : Nat := 121714541487286878332105

theorem tailTrace_800004 : CollatzResearch.WordTrace tailWord_800004 prefixEnd_800004 121714541487286878332105 := by
  unfold tailWord_800004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589271496864806325327533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19452361995819741767103377 14589271496864806325327533)
  ·
    refine ⟨5470976811324302371997825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14589271496864806325327533 5470976811324302371997825)
    ·
      refine ⟨4103232608493226778998369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470976811324302371997825 4103232608493226778998369)
      ·
        refine ⟨3077424456369920084248777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103232608493226778998369 3077424456369920084248777)
        ·
          refine ⟨2308068342277440063186583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3077424456369920084248777 2308068342277440063186583)
          ·
            refine ⟨3462102513416160094779875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308068342277440063186583 3462102513416160094779875)
            ·
              refine ⟨5193153770124240142169813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462102513416160094779875 5193153770124240142169813)
              ·
                refine ⟨121714541487286878332105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5193153770124240142169813 121714541487286878332105)
                ·
                  rfl

theorem cell20_800004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_800004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800004 prefixEnd_800004 := by exact prefixLift 800004
  have htrace : WordTrace (prefixWord ++ tailWord_800004) baseStart_800004 baseEnd_800004 := by
    simpa [prefixWord, tailWord_800004, baseEnd_800004] using wordTrace_append hprefix tailTrace_800004
  have hstable : (prefixWord ++ tailWord_800004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800004).length < 2 ^ (prefixWord ++ tailWord_800004).sum := by decide
  have hdescent : baseEnd_800004 < baseStart_800004 := by decide
  rcases family_descends (prefixWord ++ tailWord_800004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800042 : List Nat := [3, 1, 4, 2, 1, 9]
def baseStart_800042 : Nat := 118140960795 + 800042 * 2 ^ 59
def prefixEnd_800042 : Nat := 4983230072969 + 3 ^ 40 * 800042 * 2
def baseEnd_800042 : Nat := 13524480322122273767759

theorem tailTrace_800042 : CollatzResearch.WordTrace tailWord_800042 prefixEnd_800042 13524480322122273767759 := by
  unfold tailWord_800042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294982241897986285134595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19453285978394630093692253 7294982241897986285134595)
  ·
    refine ⟨10942473362846979427701893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294982241897986285134595 10942473362846979427701893)
    ·
      refine ⟨2051713755533808642694105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10942473362846979427701893 2051713755533808642694105)
      ·
        refine ⟨1538785316650356482020579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051713755533808642694105 1538785316650356482020579)
        ·
          refine ⟨2308177974975534723030869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538785316650356482020579 2308177974975534723030869)
          ·
            refine ⟨13524480322122273767759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2308177974975534723030869 13524480322122273767759)
            ·
              rfl

theorem cell20_800042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 9].length) (baseStart_800042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800042 prefixEnd_800042 := by exact prefixLift 800042
  have htrace : WordTrace (prefixWord ++ tailWord_800042) baseStart_800042 baseEnd_800042 := by
    simpa [prefixWord, tailWord_800042, baseEnd_800042] using wordTrace_append hprefix tailTrace_800042
  have hstable : (prefixWord ++ tailWord_800042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800042).length < 2 ^ (prefixWord ++ tailWord_800042).sum := by decide
  have hdescent : baseEnd_800042 < baseStart_800042 := by decide
  rcases family_descends (prefixWord ++ tailWord_800042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800045 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_800045 : Nat := 118140960795 + 800045 * 2 ^ 59
def prefixEnd_800045 : Nat := 4983230072969 + 3 ^ 40 * 800045 * 2
def baseEnd_800045 : Nat := 365162337979046714629481

theorem tailTrace_800045 : CollatzResearch.WordTrace tailWord_800045 prefixEnd_800045 365162337979046714629481 := by
  unfold tailWord_800045
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180038386581076652897589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19453358924387384435265059 29180038386581076652897589)
  ·
    refine ⟨2735628598741975936209149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29180038386581076652897589 2735628598741975936209149)
    ·
      refine ⟨1025860724528240976078431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2735628598741975936209149 1025860724528240976078431)
      ·
        refine ⟨1538791086792361464117647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025860724528240976078431 1538791086792361464117647)
        ·
          refine ⟨2308186630188542196176471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538791086792361464117647 2308186630188542196176471)
          ·
            refine ⟨3462279945282813294264707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308186630188542196176471 3462279945282813294264707)
            ·
              refine ⟨5193419917924219941397061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462279945282813294264707 5193419917924219941397061)
              ·
                refine ⟨973766234610791239011949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5193419917924219941397061 973766234610791239011949)
                ·
                  refine ⟨365162337979046714629481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973766234610791239011949 365162337979046714629481)
                  ·
                    rfl

theorem cell20_800045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_800045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800045 prefixEnd_800045 := by exact prefixLift 800045
  have htrace : WordTrace (prefixWord ++ tailWord_800045) baseStart_800045 baseEnd_800045 := by
    simpa [prefixWord, tailWord_800045, baseEnd_800045] using wordTrace_append hprefix tailTrace_800045
  have hstable : (prefixWord ++ tailWord_800045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800045).length < 2 ^ (prefixWord ++ tailWord_800045).sum := by decide
  have hdescent : baseEnd_800045 < baseStart_800045 := by decide
  rcases family_descends (prefixWord ++ tailWord_800045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800056 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_800056 : Nat := 118140960795 + 800056 * 2 ^ 59
def prefixEnd_800056 : Nat := 4983230072969 + 3 ^ 40 * 800056 * 2
def baseEnd_800056 : Nat := 365167358678779565262769

theorem tailTrace_800056 : CollatzResearch.WordTrace tailWord_800056 prefixEnd_800056 365167358678779565262769 := by
  unfold tailWord_800056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14590219794770612765774011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19453626393027483687698681 14590219794770612765774011)
  ·
    refine ⟨21885329692155919148661017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14590219794770612765774011 21885329692155919148661017)
    ·
      refine ⟨16413997269116939361495763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21885329692155919148661017 16413997269116939361495763)
      ·
        refine ⟨24620995903675409042243645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16413997269116939361495763 24620995903675409042243645)
        ·
          refine ⟨9232873463878278390841367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24620995903675409042243645 9232873463878278390841367)
          ·
            refine ⟨13849310195817417586262051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232873463878278390841367 13849310195817417586262051)
            ·
              refine ⟨20773965293726126379393077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849310195817417586262051 20773965293726126379393077)
              ·
                refine ⟨1947559246286824348068101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20773965293726126379393077 1947559246286824348068101)
                ·
                  refine ⟨365167358678779565262769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947559246286824348068101 365167358678779565262769)
                  ·
                    rfl

theorem cell20_800056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_800056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800056 prefixEnd_800056 := by exact prefixLift 800056
  have htrace : WordTrace (prefixWord ++ tailWord_800056) baseStart_800056 baseEnd_800056 := by
    simpa [prefixWord, tailWord_800056, baseEnd_800056] using wordTrace_append hprefix tailTrace_800056
  have hstable : (prefixWord ++ tailWord_800056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800056).length < 2 ^ (prefixWord ++ tailWord_800056).sum := by decide
  have hdescent : baseEnd_800056 < baseStart_800056 := by decide
  rcases family_descends (prefixWord ++ tailWord_800056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800080 : List Nat := [2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_800080 : Nat := 118140960795 + 800080 * 2 ^ 59
def prefixEnd_800080 : Nat := 4983230072969 + 3 ^ 40 * 800080 * 2
def baseEnd_800080 : Nat := 121726104310914049487557

theorem tailTrace_800080 : CollatzResearch.WordTrace tailWord_800080 prefixEnd_800080 121726104310914049487557 := by
  unfold tailWord_800080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14590657470727138815210847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19454209960969518420281129 14590657470727138815210847)
  ·
    refine ⟨21885986206090708222816271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14590657470727138815210847 21885986206090708222816271)
    ·
      refine ⟨32828979309136062334224407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885986206090708222816271 32828979309136062334224407)
      ·
        refine ⟨49243468963704093501336611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32828979309136062334224407 49243468963704093501336611)
        ·
          refine ⟨73865203445556140252004917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49243468963704093501336611 73865203445556140252004917)
          ·
            refine ⟨6924862823020888148625461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73865203445556140252004917 6924862823020888148625461)
            ·
              refine ⟨649205889658208263933637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6924862823020888148625461 649205889658208263933637)
              ·
                refine ⟨121726104310914049487557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649205889658208263933637 121726104310914049487557)
                ·
                  rfl

theorem cell20_800080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_800080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800080 prefixEnd_800080 := by exact prefixLift 800080
  have htrace : WordTrace (prefixWord ++ tailWord_800080) baseStart_800080 baseEnd_800080 := by
    simpa [prefixWord, tailWord_800080, baseEnd_800080] using wordTrace_append hprefix tailTrace_800080
  have hstable : (prefixWord ++ tailWord_800080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800080).length < 2 ^ (prefixWord ++ tailWord_800080).sum := by decide
  have hdescent : baseEnd_800080 < baseStart_800080 := by decide
  rcases family_descends (prefixWord ++ tailWord_800080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800101 : List Nat := [1, 3, 1, 3, 1, 2, 9]
def baseStart_800101 : Nat := 118140960795 + 800101 * 2 ^ 59
def prefixEnd_800101 : Nat := 4983230072969 + 3 ^ 40 * 800101 * 2
def baseEnd_800101 : Nat := 40576433100551045418065

theorem tailTrace_800101 : CollatzResearch.WordTrace tailWord_800101 prefixEnd_800101 40576433100551045418065 := by
  unfold tailWord_800101
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182080874378198216936157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19454720582918798811290771 29182080874378198216936157)
  ·
    refine ⟨10943280327891824331351059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29182080874378198216936157 10943280327891824331351059)
    ·
      refine ⟨16414920491837736497026589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10943280327891824331351059 16414920491837736497026589)
      ·
        refine ⟨6155595184439151186384971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16414920491837736497026589 6155595184439151186384971)
        ·
          refine ⟨9233392776658726779577457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155595184439151186384971 9233392776658726779577457)
          ·
            refine ⟨6925044582494045084683093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9233392776658726779577457 6925044582494045084683093)
            ·
              refine ⟨40576433100551045418065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6925044582494045084683093 40576433100551045418065)
              ·
                rfl

theorem cell20_800101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_800101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800101 prefixEnd_800101 := by exact prefixLift 800101
  have htrace : WordTrace (prefixWord ++ tailWord_800101) baseStart_800101 baseEnd_800101 := by
    simpa [prefixWord, tailWord_800101, baseEnd_800101] using wordTrace_append hprefix tailTrace_800101
  have hstable : (prefixWord ++ tailWord_800101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800101).length < 2 ^ (prefixWord ++ tailWord_800101).sum := by decide
  have hdescent : baseEnd_800101 < baseStart_800101 := by decide
  rcases family_descends (prefixWord ++ tailWord_800101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800104 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_800104 : Nat := 118140960795 + 800104 * 2 ^ 59
def prefixEnd_800104 : Nat := 4983230072969 + 3 ^ 40 * 800104 * 2
def baseEnd_800104 : Nat := 365189267186704731662573

theorem tailTrace_800104 : CollatzResearch.WordTrace tailWord_800104 prefixEnd_800104 365189267186704731662573 := by
  unfold tailWord_800104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591095146683664864647683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19454793528911553152863577 14591095146683664864647683)
  ·
    refine ⟨21886642720025497296971525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14591095146683664864647683 21886642720025497296971525)
    ·
      refine ⟨4103745510004780743182161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21886642720025497296971525 4103745510004780743182161)
      ·
        refine ⟨3077809132503585557386621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103745510004780743182161 3077809132503585557386621)
        ·
          refine ⟨1154178424688844584019983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3077809132503585557386621 1154178424688844584019983)
          ·
            refine ⟨1731267637033266876029975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154178424688844584019983 1731267637033266876029975)
            ·
              refine ⟨2596901455549900314044963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731267637033266876029975 2596901455549900314044963)
              ·
                refine ⟨3895352183324850471067445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596901455549900314044963 3895352183324850471067445)
                ·
                  refine ⟨365189267186704731662573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3895352183324850471067445 365189267186704731662573)
                  ·
                    rfl

theorem cell20_800104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_800104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800104 prefixEnd_800104 := by exact prefixLift 800104
  have htrace : WordTrace (prefixWord ++ tailWord_800104) baseStart_800104 baseEnd_800104 := by
    simpa [prefixWord, tailWord_800104, baseEnd_800104] using wordTrace_append hprefix tailTrace_800104
  have hstable : (prefixWord ++ tailWord_800104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800104).length < 2 ^ (prefixWord ++ tailWord_800104).sum := by decide
  have hdescent : baseEnd_800104 < baseStart_800104 := by decide
  rcases family_descends (prefixWord ++ tailWord_800104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800111 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 2]
def baseStart_800111 : Nat := 118140960795 + 800111 * 2 ^ 59
def prefixEnd_800111 : Nat := 4983230072969 + 3 ^ 40 * 800111 * 2
def baseEnd_800111 : Nat := 365192462177443818429211

theorem tailTrace_800111 : CollatzResearch.WordTrace tailWord_800111 prefixEnd_800111 365192462177443818429211 := by
  unfold tailWord_800111
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182445604341969924800187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19454963736227979949866791 29182445604341969924800187)
  ·
    refine ⟨43773668406512954887200281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29182445604341969924800187 43773668406512954887200281)
    ·
      refine ⟨32830251304884716165400211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43773668406512954887200281 32830251304884716165400211)
      ·
        refine ⟨49245376957327074248100317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32830251304884716165400211 49245376957327074248100317)
        ·
          refine ⟨18467016358997652843037619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49245376957327074248100317 18467016358997652843037619)
          ·
            refine ⟨27700524538496479264556429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18467016358997652843037619 27700524538496479264556429)
            ·
              refine ⟨10387696701936179724208661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27700524538496479264556429 10387696701936179724208661)
              ·
                refine ⟨486923282903258424572281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10387696701936179724208661 486923282903258424572281)
                ·
                  refine ⟨365192462177443818429211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486923282903258424572281 365192462177443818429211)
                  ·
                    rfl

theorem cell20_800111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2].length) (baseStart_800111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800111 prefixEnd_800111 := by exact prefixLift 800111
  have htrace : WordTrace (prefixWord ++ tailWord_800111) baseStart_800111 baseEnd_800111 := by
    simpa [prefixWord, tailWord_800111, baseEnd_800111] using wordTrace_append hprefix tailTrace_800111
  have hstable : (prefixWord ++ tailWord_800111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800111).length < 2 ^ (prefixWord ++ tailWord_800111).sum := by decide
  have hdescent : baseEnd_800111 < baseStart_800111 := by decide
  rcases family_descends (prefixWord ++ tailWord_800111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800135 : List Nat := [1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_800135 : Nat := 118140960795 + 800135 * 2 ^ 59
def prefixEnd_800135 : Nat := 4983230072969 + 3 ^ 40 * 800135 * 2
def baseEnd_800135 : Nat := 121734472143802133876371

theorem tailTrace_800135 : CollatzResearch.WordTrace tailWord_800135 prefixEnd_800135 121734472143802133876371 := by
  unfold tailWord_800135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183320956255022023673859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455547304170014682449239 29183320956255022023673859)
  ·
    refine ⟨43774981434382533035510789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29183320956255022023673859 43774981434382533035510789)
    ·
      refine ⟨8207809018946724944158273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43774981434382533035510789 8207809018946724944158273)
      ·
        refine ⟨6155856764210043708118705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8207809018946724944158273 6155856764210043708118705)
        ·
          refine ⟨4616892573157532781089029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155856764210043708118705 4616892573157532781089029)
          ·
            refine ⟨865667357467037396454193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4616892573157532781089029 865667357467037396454193)
            ·
              refine ⟨649250518100278047340645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865667357467037396454193 649250518100278047340645)
              ·
                refine ⟨121734472143802133876371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649250518100278047340645 121734472143802133876371)
                ·
                  rfl

theorem cell20_800135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_800135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800135 prefixEnd_800135 := by exact prefixLift 800135
  have htrace : WordTrace (prefixWord ++ tailWord_800135) baseStart_800135 baseEnd_800135 := by
    simpa [prefixWord, tailWord_800135, baseEnd_800135] using wordTrace_append hprefix tailTrace_800135
  have hstable : (prefixWord ++ tailWord_800135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800135).length < 2 ^ (prefixWord ++ tailWord_800135).sum := by decide
  have hdescent : baseEnd_800135 < baseStart_800135 := by decide
  rcases family_descends (prefixWord ++ tailWord_800135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800139 : List Nat := [1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_800139 : Nat := 118140960795 + 800139 * 2 ^ 59
def prefixEnd_800139 : Nat := 4983230072969 + 3 ^ 40 * 800139 * 2
def baseEnd_800139 : Nat := 121735080713466721831921

theorem tailTrace_800139 : CollatzResearch.WordTrace tailWord_800139 prefixEnd_800139 121735080713466721831921 := by
  unfold tailWord_800139
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183466848240530706819471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455644565493687137879647 29183466848240530706819471)
  ·
    refine ⟨43775200272360796060229207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29183466848240530706819471 43775200272360796060229207)
    ·
      refine ⟨65662800408541194090343811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43775200272360796060229207 65662800408541194090343811)
      ·
        refine ⟨98494200612811791135515717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65662800408541194090343811 98494200612811791135515717)
        ·
          refine ⟨18467662614902210837909197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98494200612811791135515717 18467662614902210837909197)
          ·
            refine ⟨6925373480588329064215949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18467662614902210837909197 6925373480588329064215949)
            ·
              refine ⟨2597015055220623399080981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6925373480588329064215949 2597015055220623399080981)
              ·
                refine ⟨121735080713466721831921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2597015055220623399080981 121735080713466721831921)
                ·
                  rfl

theorem cell20_800139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_800139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800139 prefixEnd_800139 := by exact prefixLift 800139
  have htrace : WordTrace (prefixWord ++ tailWord_800139) baseStart_800139 baseEnd_800139 := by
    simpa [prefixWord, tailWord_800139, baseEnd_800139] using wordTrace_append hprefix tailTrace_800139
  have hstable : (prefixWord ++ tailWord_800139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800139).length < 2 ^ (prefixWord ++ tailWord_800139).sum := by decide
  have hdescent : baseEnd_800139 < baseStart_800139 := by decide
  rcases family_descends (prefixWord ++ tailWord_800139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800163 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_800163 : Nat := 118140960795 + 800163 * 2 ^ 59
def prefixEnd_800163 : Nat := 4983230072969 + 3 ^ 40 * 800163 * 2
def baseEnd_800163 : Nat := 365216196394362748695665

theorem tailTrace_800163 : CollatzResearch.WordTrace tailWord_800163 prefixEnd_800163 365216196394362748695665 := by
  unfold tailWord_800163
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184342200153582805693143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19456228133435721870462095 29184342200153582805693143)
  ·
    refine ⟨43776513300230374208539715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29184342200153582805693143 43776513300230374208539715)
    ·
      refine ⟨65664769950345561312809573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43776513300230374208539715 65664769950345561312809573)
      ·
        refine ⟨12312144365689792746151795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65664769950345561312809573 12312144365689792746151795)
        ·
          refine ⟨18468216548534689119227693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12312144365689792746151795 18468216548534689119227693)
          ·
            refine ⟨6925581205700508419710385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18468216548534689119227693 6925581205700508419710385)
            ·
              refine ⟨5194185904275381314782789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925581205700508419710385 5194185904275381314782789)
              ·
                refine ⟨973909857051633996521773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5194185904275381314782789 973909857051633996521773)
                ·
                  refine ⟨365216196394362748695665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973909857051633996521773 365216196394362748695665)
                  ·
                    rfl

theorem cell20_800163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_800163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800163 prefixEnd_800163 := by exact prefixLift 800163
  have htrace : WordTrace (prefixWord ++ tailWord_800163) baseStart_800163 baseEnd_800163 := by
    simpa [prefixWord, tailWord_800163, baseEnd_800163] using wordTrace_append hprefix tailTrace_800163
  have hstable : (prefixWord ++ tailWord_800163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800163).length < 2 ^ (prefixWord ++ tailWord_800163).sum := by decide
  have hdescent : baseEnd_800163 < baseStart_800163 := by decide
  rcases family_descends (prefixWord ++ tailWord_800163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800173 : List Nat := [1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_800173 : Nat := 118140960795 + 800173 * 2 ^ 59
def prefixEnd_800173 : Nat := 4983230072969 + 3 ^ 40 * 800173 * 2
def baseEnd_800173 : Nat := 121740253555615719454097

theorem tailTrace_800173 : CollatzResearch.WordTrace tailWord_800173 prefixEnd_800173 121740253555615719454097 := by
  unfold tailWord_800173
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184706930117354513557173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19456471286744903009038115 29184706930117354513557173)
  ·
    refine ⟨2736066274698501985645985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29184706930117354513557173 2736066274698501985645985)
    ·
      refine ⟨2052049706023876489234489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2736066274698501985645985 2052049706023876489234489)
      ·
        refine ⟨1539037279517907366925867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2052049706023876489234489 1539037279517907366925867)
        ·
          refine ⟨2308555919276861050388801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539037279517907366925867 2308555919276861050388801)
          ·
            refine ⟨1731416939457645787791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308555919276861050388801 1731416939457645787791601)
            ·
              refine ⟨1298562704593234340843701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731416939457645787791601 1298562704593234340843701)
              ·
                refine ⟨121740253555615719454097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298562704593234340843701 121740253555615719454097)
                ·
                  rfl

theorem cell20_800173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_800173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800173 prefixEnd_800173 := by exact prefixLift 800173
  have htrace : WordTrace (prefixWord ++ tailWord_800173) baseStart_800173 baseEnd_800173 := by
    simpa [prefixWord, tailWord_800173, baseEnd_800173] using wordTrace_append hprefix tailTrace_800173
  have hstable : (prefixWord ++ tailWord_800173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800173).length < 2 ^ (prefixWord ++ tailWord_800173).sum := by decide
  have hdescent : baseEnd_800173 < baseStart_800173 := by decide
  rcases family_descends (prefixWord ++ tailWord_800173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800218 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_800218 : Nat := 118140960795 + 800218 * 2 ^ 59
def prefixEnd_800218 : Nat := 4983230072969 + 3 ^ 40 * 800218 * 2
def baseEnd_800218 : Nat := 365241299893027001862107

theorem tailTrace_800218 : CollatzResearch.WordTrace tailWord_800218 prefixEnd_800218 365241299893027001862107 := by
  unfold tailWord_800218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296587053738581799736327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19457565476636218132630205 7296587053738581799736327)
  ·
    refine ⟨10944880580607872699604491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296587053738581799736327 10944880580607872699604491)
    ·
      refine ⟨16417320870911809049406737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10944880580607872699604491 16417320870911809049406737)
      ·
        refine ⟨12312990653183856787055053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16417320870911809049406737 12312990653183856787055053)
        ·
          refine ⟨4617371494943946295145645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12312990653183856787055053 4617371494943946295145645)
          ·
            refine ⟨1731514310603979860679617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4617371494943946295145645 1731514310603979860679617)
            ·
              refine ⟨1298635732952984895509713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731514310603979860679617 1298635732952984895509713)
              ·
                refine ⟨973976799714738671632285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298635732952984895509713 973976799714738671632285)
                ·
                  refine ⟨365241299893027001862107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973976799714738671632285 365241299893027001862107)
                  ·
                    rfl

theorem cell20_800218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_800218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800218 prefixEnd_800218 := by exact prefixLift 800218
  have htrace : WordTrace (prefixWord ++ tailWord_800218) baseStart_800218 baseEnd_800218 := by
    simpa [prefixWord, tailWord_800218, baseEnd_800218] using wordTrace_append hprefix tailTrace_800218
  have hstable : (prefixWord ++ tailWord_800218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800218).length < 2 ^ (prefixWord ++ tailWord_800218).sum := by decide
  have hdescent : baseEnd_800218 < baseStart_800218 := by decide
  rcases family_descends (prefixWord ++ tailWord_800218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800221 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 2]
def baseStart_800221 : Nat := 118140960795 + 800221 * 2 ^ 59
def prefixEnd_800221 : Nat := 4983230072969 + 3 ^ 40 * 800221 * 2
def baseEnd_800221 : Nat := 365242669174772324762095

theorem tailTrace_800221 : CollatzResearch.WordTrace tailWord_800221 prefixEnd_800221 365242669174772324762095 := by
  unfold tailWord_800221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186457633943458711304517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19457638422628972474203011 29186457633943458711304517)
  ·
    refine ⟨5472460806364398508369597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29186457633943458711304517 5472460806364398508369597)
    ·
      refine ⟨2052172802386649440638599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5472460806364398508369597 2052172802386649440638599)
      ·
        refine ⟨3078259203579974160957899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052172802386649440638599 3078259203579974160957899)
        ·
          refine ⟨4617388805369961241436849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078259203579974160957899 4617388805369961241436849)
          ·
            refine ⟨3463041604027470931077637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617388805369961241436849 3463041604027470931077637)
            ·
              refine ⟨649320300755150799577057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3463041604027470931077637 649320300755150799577057)
              ·
                refine ⟨486990225566363099682793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649320300755150799577057 486990225566363099682793)
                ·
                  refine ⟨365242669174772324762095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486990225566363099682793 365242669174772324762095)
                  ·
                    rfl

theorem cell20_800221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_800221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800221 prefixEnd_800221 := by exact prefixLift 800221
  have htrace : WordTrace (prefixWord ++ tailWord_800221) baseStart_800221 baseEnd_800221 := by
    simpa [prefixWord, tailWord_800221, baseEnd_800221] using wordTrace_append hprefix tailTrace_800221
  have hstable : (prefixWord ++ tailWord_800221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800221).length < 2 ^ (prefixWord ++ tailWord_800221).sum := by decide
  have hdescent : baseEnd_800221 < baseStart_800221 := by decide
  rcases family_descends (prefixWord ++ tailWord_800221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800239 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_800239 : Nat := 118140960795 + 800239 * 2 ^ 59
def prefixEnd_800239 : Nat := 4983230072969 + 3 ^ 40 * 800239 * 2
def baseEnd_800239 : Nat := 365250884865244262162021

theorem tailTrace_800239 : CollatzResearch.WordTrace tailWord_800239 prefixEnd_800239 365250884865244262162021 := by
  unfold tailWord_800239
  simp only [CollatzResearch.WordTrace]
  refine ⟨29187114147878247785459771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19458076098585498523639847 29187114147878247785459771)
  ·
    refine ⟨43780671221817371678189657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29187114147878247785459771 43780671221817371678189657)
    ·
      refine ⟨32835503416363028758642243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43780671221817371678189657 32835503416363028758642243)
      ·
        refine ⟨49253255124544543137963365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32835503416363028758642243 49253255124544543137963365)
        ·
          refine ⟨9234985335852101838368131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49253255124544543137963365 9234985335852101838368131)
          ·
            refine ⟨13852478003778152757552197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9234985335852101838368131 13852478003778152757552197)
            ·
              refine ⟨2597339625708403642041037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13852478003778152757552197 2597339625708403642041037)
              ·
                refine ⟨974002359640651365765389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2597339625708403642041037 974002359640651365765389)
                ·
                  refine ⟨365250884865244262162021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974002359640651365765389 365250884865244262162021)
                  ·
                    rfl

theorem cell20_800239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_800239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800239 prefixEnd_800239 := by exact prefixLift 800239
  have htrace : WordTrace (prefixWord ++ tailWord_800239) baseStart_800239 baseEnd_800239 := by
    simpa [prefixWord, tailWord_800239, baseEnd_800239] using wordTrace_append hprefix tailTrace_800239
  have hstable : (prefixWord ++ tailWord_800239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800239).length < 2 ^ (prefixWord ++ tailWord_800239).sum := by decide
  have hdescent : baseEnd_800239 < baseStart_800239 := by decide
  rcases family_descends (prefixWord ++ tailWord_800239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800269 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_800269 : Nat := 118140960795 + 800269 * 2 ^ 59
def prefixEnd_800269 : Nat := 4983230072969 + 3 ^ 40 * 800269 * 2
def baseEnd_800269 : Nat := 365264577682697491161899

theorem tailTrace_800269 : CollatzResearch.WordTrace tailWord_800269 prefixEnd_800269 365264577682697491161899 := by
  unfold tailWord_800269
  simp only [CollatzResearch.WordTrace]
  refine ⟨29188208337769562909051861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19458805558513041939367907 29188208337769562909051861)
  ·
    refine ⟨684098632916474130680903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29188208337769562909051861 684098632916474130680903)
    ·
      refine ⟨1026147949374711196021355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684098632916474130680903 1026147949374711196021355)
      ·
        refine ⟨1539221924062066794032033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026147949374711196021355 1539221924062066794032033)
        ·
          refine ⟨1154416443046550095524025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539221924062066794032033 1154416443046550095524025)
          ·
            refine ⟨865812332284912571643019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154416443046550095524025 865812332284912571643019)
            ·
              refine ⟨1298718498427368857464529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865812332284912571643019 1298718498427368857464529)
              ·
                refine ⟨974038873820526643098397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298718498427368857464529 974038873820526643098397)
                ·
                  refine ⟨365264577682697491161899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974038873820526643098397 365264577682697491161899)
                  ·
                    rfl

theorem cell20_800269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_800269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800269 prefixEnd_800269 := by exact prefixLift 800269
  have htrace : WordTrace (prefixWord ++ tailWord_800269) baseStart_800269 baseEnd_800269 := by
    simpa [prefixWord, tailWord_800269, baseEnd_800269] using wordTrace_append hprefix tailTrace_800269
  have hstable : (prefixWord ++ tailWord_800269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800269).length < 2 ^ (prefixWord ++ tailWord_800269).sum := by decide
  have hdescent : baseEnd_800269 < baseStart_800269 := by decide
  rcases family_descends (prefixWord ++ tailWord_800269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800270 : List Nat := [4, 1, 1, 2, 4, 1, 7]
def baseStart_800270 : Nat := 118140960795 + 800270 * 2 ^ 59
def prefixEnd_800270 : Nat := 4983230072969 + 3 ^ 40 * 800270 * 2
def baseEnd_800270 : Nat := 40585003789993992458729

theorem tailTrace_800270 : CollatzResearch.WordTrace tailWord_800270 prefixEnd_800270 40585003789993992458729 := by
  unfold tailWord_800270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648530601345742509979783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19458829873843960053225509 3648530601345742509979783)
  ·
    refine ⟨5472795902018613764969675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648530601345742509979783 5472795902018613764969675)
    ·
      refine ⟨8209193853027920647454513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472795902018613764969675 8209193853027920647454513)
      ·
        refine ⟨6156895389770940485590885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8209193853027920647454513 6156895389770940485590885)
        ·
          refine ⟨1154417885582051341048291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6156895389770940485590885 1154417885582051341048291)
          ·
            refine ⟨1731626828373077011572437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154417885582051341048291 1731626828373077011572437)
            ·
              refine ⟨40585003789993992458729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1731626828373077011572437 40585003789993992458729)
              ·
                rfl

theorem cell20_800270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_800270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800270 prefixEnd_800270 := by exact prefixLift 800270
  have htrace : WordTrace (prefixWord ++ tailWord_800270) baseStart_800270 baseEnd_800270 := by
    simpa [prefixWord, tailWord_800270, baseEnd_800270] using wordTrace_append hprefix tailTrace_800270
  have hstable : (prefixWord ++ tailWord_800270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800270).length < 2 ^ (prefixWord ++ tailWord_800270).sum := by decide
  have hdescent : baseEnd_800270 < baseStart_800270 := by decide
  rcases family_descends (prefixWord ++ tailWord_800270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800277 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_800277 : Nat := 118140960795 + 800277 * 2 ^ 59
def prefixEnd_800277 : Nat := 4983230072969 + 3 ^ 40 * 800277 * 2
def baseEnd_800277 : Nat := 365268229100685018895199

theorem tailTrace_800277 : CollatzResearch.WordTrace tailWord_800277 prefixEnd_800277 365268229100685018895199 := by
  unfold tailWord_800277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29188500121740580275343085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19459000081160386850228723 29188500121740580275343085)
  ·
    refine ⟨10945687545652717603253657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29188500121740580275343085 10945687545652717603253657)
    ·
      refine ⟨8209265659239538202440243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10945687545652717603253657 8209265659239538202440243)
      ·
        refine ⟨12313898488859307303660365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209265659239538202440243 12313898488859307303660365)
        ·
          refine ⟨4617711933322240238872637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12313898488859307303660365 4617711933322240238872637)
          ·
            refine ⟨1731641974995840089577239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4617711933322240238872637 1731641974995840089577239)
            ·
              refine ⟨2597462962493760134365859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731641974995840089577239 2597462962493760134365859)
              ·
                refine ⟨3896194443740640201548789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597462962493760134365859 3896194443740640201548789)
                ·
                  refine ⟨365268229100685018895199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896194443740640201548789 365268229100685018895199)
                  ·
                    rfl

theorem cell20_800277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_800277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800277 prefixEnd_800277 := by exact prefixLift 800277
  have htrace : WordTrace (prefixWord ++ tailWord_800277) baseStart_800277 baseEnd_800277 := by
    simpa [prefixWord, tailWord_800277, baseEnd_800277] using wordTrace_append hprefix tailTrace_800277
  have hstable : (prefixWord ++ tailWord_800277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800277).length < 2 ^ (prefixWord ++ tailWord_800277).sum := by decide
  have hdescent : baseEnd_800277 < baseStart_800277 := by decide
  rcases family_descends (prefixWord ++ tailWord_800277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800286 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_800286 : Nat := 118140960795 + 800286 * 2 ^ 59
def prefixEnd_800286 : Nat := 4983230072969 + 3 ^ 40 * 800286 * 2
def baseEnd_800286 : Nat := 365272336945920987595163

theorem tailTrace_800286 : CollatzResearch.WordTrace tailWord_800286 prefixEnd_800286 365272336945920987595163 := by
  unfold tailWord_800286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648603547338496851552589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19459218919138649874947141 3648603547338496851552589)
  ·
    refine ⟨1368226330251936319332221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3648603547338496851552589 1368226330251936319332221)
    ·
      refine ⟨513084873844476119749583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1368226330251936319332221 513084873844476119749583)
      ·
        refine ⟨769627310766714179624375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513084873844476119749583 769627310766714179624375)
        ·
          refine ⟨1154440966150071269436563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769627310766714179624375 1154440966150071269436563)
          ·
            refine ⟨1731661449225106904154845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154440966150071269436563 1731661449225106904154845)
            ·
              refine ⟨649373043459415089058067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731661449225106904154845 649373043459415089058067)
              ·
                refine ⟨974059565189122633587101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649373043459415089058067 974059565189122633587101)
                ·
                  refine ⟨365272336945920987595163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974059565189122633587101 365272336945920987595163)
                  ·
                    rfl

theorem cell20_800286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_800286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800286 prefixEnd_800286 := by exact prefixLift 800286
  have htrace : WordTrace (prefixWord ++ tailWord_800286) baseStart_800286 baseEnd_800286 := by
    simpa [prefixWord, tailWord_800286, baseEnd_800286] using wordTrace_append hprefix tailTrace_800286
  have hstable : (prefixWord ++ tailWord_800286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800286).length < 2 ^ (prefixWord ++ tailWord_800286).sum := by decide
  have hdescent : baseEnd_800286 < baseStart_800286 := by decide
  rcases family_descends (prefixWord ++ tailWord_800286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800336 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_800336 : Nat := 118140960795 + 800336 * 2 ^ 59
def prefixEnd_800336 : Nat := 4983230072969 + 3 ^ 40 * 800336 * 2
def baseEnd_800336 : Nat := 365295158308343035928291

theorem tailTrace_800336 : CollatzResearch.WordTrace tailWord_800336 prefixEnd_800336 365295158308343035928291 := by
  unfold tailWord_800336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595326014263416675870431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19460434685684555567827241 14595326014263416675870431)
  ·
    refine ⟨21892989021395125013805647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14595326014263416675870431 21892989021395125013805647)
    ·
      refine ⟨32839483532092687520708471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21892989021395125013805647 32839483532092687520708471)
      ·
        refine ⟨49259225298139031281062707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32839483532092687520708471 49259225298139031281062707)
        ·
          refine ⟨73888837947208546921594061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49259225298139031281062707 73888837947208546921594061)
          ·
            refine ⟨27708314230203205095597773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73888837947208546921594061 27708314230203205095597773)
            ·
              refine ⟨10390617836326201910849165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27708314230203205095597773 10390617836326201910849165)
              ·
                refine ⟨3896481688622325716568437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10390617836326201910849165 3896481688622325716568437)
                ·
                  refine ⟨365295158308343035928291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896481688622325716568437 365295158308343035928291)
                  ·
                    rfl

theorem cell20_800336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_800336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800336 prefixEnd_800336 := by exact prefixLift 800336
  have htrace : WordTrace (prefixWord ++ tailWord_800336) baseStart_800336 baseEnd_800336 := by
    simpa [prefixWord, tailWord_800336, baseEnd_800336] using wordTrace_append hprefix tailTrace_800336
  have hstable : (prefixWord ++ tailWord_800336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800336).length < 2 ^ (prefixWord ++ tailWord_800336).sum := by decide
  have hdescent : baseEnd_800336 < baseStart_800336 := by decide
  rcases family_descends (prefixWord ++ tailWord_800336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800353 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_800353 : Nat := 118140960795 + 800353 * 2 ^ 59
def prefixEnd_800353 : Nat := 4983230072969 + 3 ^ 40 * 800353 * 2
def baseEnd_800353 : Nat := 365302917571566532361555

theorem tailTrace_800353 : CollatzResearch.WordTrace tailWord_800353 prefixEnd_800353 365302917571566532361555 := by
  unfold tailWord_800353
  simp only [CollatzResearch.WordTrace]
  refine ⟨29191272069465245255109713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19460848046310163503406475 29191272069465245255109713)
  ·
    refine ⟨21893454052098933941332285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29191272069465245255109713 21893454052098933941332285)
    ·
      refine ⟨8210045269537100227999607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21893454052098933941332285 8210045269537100227999607)
      ·
        refine ⟨12315067904305650341999411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210045269537100227999607 12315067904305650341999411)
        ·
          refine ⟨18472601856458475512999117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315067904305650341999411 18472601856458475512999117)
          ·
            refine ⟨6927225696171928317374669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18472601856458475512999117 6927225696171928317374669)
            ·
              refine ⟨2597709636064473119015501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6927225696171928317374669 2597709636064473119015501)
              ·
                refine ⟨974141113524177419630813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2597709636064473119015501 974141113524177419630813)
                ·
                  refine ⟨365302917571566532361555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974141113524177419630813 365302917571566532361555)
                  ·
                    rfl

theorem cell20_800353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_800353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800353 prefixEnd_800353 := by exact prefixLift 800353
  have htrace : WordTrace (prefixWord ++ tailWord_800353) baseStart_800353 baseEnd_800353 := by
    simpa [prefixWord, tailWord_800353, baseEnd_800353] using wordTrace_append hprefix tailTrace_800353
  have hstable : (prefixWord ++ tailWord_800353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800353).length < 2 ^ (prefixWord ++ tailWord_800353).sum := by decide
  have hdescent : baseEnd_800353 < baseStart_800353 := by decide
  rcases family_descends (prefixWord ++ tailWord_800353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800377 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 2]
def baseStart_800377 : Nat := 118140960795 + 800377 * 2 ^ 59
def prefixEnd_800377 : Nat := 4983230072969 + 3 ^ 40 * 800377 * 2
def baseEnd_800377 : Nat := 365313871825529115561457

theorem tailTrace_800377 : CollatzResearch.WordTrace tailWord_800377 prefixEnd_800377 365313871825529115561457 := by
  unfold tailWord_800377
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192147421378297353983385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19461431614252198235988923 29192147421378297353983385)
  ·
    refine ⟨21894110566033723015487539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29192147421378297353983385 21894110566033723015487539)
    ·
      refine ⟨32841165849050584523231309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894110566033723015487539 32841165849050584523231309)
      ·
        refine ⟨12315437193393969196211741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32841165849050584523231309 12315437193393969196211741)
        ·
          refine ⟨4618288947522738448579403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12315437193393969196211741 4618288947522738448579403)
          ·
            refine ⟨6927433421284107672869105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618288947522738448579403 6927433421284107672869105)
            ·
              refine ⟨5195575065963080754651829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927433421284107672869105 5195575065963080754651829)
              ·
                refine ⟨487085162434038820748609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5195575065963080754651829 487085162434038820748609)
                ·
                  refine ⟨365313871825529115561457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487085162434038820748609 365313871825529115561457)
                  ·
                    rfl

theorem cell20_800377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_800377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800377 prefixEnd_800377 := by exact prefixLift 800377
  have htrace : WordTrace (prefixWord ++ tailWord_800377) baseStart_800377 baseEnd_800377 := by
    simpa [prefixWord, tailWord_800377, baseEnd_800377] using wordTrace_append hprefix tailTrace_800377
  have hstable : (prefixWord ++ tailWord_800377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800377).length < 2 ^ (prefixWord ++ tailWord_800377).sum := by decide
  have hdescent : baseEnd_800377 < baseStart_800377 := by decide
  rcases family_descends (prefixWord ++ tailWord_800377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800391 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_800391 : Nat := 118140960795 + 800391 * 2 ^ 59
def prefixEnd_800391 : Nat := 4983230072969 + 3 ^ 40 * 800391 * 2
def baseEnd_800391 : Nat := 365320261807007289094733

theorem tailTrace_800391 : CollatzResearch.WordTrace tailWord_800391 prefixEnd_800391 365320261807007289094733 := by
  unfold tailWord_800391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192658043327577744993027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19461772028885051829995351 29192658043327577744993027)
  ·
    refine ⟨43788987064991366617489541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29192658043327577744993027 43788987064991366617489541)
    ·
      refine ⟨8210435074685881240779289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43788987064991366617489541 8210435074685881240779289)
      ·
        refine ⟨6157826306014410930584467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8210435074685881240779289 6157826306014410930584467)
        ·
          refine ⟨9236739459021616395876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157826306014410930584467 9236739459021616395876701)
          ·
            refine ⟨3463777297133106148453763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9236739459021616395876701 3463777297133106148453763)
            ·
              refine ⟨5195665945699659222680645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463777297133106148453763 5195665945699659222680645)
              ·
                refine ⟨974187364818686104252621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5195665945699659222680645 974187364818686104252621)
                ·
                  refine ⟨365320261807007289094733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974187364818686104252621 365320261807007289094733)
                  ·
                    rfl

theorem cell20_800391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_800391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800391 prefixEnd_800391 := by exact prefixLift 800391
  have htrace : WordTrace (prefixWord ++ tailWord_800391) baseStart_800391 baseEnd_800391 := by
    simpa [prefixWord, tailWord_800391, baseEnd_800391] using wordTrace_append hprefix tailTrace_800391
  have hstable : (prefixWord ++ tailWord_800391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800391).length < 2 ^ (prefixWord ++ tailWord_800391).sum := by decide
  have hdescent : baseEnd_800391 < baseStart_800391 := by decide
  rcases family_descends (prefixWord ++ tailWord_800391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800394 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_800394 : Nat := 118140960795 + 800394 * 2 ^ 59
def prefixEnd_800394 : Nat := 4983230072969 + 3 ^ 40 * 800394 * 2
def baseEnd_800394 : Nat := 365321631088752611994721

theorem tailTrace_800394 : CollatzResearch.WordTrace tailWord_800394 prefixEnd_800394 365321631088752611994721 := by
  unfold tailWord_800394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298191865579177314338059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19461844974877806171568157 7298191865579177314338059)
  ·
    refine ⟨10947287798368765971507089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298191865579177314338059 10947287798368765971507089)
    ·
      refine ⟨8210465848776574478630317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947287798368765971507089 8210465848776574478630317)
      ·
        refine ⟨3078924693291215429486369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8210465848776574478630317 3078924693291215429486369)
        ·
          refine ⟨2309193519968411572114777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078924693291215429486369 2309193519968411572114777)
          ·
            refine ⟨1731895139976308679086083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309193519968411572114777 1731895139976308679086083)
            ·
              refine ⟨2597842709964463018629125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731895139976308679086083 2597842709964463018629125)
              ·
                refine ⟨487095508118336815992961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2597842709964463018629125 487095508118336815992961)
                ·
                  refine ⟨365321631088752611994721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487095508118336815992961 365321631088752611994721)
                  ·
                    rfl

theorem cell20_800394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_800394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800394 prefixEnd_800394 := by exact prefixLift 800394
  have htrace : WordTrace (prefixWord ++ tailWord_800394) baseStart_800394 baseEnd_800394 := by
    simpa [prefixWord, tailWord_800394, baseEnd_800394] using wordTrace_append hprefix tailTrace_800394
  have hstable : (prefixWord ++ tailWord_800394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800394).length < 2 ^ (prefixWord ++ tailWord_800394).sum := by decide
  have hdescent : baseEnd_800394 < baseStart_800394 := by decide
  rcases family_descends (prefixWord ++ tailWord_800394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800418 : List Nat := [3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_800418 : Nat := 118140960795 + 800418 * 2 ^ 59
def prefixEnd_800418 : Nat := 4983230072969 + 3 ^ 40 * 800418 * 2
def baseEnd_800418 : Nat := 121777528447571731731541

theorem tailTrace_800418 : CollatzResearch.WordTrace tailWord_800418 prefixEnd_800418 121777528447571731731541 := by
  unfold tailWord_800418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298410703557440339056477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19462428542819840904150605 7298410703557440339056477)
  ·
    refine ⟨2736904013834040127146179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7298410703557440339056477 2736904013834040127146179)
    ·
      refine ⟨4105356020751060190719269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736904013834040127146179 4105356020751060190719269)
      ·
        refine ⟨769754253890823785759863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4105356020751060190719269 769754253890823785759863)
        ·
          refine ⟨1154631380836235678639795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769754253890823785759863 1154631380836235678639795)
          ·
            refine ⟨1731947071254353517959693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154631380836235678639795 1731947071254353517959693)
            ·
              refine ⟨649480151720382569234885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731947071254353517959693 649480151720382569234885)
              ·
                refine ⟨121777528447571731731541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649480151720382569234885 121777528447571731731541)
                ·
                  rfl

theorem cell20_800418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_800418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800418 prefixEnd_800418 := by exact prefixLift 800418
  have htrace : WordTrace (prefixWord ++ tailWord_800418) baseStart_800418 baseEnd_800418 := by
    simpa [prefixWord, tailWord_800418, baseEnd_800418] using wordTrace_append hprefix tailTrace_800418
  have hstable : (prefixWord ++ tailWord_800418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800418).length < 2 ^ (prefixWord ++ tailWord_800418).sum := by decide
  have hdescent : baseEnd_800418 < baseStart_800418 := by decide
  rcases family_descends (prefixWord ++ tailWord_800418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800429 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_800429 : Nat := 118140960795 + 800429 * 2 ^ 59
def prefixEnd_800429 : Nat := 4983230072969 + 3 ^ 40 * 800429 * 2
def baseEnd_800429 : Nat := 365337606042448045827911

theorem tailTrace_800429 : CollatzResearch.WordTrace tailWord_800429 prefixEnd_800429 365337606042448045827911 := by
  unfold tailWord_800429
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194044017189910234876341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19462696011459940156584227 29194044017189910234876341)
  ·
    refine ⟨2736941626611554084519657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29194044017189910234876341 2736941626611554084519657)
    ·
      refine ⟨2052706219958665563389743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2736941626611554084519657 2052706219958665563389743)
      ·
        refine ⟨3079059329937998345084615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052706219958665563389743 3079059329937998345084615)
        ·
          refine ⟨4618588994906997517626923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079059329937998345084615 4618588994906997517626923)
          ·
            refine ⟨6927883492360496276440385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618588994906997517626923 6927883492360496276440385)
            ·
              refine ⟨5195912619270372207330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927883492360496276440385 5195912619270372207330289)
              ·
                refine ⟨3896934464452779155497717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195912619270372207330289 3896934464452779155497717)
                ·
                  refine ⟨365337606042448045827911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896934464452779155497717 365337606042448045827911)
                  ·
                    rfl

theorem cell20_800429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_800429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800429 prefixEnd_800429 := by exact prefixLift 800429
  have htrace : WordTrace (prefixWord ++ tailWord_800429) baseStart_800429 baseEnd_800429 := by
    simpa [prefixWord, tailWord_800429, baseEnd_800429] using wordTrace_append hprefix tailTrace_800429
  have hstable : (prefixWord ++ tailWord_800429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800429).length < 2 ^ (prefixWord ++ tailWord_800429).sum := by decide
  have hdescent : baseEnd_800429 < baseStart_800429 := by decide
  rcases family_descends (prefixWord ++ tailWord_800429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800446 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_800446 : Nat := 118140960795 + 800446 * 2 ^ 59
def prefixEnd_800446 : Nat := 4983230072969 + 3 ^ 40 * 800446 * 2
def baseEnd_800446 : Nat := 365345365305671542261175

theorem tailTrace_800446 : CollatzResearch.WordTrace tailWord_800446 prefixEnd_800446 365345365305671542261175 := by
  unfold tailWord_800446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649333007266040267280649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19463109372085548092163461 3649333007266040267280649)
  ·
    refine ⟨2736999755449530200460487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3649333007266040267280649 2736999755449530200460487)
    ·
      refine ⟨4105499633174295300690731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736999755449530200460487 4105499633174295300690731)
      ·
        refine ⟨6158249449761442951036097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105499633174295300690731 6158249449761442951036097)
        ·
          refine ⟨4618687087321082213277073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6158249449761442951036097 4618687087321082213277073)
          ·
            refine ⟨3464015315490811659957805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618687087321082213277073 3464015315490811659957805)
            ·
              refine ⟨1299005743309054372484177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3464015315490811659957805 1299005743309054372484177)
              ·
                refine ⟨974254307481790779363133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299005743309054372484177 974254307481790779363133)
                ·
                  refine ⟨365345365305671542261175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974254307481790779363133 365345365305671542261175)
                  ·
                    rfl

theorem cell20_800446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_800446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800446 prefixEnd_800446 := by exact prefixLift 800446
  have htrace : WordTrace (prefixWord ++ tailWord_800446) baseStart_800446 baseEnd_800446 := by
    simpa [prefixWord, tailWord_800446, baseEnd_800446] using wordTrace_append hprefix tailTrace_800446
  have hstable : (prefixWord ++ tailWord_800446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800446).length < 2 ^ (prefixWord ++ tailWord_800446).sum := by decide
  have hdescent : baseEnd_800446 < baseStart_800446 := by decide
  rcases family_descends (prefixWord ++ tailWord_800446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800474 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_800474 : Nat := 118140960795 + 800474 * 2 ^ 59
def prefixEnd_800474 : Nat := 4983230072969 + 3 ^ 40 * 800474 * 2
def baseEnd_800474 : Nat := 365358145268627889327727

theorem tailTrace_800474 : CollatzResearch.WordTrace tailWord_800474 prefixEnd_800474 365358145268627889327727 := by
  unfold tailWord_800474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298921325506720730066119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19463790201351255280176317 7298921325506720730066119)
  ·
    refine ⟨10948381988260081095099179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298921325506720730066119 10948381988260081095099179)
    ·
      refine ⟨16422572982390121642648769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10948381988260081095099179 16422572982390121642648769)
      ·
        refine ⟨12316929736792591231986577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16422572982390121642648769 12316929736792591231986577)
        ·
          refine ⟨9237697302594443423989933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12316929736792591231986577 9237697302594443423989933)
          ·
            refine ⟨3464136488472916283996225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9237697302594443423989933 3464136488472916283996225)
            ·
              refine ⟨2598102366354687212997169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464136488472916283996225 2598102366354687212997169)
              ·
                refine ⟨1948576774766015409747877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598102366354687212997169 1948576774766015409747877)
                ·
                  refine ⟨365358145268627889327727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948576774766015409747877 365358145268627889327727)
                  ·
                    rfl

theorem cell20_800474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_800474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800474 prefixEnd_800474 := by exact prefixLift 800474
  have htrace : WordTrace (prefixWord ++ tailWord_800474) baseStart_800474 baseEnd_800474 := by
    simpa [prefixWord, tailWord_800474, baseEnd_800474] using wordTrace_append hprefix tailTrace_800474
  have hstable : (prefixWord ++ tailWord_800474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800474).length < 2 ^ (prefixWord ++ tailWord_800474).sum := by decide
  have hdescent : baseEnd_800474 < baseStart_800474 := by decide
  rcases family_descends (prefixWord ++ tailWord_800474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800477 : List Nat := [1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_800477 : Nat := 118140960795 + 800477 * 2 ^ 59
def prefixEnd_800477 : Nat := 4983230072969 + 3 ^ 40 * 800477 * 2
def baseEnd_800477 : Nat := 121786504850124404075905

theorem tailTrace_800477 : CollatzResearch.WordTrace tailWord_800477 prefixEnd_800477 121786504850124404075905 := by
  unfold tailWord_800477
  simp only [CollatzResearch.WordTrace]
  refine ⟨29195794721016014432623685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19463863147344009621749123 29195794721016014432623685)
  ·
    refine ⟨5474211510190502706116941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29195794721016014432623685 5474211510190502706116941)
    ·
      refine ⟨2052829316321438514793853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5474211510190502706116941 2052829316321438514793853)
      ·
        refine ⟨769810993620539443047695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2052829316321438514793853 769810993620539443047695)
        ·
          refine ⟨1154716490430809164571543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769810993620539443047695 1154716490430809164571543)
          ·
            refine ⟨1732074735646213746857315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154716490430809164571543 1732074735646213746857315)
            ·
              refine ⟨2598112103469320620285973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732074735646213746857315 2598112103469320620285973)
              ·
                refine ⟨121786504850124404075905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2598112103469320620285973 121786504850124404075905)
                ·
                  rfl

theorem cell20_800477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_800477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800477 prefixEnd_800477 := by exact prefixLift 800477
  have htrace : WordTrace (prefixWord ++ tailWord_800477) baseStart_800477 baseEnd_800477 := by
    simpa [prefixWord, tailWord_800477, baseEnd_800477] using wordTrace_append hprefix tailTrace_800477
  have hstable : (prefixWord ++ tailWord_800477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800477).length < 2 ^ (prefixWord ++ tailWord_800477).sum := by decide
  have hdescent : baseEnd_800477 < baseStart_800477 := by decide
  rcases family_descends (prefixWord ++ tailWord_800477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800491 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 2]
def baseStart_800491 : Nat := 118140960795 + 800491 * 2 ^ 59
def prefixEnd_800491 : Nat := 4983230072969 + 3 ^ 40 * 800491 * 2
def baseEnd_800491 : Nat := 365365904531851385760991

theorem tailTrace_800491 : CollatzResearch.WordTrace tailWord_800491 prefixEnd_800491 365365904531851385760991 := by
  unfold tailWord_800491
  simp only [CollatzResearch.WordTrace]
  refine ⟨29196305342965294823633327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19464203561976863215755551 29196305342965294823633327)
  ·
    refine ⟨43794458014447942235449991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29196305342965294823633327 43794458014447942235449991)
    ·
      refine ⟨65691687021671913353174987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43794458014447942235449991 65691687021671913353174987)
      ·
        refine ⟨98537530532507870029762481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65691687021671913353174987 98537530532507870029762481)
        ·
          refine ⟨73903147899380902522321861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98537530532507870029762481 73903147899380902522321861)
          ·
            refine ⟨13856840231133919222935349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73903147899380902522321861 13856840231133919222935349)
            ·
              refine ⟨1299078771668804927150189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13856840231133919222935349 1299078771668804927150189)
              ·
                refine ⟨487154539375801847681321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299078771668804927150189 487154539375801847681321)
                ·
                  refine ⟨365365904531851385760991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487154539375801847681321 365365904531851385760991)
                  ·
                    rfl

theorem cell20_800491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2].length) (baseStart_800491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800491 prefixEnd_800491 := by exact prefixLift 800491
  have htrace : WordTrace (prefixWord ++ tailWord_800491) baseStart_800491 baseEnd_800491 := by
    simpa [prefixWord, tailWord_800491, baseEnd_800491] using wordTrace_append hprefix tailTrace_800491
  have hstable : (prefixWord ++ tailWord_800491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800491).length < 2 ^ (prefixWord ++ tailWord_800491).sum := by decide
  have hdescent : baseEnd_800491 < baseStart_800491 := by decide
  rcases family_descends (prefixWord ++ tailWord_800491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800508 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_800508 : Nat := 118140960795 + 800508 * 2 ^ 59
def prefixEnd_800508 : Nat := 4983230072969 + 3 ^ 40 * 800508 * 2
def baseEnd_800508 : Nat := 365373663795074882194255

theorem tailTrace_800508 : CollatzResearch.WordTrace tailWord_800508 prefixEnd_800508 365373663795074882194255 := by
  unfold tailWord_800508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14598462691951853363501089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19464616922602471151334785 14598462691951853363501089)
  ·
    refine ⟨10948847018963890022625817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14598462691951853363501089 10948847018963890022625817)
    ·
      refine ⟨8211635264222917516969363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10948847018963890022625817 8211635264222917516969363)
      ·
        refine ⟨12317452896334376275454045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211635264222917516969363 12317452896334376275454045)
        ·
          refine ⟨4619044836125391103295267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12317452896334376275454045 4619044836125391103295267)
          ·
            refine ⟨6928567254188086654942901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619044836125391103295267 6928567254188086654942901)
            ·
              refine ⟨649553180080133123900897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6928567254188086654942901 649553180080133123900897)
              ·
                refine ⟨487164885060099842925673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649553180080133123900897 487164885060099842925673)
                ·
                  refine ⟨365373663795074882194255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487164885060099842925673 365373663795074882194255)
                  ·
                    rfl

theorem cell20_800508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_800508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800508 prefixEnd_800508 := by exact prefixLift 800508
  have htrace : WordTrace (prefixWord ++ tailWord_800508) baseStart_800508 baseEnd_800508 := by
    simpa [prefixWord, tailWord_800508, baseEnd_800508] using wordTrace_append hprefix tailTrace_800508
  have hstable : (prefixWord ++ tailWord_800508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800508).length < 2 ^ (prefixWord ++ tailWord_800508).sum := by decide
  have hdescent : baseEnd_800508 < baseStart_800508 := by decide
  rcases family_descends (prefixWord ++ tailWord_800508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800522 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_800522 : Nat := 118140960795 + 800522 * 2 ^ 59
def prefixEnd_800522 : Nat := 4983230072969 + 3 ^ 40 * 800522 * 2
def baseEnd_800522 : Nat := 365380053776553055727531

theorem tailTrace_800522 : CollatzResearch.WordTrace tailWord_800522 prefixEnd_800522 365380053776553055727531 := by
  unfold tailWord_800522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299359001463246779502955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19464957337235324745341213 7299359001463246779502955)
  ·
    refine ⟨10949038502194870169254433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299359001463246779502955 10949038502194870169254433)
    ·
      refine ⟨8211778876646152626940825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10949038502194870169254433 8211778876646152626940825)
      ·
        refine ⟨6158834157484614470205619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8211778876646152626940825 6158834157484614470205619)
        ·
          refine ⟨9238251236226921705308429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158834157484614470205619 9238251236226921705308429)
          ·
            refine ⟨3464344213585095639490661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9238251236226921705308429 3464344213585095639490661)
            ·
              refine ⟨649564540047205432404499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3464344213585095639490661 649564540047205432404499)
              ·
                refine ⟨974346810070808148606749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649564540047205432404499 974346810070808148606749)
                ·
                  refine ⟨365380053776553055727531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974346810070808148606749 365380053776553055727531)
                  ·
                    rfl

theorem cell20_800522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_800522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800522 prefixEnd_800522 := by exact prefixLift 800522
  have htrace : WordTrace (prefixWord ++ tailWord_800522) baseStart_800522 baseEnd_800522 := by
    simpa [prefixWord, tailWord_800522, baseEnd_800522] using wordTrace_append hprefix tailTrace_800522
  have hstable : (prefixWord ++ tailWord_800522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800522).length < 2 ^ (prefixWord ++ tailWord_800522).sum := by decide
  have hdescent : baseEnd_800522 < baseStart_800522 := by decide
  rcases family_descends (prefixWord ++ tailWord_800522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800557 : List Nat := [1, 5, 3, 11]
def baseStart_800557 : Nat := 118140960795 + 800557 * 2 ^ 59
def prefixEnd_800557 : Nat := 4983230072969 + 3 ^ 40 * 800557 * 2
def baseEnd_800557 : Nat := 1503687361029829175147

theorem tailTrace_800557 : CollatzResearch.WordTrace tailWord_800557 prefixEnd_800557 1503687361029829175147 := by
  unfold tailWord_800557
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198712560726188095535925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19465808373817458730357283 29198712560726188095535925)
  ·
    refine ⟨2737379302568080133956493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29198712560726188095535925 2737379302568080133956493)
    ·
      refine ⟨1026517238463030050233685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2737379302568080133956493 1026517238463030050233685)
      ·
        refine ⟨1503687361029829175147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1026517238463030050233685 1503687361029829175147)
        ·
          rfl

theorem cell20_800557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 11].length) (baseStart_800557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800557 prefixEnd_800557 := by exact prefixLift 800557
  have htrace : WordTrace (prefixWord ++ tailWord_800557) baseStart_800557 baseEnd_800557 := by
    simpa [prefixWord, tailWord_800557, baseEnd_800557] using wordTrace_append hprefix tailTrace_800557
  have hstable : (prefixWord ++ tailWord_800557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800557).length < 2 ^ (prefixWord ++ tailWord_800557).sum := by decide
  have hdescent : baseEnd_800557 < baseStart_800557 := by decide
  rcases family_descends (prefixWord ++ tailWord_800557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800563 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 2]
def baseStart_800563 : Nat := 118140960795 + 800563 * 2 ^ 59
def prefixEnd_800563 : Nat := 4983230072969 + 3 ^ 40 * 800563 * 2
def baseEnd_800563 : Nat := 365398767293739135360697

theorem tailTrace_800563 : CollatzResearch.WordTrace tailWord_800563 prefixEnd_800563 365398767293739135360697 := by
  unfold tailWord_800563
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198931398704451120254343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19465954265802967413502895 29198931398704451120254343)
  ·
    refine ⟨43798397098056676680381515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29198931398704451120254343 43798397098056676680381515)
    ·
      refine ⟨65697595647085015020572273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43798397098056676680381515 65697595647085015020572273)
      ·
        refine ⟨49273196735313761265429205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65697595647085015020572273 49273196735313761265429205)
        ·
          refine ⟨1154840548483916279658497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49273196735313761265429205 1154840548483916279658497)
          ·
            refine ⟨866130411362937209743873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154840548483916279658497 866130411362937209743873)
            ·
              refine ⟨649597808522202907307905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866130411362937209743873 649597808522202907307905)
              ·
                refine ⟨487198356391652180480929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649597808522202907307905 487198356391652180480929)
                ·
                  refine ⟨365398767293739135360697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487198356391652180480929 365398767293739135360697)
                  ·
                    rfl

theorem cell20_800563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2].length) (baseStart_800563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800563 prefixEnd_800563 := by exact prefixLift 800563
  have htrace : WordTrace (prefixWord ++ tailWord_800563) baseStart_800563 baseEnd_800563 := by
    simpa [prefixWord, tailWord_800563, baseEnd_800563] using wordTrace_append hprefix tailTrace_800563
  have hstable : (prefixWord ++ tailWord_800563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800563).length < 2 ^ (prefixWord ++ tailWord_800563).sum := by decide
  have hdescent : baseEnd_800563 < baseStart_800563 := by decide
  rcases family_descends (prefixWord ++ tailWord_800563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800574 : List Nat := [4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_800574 : Nat := 118140960795 + 800574 * 2 ^ 59
def prefixEnd_800574 : Nat := 4983230072969 + 3 ^ 40 * 800574 * 2
def baseEnd_800574 : Nat := 121801262664490661997995

theorem tailTrace_800574 : CollatzResearch.WordTrace tailWord_800574 prefixEnd_800574 121801262664490661997995 := by
  unfold tailWord_800574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649916575208074999863097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19466221734443066665936517 3649916575208074999863097)
  ·
    refine ⟨2737437431406056249897323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3649916575208074999863097 2737437431406056249897323)
    ·
      refine ⟨4106156147109084374845985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737437431406056249897323 4106156147109084374845985)
      ·
        refine ⟨3079617110331813281134489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106156147109084374845985 3079617110331813281134489)
        ·
          refine ⟨2309712832748859960850867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079617110331813281134489 2309712832748859960850867)
          ·
            refine ⟨3464569249123289941276301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309712832748859960850867 3464569249123289941276301)
            ·
              refine ⟨1299213468421233727978613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3464569249123289941276301 1299213468421233727978613)
              ·
                refine ⟨121801262664490661997995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1299213468421233727978613 121801262664490661997995)
                ·
                  rfl

theorem cell20_800574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_800574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800574 prefixEnd_800574 := by exact prefixLift 800574
  have htrace : WordTrace (prefixWord ++ tailWord_800574) baseStart_800574 baseEnd_800574 := by
    simpa [prefixWord, tailWord_800574, baseEnd_800574] using wordTrace_append hprefix tailTrace_800574
  have hstable : (prefixWord ++ tailWord_800574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800574).length < 2 ^ (prefixWord ++ tailWord_800574).sum := by decide
  have hdescent : baseEnd_800574 < baseStart_800574 := by decide
  rcases family_descends (prefixWord ++ tailWord_800574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800602 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_800602 : Nat := 118140960795 + 800602 * 2 ^ 59
def prefixEnd_800602 : Nat := 4983230072969 + 3 ^ 40 * 800602 * 2
def baseEnd_800602 : Nat := 365416567956428333060537

theorem tailTrace_800602 : CollatzResearch.WordTrace tailWord_800602 prefixEnd_800602 365416567956428333060537 := by
  unfold tailWord_800602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300088461390790195231015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19466902563708773853949373 7300088461390790195231015)
  ·
    refine ⟨10950132692086185292846523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300088461390790195231015 10950132692086185292846523)
    ·
      refine ⟨16425199038129277939269785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950132692086185292846523 16425199038129277939269785)
      ·
        refine ⟨12318899278596958454452339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16425199038129277939269785 12318899278596958454452339)
        ·
          refine ⟨18478348917895437681678509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318899278596958454452339 18478348917895437681678509)
          ·
            refine ⟨6929380844210789130629441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18478348917895437681678509 6929380844210789130629441)
            ·
              refine ⟨5197035633158091847972081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6929380844210789130629441 5197035633158091847972081)
              ·
                refine ⟨3897776724868568885979061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5197035633158091847972081 3897776724868568885979061)
                ·
                  refine ⟨365416567956428333060537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3897776724868568885979061 365416567956428333060537)
                  ·
                    rfl

theorem cell20_800602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_800602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800602 prefixEnd_800602 := by exact prefixLift 800602
  have htrace : WordTrace (prefixWord ++ tailWord_800602) baseStart_800602 baseEnd_800602 := by
    simpa [prefixWord, tailWord_800602, baseEnd_800602] using wordTrace_append hprefix tailTrace_800602
  have hstable : (prefixWord ++ tailWord_800602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800602).length < 2 ^ (prefixWord ++ tailWord_800602).sum := by decide
  have hdescent : baseEnd_800602 < baseStart_800602 := by decide
  rcases family_descends (prefixWord ++ tailWord_800602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800609 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_800609 : Nat := 118140960795 + 800609 * 2 ^ 59
def prefixEnd_800609 : Nat := 4983230072969 + 3 ^ 40 * 800609 * 2
def baseEnd_800609 : Nat := 365419762947167419827175

theorem tailTrace_800609 : CollatzResearch.WordTrace tailWord_800609 prefixEnd_800609 365419762947167419827175 := by
  unfold tailWord_800609
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200609156537800976428881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19467072771025200650952587 29200609156537800976428881)
  ·
    refine ⟨21900456867403350732321661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29200609156537800976428881 21900456867403350732321661)
    ·
      refine ⟨8212671325276256524620623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21900456867403350732321661 8212671325276256524620623)
      ·
        refine ⟨12319006987914384786930935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212671325276256524620623 12319006987914384786930935)
        ·
          refine ⟨18478510481871577180396403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319006987914384786930935 18478510481871577180396403)
          ·
            refine ⟨27717765722807365770594605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18478510481871577180396403 27717765722807365770594605)
            ·
              refine ⟨10394162146052762163972977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27717765722807365770594605 10394162146052762163972977)
              ·
                refine ⟨7795621609539571622979733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394162146052762163972977 7795621609539571622979733)
                ·
                  refine ⟨365419762947167419827175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7795621609539571622979733 365419762947167419827175)
                  ·
                    rfl

theorem cell20_800609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_800609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800609 prefixEnd_800609 := by exact prefixLift 800609
  have htrace : WordTrace (prefixWord ++ tailWord_800609) baseStart_800609 baseEnd_800609 := by
    simpa [prefixWord, tailWord_800609, baseEnd_800609] using wordTrace_append hprefix tailTrace_800609
  have hstable : (prefixWord ++ tailWord_800609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800609).length < 2 ^ (prefixWord ++ tailWord_800609).sum := by decide
  have hdescent : baseEnd_800609 < baseStart_800609 := by decide
  rcases family_descends (prefixWord ++ tailWord_800609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800622 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_800622 : Nat := 118140960795 + 800622 * 2 ^ 59
def prefixEnd_800622 : Nat := 4983230072969 + 3 ^ 40 * 800622 * 2
def baseEnd_800622 : Nat := 365425696501397152393789

theorem tailTrace_800622 : CollatzResearch.WordTrace tailWord_800622 prefixEnd_800622 365425696501397152393789 := by
  unfold tailWord_800622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650135413186338024581515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19467388870327136131101413 3650135413186338024581515)
  ·
    refine ⟨5475203119779507036872273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650135413186338024581515 5475203119779507036872273)
    ·
      refine ⟨4106402339834630277654205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475203119779507036872273 4106402339834630277654205)
      ·
        refine ⟨1539900877437986354120327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4106402339834630277654205 1539900877437986354120327)
        ·
          refine ⟨2309851316156979531180491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539900877437986354120327 2309851316156979531180491)
          ·
            refine ⟨3464776974235469296770737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309851316156979531180491 3464776974235469296770737)
            ·
              refine ⟨2598582730676601972578053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464776974235469296770737 2598582730676601972578053)
              ·
                refine ⟨487234262001862869858385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2598582730676601972578053 487234262001862869858385)
                ·
                  refine ⟨365425696501397152393789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487234262001862869858385 365425696501397152393789)
                  ·
                    rfl

theorem cell20_800622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_800622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800622 prefixEnd_800622 := by exact prefixLift 800622
  have htrace : WordTrace (prefixWord ++ tailWord_800622) baseStart_800622 baseEnd_800622 := by
    simpa [prefixWord, tailWord_800622, baseEnd_800622] using wordTrace_append hprefix tailTrace_800622
  have hstable : (prefixWord ++ tailWord_800622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800622).length < 2 ^ (prefixWord ++ tailWord_800622).sum := by decide
  have hdescent : baseEnd_800622 < baseStart_800622 := by decide
  rcases family_descends (prefixWord ++ tailWord_800622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800650 : List Nat := [3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_800650 : Nat := 118140960795 + 800650 * 2 ^ 59
def prefixEnd_800650 : Nat := 4983230072969 + 3 ^ 40 * 800650 * 2
def baseEnd_800650 : Nat := 121812825488117833153447

theorem tailTrace_800650 : CollatzResearch.WordTrace tailWord_800650 prefixEnd_800650 121812825488117833153447 := by
  unfold tailWord_800650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300526137347316244667851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19468069699592843319114269 7300526137347316244667851)
  ·
    refine ⟨10950789206020974367001777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300526137347316244667851 10950789206020974367001777)
    ·
      refine ⟨8213091904515730775251333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10950789206020974367001777 8213091904515730775251333)
      ·
        refine ⟨1539954732096699520359625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8213091904515730775251333 1539954732096699520359625)
        ·
          refine ⟨1154966049072524640269719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539954732096699520359625 1154966049072524640269719)
          ·
            refine ⟨1732449073608786960404579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154966049072524640269719 1732449073608786960404579)
            ·
              refine ⟨2598673610413180440606869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732449073608786960404579 2598673610413180440606869)
              ·
                refine ⟨121812825488117833153447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2598673610413180440606869 121812825488117833153447)
                ·
                  rfl

theorem cell20_800650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_800650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800650 prefixEnd_800650 := by exact prefixLift 800650
  have htrace : WordTrace (prefixWord ++ tailWord_800650) baseStart_800650 baseEnd_800650 := by
    simpa [prefixWord, tailWord_800650, baseEnd_800650] using wordTrace_append hprefix tailTrace_800650
  have hstable : (prefixWord ++ tailWord_800650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800650).length < 2 ^ (prefixWord ++ tailWord_800650).sum := by decide
  have hdescent : baseEnd_800650 < baseStart_800650 := by decide
  rcases family_descends (prefixWord ++ tailWord_800650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800660 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_800660 : Nat := 118140960795 + 800660 * 2 ^ 59
def prefixEnd_800660 : Nat := 4983230072969 + 3 ^ 40 * 800660 * 2
def baseEnd_800660 : Nat := 365443040736837909126967

theorem tailTrace_800660 : CollatzResearch.WordTrace tailWord_800660 prefixEnd_800660 365443040736837909126967 := by
  unfold tailWord_800660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601234639676518343267717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19468312852902024457690289 14601234639676518343267717)
  ·
    refine ⟨2737731494939347189362697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14601234639676518343267717 2737731494939347189362697)
    ·
      refine ⟨2053298621204510392022023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2737731494939347189362697 2053298621204510392022023)
      ·
        refine ⟨3079947931806765588033035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053298621204510392022023 3079947931806765588033035)
        ·
          refine ⟨4619921897710148382049553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079947931806765588033035 4619921897710148382049553)
          ·
            refine ⟨3464941423282611286537165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619921897710148382049553 3464941423282611286537165)
            ·
              refine ⟨1299353033730979232451437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3464941423282611286537165 1299353033730979232451437)
              ·
                refine ⟨487257387649117212169289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299353033730979232451437 487257387649117212169289)
                ·
                  refine ⟨365443040736837909126967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487257387649117212169289 365443040736837909126967)
                  ·
                    rfl

theorem cell20_800660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_800660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800660 prefixEnd_800660 := by exact prefixLift 800660
  have htrace : WordTrace (prefixWord ++ tailWord_800660) baseStart_800660 baseEnd_800660 := by
    simpa [prefixWord, tailWord_800660, baseEnd_800660] using wordTrace_append hprefix tailTrace_800660
  have hstable : (prefixWord ++ tailWord_800660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800660).length < 2 ^ (prefixWord ++ tailWord_800660).sum := by decide
  have hdescent : baseEnd_800660 < baseStart_800660 := by decide
  rcases family_descends (prefixWord ++ tailWord_800660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800726 : List Nat := [5, 2, 1, 1, 3, 8]
def baseStart_800726 : Nat := 118140960795 + 800726 * 2 ^ 59
def prefixEnd_800726 : Nat := 4983230072969 + 3 ^ 40 * 800726 * 2
def baseEnd_800726 : Nat := 13536043145749444923211

theorem tailTrace_800726 : CollatzResearch.WordTrace tailWord_800726 prefixEnd_800726 13536043145749444923211 := by
  unfold tailWord_800726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825304781069620622402377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19469917664742619972292021 1825304781069620622402377)
  ·
    refine ⟨1368978585802215466801783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1825304781069620622402377 1368978585802215466801783)
    ·
      refine ⟨2053467878703323200202675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368978585802215466801783 2053467878703323200202675)
      ·
        refine ⟨3080201818054984800304013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053467878703323200202675 3080201818054984800304013)
        ·
          refine ⟨1155075681770619300114005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3080201818054984800304013 1155075681770619300114005)
          ·
            refine ⟨13536043145749444923211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1155075681770619300114005 13536043145749444923211)
            ·
              rfl

theorem cell20_800726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 8].length) (baseStart_800726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800726 prefixEnd_800726 := by exact prefixLift 800726
  have htrace : WordTrace (prefixWord ++ tailWord_800726) baseStart_800726 baseEnd_800726 := by
    simpa [prefixWord, tailWord_800726, baseEnd_800726] using wordTrace_append hprefix tailTrace_800726
  have hstable : (prefixWord ++ tailWord_800726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800726).length < 2 ^ (prefixWord ++ tailWord_800726).sum := by decide
  have hdescent : baseEnd_800726 < baseStart_800726 := by decide
  rcases family_descends (prefixWord ++ tailWord_800726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800730 : List Nat := [3, 1, 1, 2, 13]
def baseStart_800730 : Nat := 118140960795 + 800730 * 2 ^ 59
def prefixEnd_800730 : Nat := 4983230072969 + 3 ^ 40 * 800730 * 2
def baseEnd_800730 : Nat := 4512036921533688602387

theorem tailTrace_800730 : CollatzResearch.WordTrace tailWord_800730 prefixEnd_800730 4512036921533688602387 := by
  unfold tailWord_800730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7301255597274859660395911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19470014926066292427722429 7301255597274859660395911)
  ·
    refine ⟨10951883395912289490593867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7301255597274859660395911 10951883395912289490593867)
    ·
      refine ⟨16427825093868434235890801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951883395912289490593867 16427825093868434235890801)
      ·
        refine ⟨12320868820401325676918101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16427825093868434235890801 12320868820401325676918101)
        ·
          refine ⟨4512036921533688602387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12320868820401325676918101 4512036921533688602387)
          ·
            rfl

theorem cell20_800730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 13].length) (baseStart_800730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800730 prefixEnd_800730 := by exact prefixLift 800730
  have htrace : WordTrace (prefixWord ++ tailWord_800730) baseStart_800730 baseEnd_800730 := by
    simpa [prefixWord, tailWord_800730, baseEnd_800730] using wordTrace_append hprefix tailTrace_800730
  have hstable : (prefixWord ++ tailWord_800730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800730).length < 2 ^ (prefixWord ++ tailWord_800730).sum := by decide
  have hdescent : baseEnd_800730 < baseStart_800730 := by decide
  rcases family_descends (prefixWord ++ tailWord_800730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800732 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_800732 : Nat := 118140960795 + 800732 * 2 ^ 59
def prefixEnd_800732 : Nat := 4983230072969 + 3 ^ 40 * 800732 * 2
def baseEnd_800732 : Nat := 365475903498725658726673

theorem tailTrace_800732 : CollatzResearch.WordTrace tailWord_800732 prefixEnd_800732 365475903498725658726673 := by
  unfold tailWord_800732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14602547667546096491578225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19470063556728128655437633 14602547667546096491578225)
  ·
    refine ⟨10951910750659572368683669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14602547667546096491578225 10951910750659572368683669)
    ·
      refine ⟨513370816437167454782047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10951910750659572368683669 513370816437167454782047)
      ·
        refine ⟨770056224655751182173071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513370816437167454782047 770056224655751182173071)
        ·
          refine ⟨1155084336983626773259607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770056224655751182173071 1155084336983626773259607)
          ·
            refine ⟨1732626505475440159889411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155084336983626773259607 1732626505475440159889411)
            ·
              refine ⟨2598939758213160239834117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732626505475440159889411 2598939758213160239834117)
              ·
                refine ⟨487301204664967544968897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2598939758213160239834117 487301204664967544968897)
                ·
                  refine ⟨365475903498725658726673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487301204664967544968897 365475903498725658726673)
                  ·
                    rfl

theorem cell20_800732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_800732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800732 prefixEnd_800732 := by exact prefixLift 800732
  have htrace : WordTrace (prefixWord ++ tailWord_800732) baseStart_800732 baseEnd_800732 := by
    simpa [prefixWord, tailWord_800732, baseEnd_800732] using wordTrace_append hprefix tailTrace_800732
  have hstable : (prefixWord ++ tailWord_800732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800732).length < 2 ^ (prefixWord ++ tailWord_800732).sum := by decide
  have hdescent : baseEnd_800732 < baseStart_800732 := by decide
  rcases family_descends (prefixWord ++ tailWord_800732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800743 : List Nat := [1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_800743 : Nat := 118140960795 + 800743 * 2 ^ 59
def prefixEnd_800743 : Nat := 4983230072969 + 3 ^ 40 * 800743 * 2
def baseEnd_800743 : Nat := 121826974732819503119987

theorem tailTrace_800743 : CollatzResearch.WordTrace tailWord_800743 prefixEnd_800743 121826974732819503119987 := by
  unfold tailWord_800743
  simp only [CollatzResearch.WordTrace]
  refine ⟨29205496538052341861806883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19470331025368227907871255 29205496538052341861806883)
  ·
    refine ⟨43808244807078512792710325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29205496538052341861806883 43808244807078512792710325)
    ·
      refine ⟨4107022950663610574316593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43808244807078512792710325 4107022950663610574316593)
      ·
        refine ⟨3080267212997707930737445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4107022950663610574316593 3080267212997707930737445)
        ·
          refine ⟨577550102437070237013271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3080267212997707930737445 577550102437070237013271)
          ·
            refine ⟨866325153655605355519907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577550102437070237013271 866325153655605355519907)
            ·
              refine ⟨1299487730483408033279861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866325153655605355519907 1299487730483408033279861)
              ·
                refine ⟨121826974732819503119987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1299487730483408033279861 121826974732819503119987)
                ·
                  rfl

theorem cell20_800743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_800743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800743 prefixEnd_800743 := by exact prefixLift 800743
  have htrace : WordTrace (prefixWord ++ tailWord_800743) baseStart_800743 baseEnd_800743 := by
    simpa [prefixWord, tailWord_800743, baseEnd_800743] using wordTrace_append hprefix tailTrace_800743
  have hstable : (prefixWord ++ tailWord_800743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800743).length < 2 ^ (prefixWord ++ tailWord_800743).sum := by decide
  have hdescent : baseEnd_800743 < baseStart_800743 := by decide
  rcases family_descends (prefixWord ++ tailWord_800743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800761 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_800761 : Nat := 118140960795 + 800761 * 2 ^ 59
def prefixEnd_800761 : Nat := 4983230072969 + 3 ^ 40 * 800761 * 2
def baseEnd_800761 : Nat := 365489139888930446759887

theorem tailTrace_800761 : CollatzResearch.WordTrace tailWord_800761 prefixEnd_800761 365489139888930446759887 := by
  unfold tailWord_800761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29206153051987130935962137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19470768701324753957308091 29206153051987130935962137)
  ·
    refine ⟨21904614788990348201971603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29206153051987130935962137 21904614788990348201971603)
    ·
      refine ⟨32856922183485522302957405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21904614788990348201971603 32856922183485522302957405)
      ·
        refine ⟨12321345818807070863609027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32856922183485522302957405 12321345818807070863609027)
        ·
          refine ⟨18482018728210606295413541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321345818807070863609027 18482018728210606295413541)
          ·
            refine ⟨3465378511539488680390039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18482018728210606295413541 3465378511539488680390039)
            ·
              refine ⟨5198067767309233020585059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465378511539488680390039 5198067767309233020585059)
              ·
                refine ⟨7797101650963849530877589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198067767309233020585059 7797101650963849530877589)
                ·
                  refine ⟨365489139888930446759887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7797101650963849530877589 365489139888930446759887)
                  ·
                    rfl

theorem cell20_800761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_800761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800761 prefixEnd_800761 := by exact prefixLift 800761
  have htrace : WordTrace (prefixWord ++ tailWord_800761) baseStart_800761 baseEnd_800761 := by
    simpa [prefixWord, tailWord_800761, baseEnd_800761] using wordTrace_append hprefix tailTrace_800761
  have hstable : (prefixWord ++ tailWord_800761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800761).length < 2 ^ (prefixWord ++ tailWord_800761).sum := by decide
  have hdescent : baseEnd_800761 < baseStart_800761 := by decide
  rcases family_descends (prefixWord ++ tailWord_800761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800792 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_800792 : Nat := 118140960795 + 800792 * 2 ^ 59
def prefixEnd_800792 : Nat := 4983230072969 + 3 ^ 40 * 800792 * 2
def baseEnd_800792 : Nat := 365503289133632116726427

theorem tailTrace_800792 : CollatzResearch.WordTrace tailWord_800792 prefixEnd_800792 365503289133632116726427 := by
  unfold tailWord_800792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603641857437411615170315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19471522476583215486893753 14603641857437411615170315)
  ·
    refine ⟨21905462786156117422755473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14603641857437411615170315 21905462786156117422755473)
    ·
      refine ⟨16429097089617088067066605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21905462786156117422755473 16429097089617088067066605)
      ·
        refine ⟨6160911408606408025149977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16429097089617088067066605 6160911408606408025149977)
        ·
          refine ⟨4620683556454806018862483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6160911408606408025149977 4620683556454806018862483)
          ·
            refine ⟨6931025334682209028293725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620683556454806018862483 6931025334682209028293725)
            ·
              refine ⟨2599134500505828385610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6931025334682209028293725 2599134500505828385610147)
              ·
                refine ⟨3898701750758742578415221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599134500505828385610147 3898701750758742578415221)
                ·
                  refine ⟨365503289133632116726427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3898701750758742578415221 365503289133632116726427)
                  ·
                    rfl

theorem cell20_800792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_800792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800792 prefixEnd_800792 := by exact prefixLift 800792
  have htrace : WordTrace (prefixWord ++ tailWord_800792) baseStart_800792 baseEnd_800792 := by
    simpa [prefixWord, tailWord_800792, baseEnd_800792] using wordTrace_append hprefix tailTrace_800792
  have hstable : (prefixWord ++ tailWord_800792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800792).length < 2 ^ (prefixWord ++ tailWord_800792).sum := by decide
  have hdescent : baseEnd_800792 < baseStart_800792 := by decide
  rcases family_descends (prefixWord ++ tailWord_800792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800823 : List Nat := [1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_800823 : Nat := 118140960795 + 800823 * 2 ^ 59
def prefixEnd_800823 : Nat := 4983230072969 + 3 ^ 40 * 800823 * 2
def baseEnd_800823 : Nat := 121839146126111262230989

theorem tailTrace_800823 : CollatzResearch.WordTrace tailWord_800823 prefixEnd_800823 121839146126111262230989 := by
  unfold tailWord_800823
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208414377762515524719123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19472276251841677016479415 29208414377762515524719123)
  ·
    refine ⟨43812621566643773287078685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29208414377762515524719123 43812621566643773287078685)
    ·
      refine ⟨16429733087491414982654507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43812621566643773287078685 16429733087491414982654507)
      ·
        refine ⟨24644599631237122473981761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429733087491414982654507 24644599631237122473981761)
        ·
          refine ⟨18483449723427841855486321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24644599631237122473981761 18483449723427841855486321)
          ·
            refine ⟨13862587292570881391614741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18483449723427841855486321 13862587292570881391614741)
            ·
              refine ⟨649808779339260065231941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13862587292570881391614741 649808779339260065231941)
              ·
                refine ⟨121839146126111262230989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649808779339260065231941 121839146126111262230989)
                ·
                  rfl

theorem cell20_800823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_800823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800823 prefixEnd_800823 := by exact prefixLift 800823
  have htrace : WordTrace (prefixWord ++ tailWord_800823) baseStart_800823 baseEnd_800823 := by
    simpa [prefixWord, tailWord_800823, baseEnd_800823] using wordTrace_append hprefix tailTrace_800823
  have hstable : (prefixWord ++ tailWord_800823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800823).length < 2 ^ (prefixWord ++ tailWord_800823).sum := by decide
  have hdescent : baseEnd_800823 < baseStart_800823 := by decide
  rcases family_descends (prefixWord ++ tailWord_800823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800844 : List Nat := [2, 2, 1, 3, 1, 1, 10]
def baseStart_800844 : Nat := 118140960795 + 800844 * 2 ^ 59
def prefixEnd_800844 : Nat := 4983230072969 + 3 ^ 40 * 800844 * 2
def baseEnd_800844 : Nat := 40614113705616782999209

theorem tailTrace_800844 : CollatzResearch.WordTrace tailWord_800844 prefixEnd_800844 40614113705616782999209 := by
  unfold tailWord_800844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604590155343218055616793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19472786873790957407489057 14604590155343218055616793)
  ·
    refine ⟨10953442616507413541712595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14604590155343218055616793 10953442616507413541712595)
    ·
      refine ⟨16430163924761120312568893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953442616507413541712595 16430163924761120312568893)
      ·
        refine ⟨6161311471785420117213335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16430163924761120312568893 6161311471785420117213335)
        ·
          refine ⟨9241967207678130175820003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161311471785420117213335 9241967207678130175820003)
          ·
            refine ⟨13862950811517195263730005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241967207678130175820003 13862950811517195263730005)
            ·
              refine ⟨40614113705616782999209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13862950811517195263730005 40614113705616782999209)
              ·
                rfl

theorem cell20_800844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_800844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800844 prefixEnd_800844 := by exact prefixLift 800844
  have htrace : WordTrace (prefixWord ++ tailWord_800844) baseStart_800844 baseEnd_800844 := by
    simpa [prefixWord, tailWord_800844, baseEnd_800844] using wordTrace_append hprefix tailTrace_800844
  have hstable : (prefixWord ++ tailWord_800844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800844).length < 2 ^ (prefixWord ++ tailWord_800844).sum := by decide
  have hdescent : baseEnd_800844 < baseStart_800844 := by decide
  rcases family_descends (prefixWord ++ tailWord_800844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800850 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_800850 : Nat := 118140960795 + 800850 * 2 ^ 59
def prefixEnd_800850 : Nat := 4983230072969 + 3 ^ 40 * 800850 * 2
def baseEnd_800850 : Nat := 365529761914041692792857

theorem tailTrace_800850 : CollatzResearch.WordTrace tailWord_800850 prefixEnd_800850 365529761914041692792857 := by
  unfold tailWord_800850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302349787166174783988001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19472932765776466090634669 7302349787166174783988001)
  ·
    refine ⟨5476762340374631087991001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7302349787166174783988001 5476762340374631087991001)
    ·
      refine ⟨4107571755280973315993251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5476762340374631087991001 4107571755280973315993251)
      ·
        refine ⟨6161357632921459973989877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107571755280973315993251 6161357632921459973989877)
        ·
          refine ⟨577627278086386872561551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6161357632921459973989877 577627278086386872561551)
          ·
            refine ⟨866440917129580308842327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577627278086386872561551 866440917129580308842327)
            ·
              refine ⟨1299661375694370463263491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866440917129580308842327 1299661375694370463263491)
              ·
                refine ⟨1949492063541555694895237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299661375694370463263491 1949492063541555694895237)
                ·
                  refine ⟨365529761914041692792857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949492063541555694895237 365529761914041692792857)
                  ·
                    rfl

theorem cell20_800850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_800850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800850 prefixEnd_800850 := by exact prefixLift 800850
  have htrace : WordTrace (prefixWord ++ tailWord_800850) baseStart_800850 baseEnd_800850 := by
    simpa [prefixWord, tailWord_800850, baseEnd_800850] using wordTrace_append hprefix tailTrace_800850
  have hstable : (prefixWord ++ tailWord_800850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800850).length < 2 ^ (prefixWord ++ tailWord_800850).sum := by decide
  have hdescent : baseEnd_800850 < baseStart_800850 := by decide
  rcases family_descends (prefixWord ++ tailWord_800850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800851 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_800851 : Nat := 118140960795 + 800851 * 2 ^ 59
def prefixEnd_800851 : Nat := 4983230072969 + 3 ^ 40 * 800851 * 2
def baseEnd_800851 : Nat := 365530218341290133759519

theorem tailTrace_800851 : CollatzResearch.WordTrace tailWord_800851 prefixEnd_800851 365530218341290133759519 := by
  unfold tailWord_800851
  simp only [CollatzResearch.WordTrace]
  refine ⟨29209435621661076306738407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19472957081107384204492271 29209435621661076306738407)
  ·
    refine ⟨43814153432491614460107611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29209435621661076306738407 43814153432491614460107611)
    ·
      refine ⟨65721230148737421690161417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43814153432491614460107611 65721230148737421690161417)
      ·
        refine ⟨49290922611553066267621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65721230148737421690161417 49290922611553066267621063)
        ·
          refine ⟨73936383917329599401431595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49290922611553066267621063 73936383917329599401431595)
          ·
            refine ⟨110904575875994399102147393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73936383917329599401431595 110904575875994399102147393)
            ·
              refine ⟨83178431906995799326610545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110904575875994399102147393 83178431906995799326610545)
              ·
                refine ⟨62383823930246849494957909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83178431906995799326610545 62383823930246849494957909)
                ·
                  refine ⟨365530218341290133759519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62383823930246849494957909 365530218341290133759519)
                  ·
                    rfl

theorem cell20_800851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_800851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800851 prefixEnd_800851 := by exact prefixLift 800851
  have htrace : WordTrace (prefixWord ++ tailWord_800851) baseStart_800851 baseEnd_800851 := by
    simpa [prefixWord, tailWord_800851, baseEnd_800851] using wordTrace_append hprefix tailTrace_800851
  have hstable : (prefixWord ++ tailWord_800851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800851).length < 2 ^ (prefixWord ++ tailWord_800851).sum := by decide
  have hdescent : baseEnd_800851 < baseStart_800851 := by decide
  rcases family_descends (prefixWord ++ tailWord_800851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800864 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_800864 : Nat := 118140960795 + 800864 * 2 ^ 59
def prefixEnd_800864 : Nat := 4983230072969 + 3 ^ 40 * 800864 * 2
def baseEnd_800864 : Nat := 365536151895519866326133

theorem tailTrace_800864 : CollatzResearch.WordTrace tailWord_800864 prefixEnd_800864 365536151895519866326133 := by
  unfold tailWord_800864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604954885306989763480823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19473273180409319684641097 14604954885306989763480823)
  ·
    refine ⟨21907432327960484645221235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604954885306989763480823 21907432327960484645221235)
    ·
      refine ⟨32861148491940726967831853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21907432327960484645221235 32861148491940726967831853)
      ·
        refine ⟨12322930684477772612936945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32861148491940726967831853 12322930684477772612936945)
        ·
          refine ⟨9242198013358329459702709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12322930684477772612936945 9242198013358329459702709)
          ·
            refine ⟨866456063752343386847129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9242198013358329459702709 866456063752343386847129)
            ·
              refine ⟨649842047814257540135347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866456063752343386847129 649842047814257540135347)
              ·
                refine ⟨974763071721386310203021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649842047814257540135347 974763071721386310203021)
                ·
                  refine ⟨365536151895519866326133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974763071721386310203021 365536151895519866326133)
                  ·
                    rfl

theorem cell20_800864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_800864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800864 prefixEnd_800864 := by exact prefixLift 800864
  have htrace : WordTrace (prefixWord ++ tailWord_800864) baseStart_800864 baseEnd_800864 := by
    simpa [prefixWord, tailWord_800864, baseEnd_800864] using wordTrace_append hprefix tailTrace_800864
  have hstable : (prefixWord ++ tailWord_800864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800864).length < 2 ^ (prefixWord ++ tailWord_800864).sum := by decide
  have hdescent : baseEnd_800864 < baseStart_800864 := by decide
  rcases family_descends (prefixWord ++ tailWord_800864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800930 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_800930 : Nat := 118140960795 + 800930 * 2 ^ 59
def prefixEnd_800930 : Nat := 4983230072969 + 3 ^ 40 * 800930 * 2
def baseEnd_800930 : Nat := 365566276093916970125863

theorem tailTrace_800930 : CollatzResearch.WordTrace tailWord_800930 prefixEnd_800930 365566276093916970125863 := by
  unfold tailWord_800930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303079247093718199716061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19474877992249915199242829 7303079247093718199716061)
  ·
    refine ⟨2738654717660144324893523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7303079247093718199716061 2738654717660144324893523)
    ·
      refine ⟨4107982076490216487340285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738654717660144324893523 4107982076490216487340285)
      ·
        refine ⟨1540493278683831182752607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4107982076490216487340285 1540493278683831182752607)
        ·
          refine ⟨2310739918025746774128911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540493278683831182752607 2310739918025746774128911)
          ·
            refine ⟨3466109877038620161193367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310739918025746774128911 3466109877038620161193367)
            ·
              refine ⟨5199164815557930241790051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466109877038620161193367 5199164815557930241790051)
              ·
                refine ⟨7798747223336895362685077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199164815557930241790051 7798747223336895362685077)
                ·
                  refine ⟨365566276093916970125863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7798747223336895362685077 365566276093916970125863)
                  ·
                    rfl

theorem cell20_800930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_800930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800930 prefixEnd_800930 := by exact prefixLift 800930
  have htrace : WordTrace (prefixWord ++ tailWord_800930) baseStart_800930 baseEnd_800930 := by
    simpa [prefixWord, tailWord_800930, baseEnd_800930] using wordTrace_append hprefix tailTrace_800930
  have hstable : (prefixWord ++ tailWord_800930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800930).length < 2 ^ (prefixWord ++ tailWord_800930).sum := by decide
  have hdescent : baseEnd_800930 < baseStart_800930 := by decide
  rcases family_descends (prefixWord ++ tailWord_800930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800978 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_800978 : Nat := 118140960795 + 800978 * 2 ^ 59
def prefixEnd_800978 : Nat := 4983230072969 + 3 ^ 40 * 800978 * 2
def baseEnd_800978 : Nat := 365588184601842136525667

theorem tailTrace_800978 : CollatzResearch.WordTrace tailWord_800978 prefixEnd_800978 365588184601842136525667 := by
  unfold tailWord_800978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303516923050244249152897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19476045128133984664407725 7303516923050244249152897)
  ·
    refine ⟨5477637692287683186864673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7303516923050244249152897 5477637692287683186864673)
    ·
      refine ⟨4108228269215762390148505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5477637692287683186864673 4108228269215762390148505)
      ·
        refine ⟨3081171201911821792611379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108228269215762390148505 3081171201911821792611379)
        ·
          refine ⟨4621756802867732688917069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081171201911821792611379 4621756802867732688917069)
          ·
            refine ⟨1733158801075399758343901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4621756802867732688917069 1733158801075399758343901)
            ·
              refine ⟨649934550403274909378963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1733158801075399758343901 649934550403274909378963)
              ·
                refine ⟨974901825604912364068445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649934550403274909378963 974901825604912364068445)
                ·
                  refine ⟨365588184601842136525667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974901825604912364068445 365588184601842136525667)
                  ·
                    rfl

theorem cell20_800978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_800978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800978 prefixEnd_800978 := by exact prefixLift 800978
  have htrace : WordTrace (prefixWord ++ tailWord_800978) baseStart_800978 baseEnd_800978 := by
    simpa [prefixWord, tailWord_800978, baseEnd_800978] using wordTrace_append hprefix tailTrace_800978
  have hstable : (prefixWord ++ tailWord_800978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800978).length < 2 ^ (prefixWord ++ tailWord_800978).sum := by decide
  have hdescent : baseEnd_800978 < baseStart_800978 := by decide
  rcases family_descends (prefixWord ++ tailWord_800978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800988 : List Nat := [2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_800988 : Nat := 118140960795 + 800988 * 2 ^ 59
def prefixEnd_800988 : Nat := 4983230072969 + 3 ^ 40 * 800988 * 2
def baseEnd_800988 : Nat := 121864249624775515397431

theorem tailTrace_800988 : CollatzResearch.WordTrace tailWord_800988 prefixEnd_800988 121864249624775515397431 := by
  unfold tailWord_800988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607216211082374352237809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19476288281443165802983745 14607216211082374352237809)
  ·
    refine ⟨10955412158311780764178357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14607216211082374352237809 10955412158311780764178357)
    ·
      refine ⟨1027069889841729446641721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10955412158311780764178357 1027069889841729446641721)
      ·
        refine ⟨770302417381297084981291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027069889841729446641721 770302417381297084981291)
        ·
          refine ⟨1155453626071945627471937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770302417381297084981291 1155453626071945627471937)
          ·
            refine ⟨866590219553959220603953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155453626071945627471937 866590219553959220603953)
            ·
              refine ⟨649942664665469415452965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866590219553959220603953 649942664665469415452965)
              ·
                refine ⟨121864249624775515397431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649942664665469415452965 121864249624775515397431)
                ·
                  rfl

theorem cell20_800988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_800988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_800988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_800988 prefixEnd_800988 := by exact prefixLift 800988
  have htrace : WordTrace (prefixWord ++ tailWord_800988) baseStart_800988 baseEnd_800988 := by
    simpa [prefixWord, tailWord_800988, baseEnd_800988] using wordTrace_append hprefix tailTrace_800988
  have hstable : (prefixWord ++ tailWord_800988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800988).length < 2 ^ (prefixWord ++ tailWord_800988).sum := by decide
  have hdescent : baseEnd_800988 < baseStart_800988 := by decide
  rcases family_descends (prefixWord ++ tailWord_800988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801003 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_801003 : Nat := 118140960795 + 801003 * 2 ^ 59
def prefixEnd_801003 : Nat := 4983230072969 + 3 ^ 40 * 801003 * 2
def baseEnd_801003 : Nat := 365599595283053160692231

theorem tailTrace_801003 : CollatzResearch.WordTrace tailWord_801003 prefixEnd_801003 365599595283053160692231 := by
  unfold tailWord_801003
  simp only [CollatzResearch.WordTrace]
  refine ⟨29214979517110406266271663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19476653011406937510847775 29214979517110406266271663)
  ·
    refine ⟨43822469275665609399407495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29214979517110406266271663 43822469275665609399407495)
    ·
      refine ⟨65733703913498414099111243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43822469275665609399407495 65733703913498414099111243)
      ·
        refine ⟨98600555870247621148666865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65733703913498414099111243 98600555870247621148666865)
        ·
          refine ⟨73950416902685715861500149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98600555870247621148666865 73950416902685715861500149)
          ·
            refine ⟨6932851584626785862015639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73950416902685715861500149 6932851584626785862015639)
            ·
              refine ⟨10399277376940178793023459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932851584626785862015639 10399277376940178793023459)
              ·
                refine ⟨15598916065410268189535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399277376940178793023459 15598916065410268189535189)
                ·
                  refine ⟨365599595283053160692231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15598916065410268189535189 365599595283053160692231)
                  ·
                    rfl

theorem cell20_801003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_801003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801003 prefixEnd_801003 := by exact prefixLift 801003
  have htrace : WordTrace (prefixWord ++ tailWord_801003) baseStart_801003 baseEnd_801003 := by
    simpa [prefixWord, tailWord_801003, baseEnd_801003] using wordTrace_append hprefix tailTrace_801003
  have hstable : (prefixWord ++ tailWord_801003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801003).length < 2 ^ (prefixWord ++ tailWord_801003).sum := by decide
  have hdescent : baseEnd_801003 < baseStart_801003 := by decide
  rcases family_descends (prefixWord ++ tailWord_801003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801020 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_801020 : Nat := 118140960795 + 801020 * 2 ^ 59
def prefixEnd_801020 : Nat := 4983230072969 + 3 ^ 40 * 801020 * 2
def baseEnd_801020 : Nat := 365607354546276657125495

theorem tailTrace_801020 : CollatzResearch.WordTrace tailWord_801020 prefixEnd_801020 365607354546276657125495 := by
  unfold tailWord_801020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607799779024409084820257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19477066372032545446427009 14607799779024409084820257)
  ·
    refine ⟨10955849834268306813615193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14607799779024409084820257 10955849834268306813615193)
    ·
      refine ⟨8216887375701230110211395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10955849834268306813615193 8216887375701230110211395)
      ·
        refine ⟨12325331063551845165317093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8216887375701230110211395 12325331063551845165317093)
        ·
          refine ⟨2310999574415970968496955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12325331063551845165317093 2310999574415970968496955)
          ·
            refine ⟨3466499361623956452745433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310999574415970968496955 3466499361623956452745433)
            ·
              refine ⟨2599874521217967339559075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466499361623956452745433 2599874521217967339559075)
              ·
                refine ⟨3899811781826951009338613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599874521217967339559075 3899811781826951009338613)
                ·
                  refine ⟨365607354546276657125495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3899811781826951009338613 365607354546276657125495)
                  ·
                    rfl

theorem cell20_801020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_801020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801020 prefixEnd_801020 := by exact prefixLift 801020
  have htrace : WordTrace (prefixWord ++ tailWord_801020) baseStart_801020 baseEnd_801020 := by
    simpa [prefixWord, tailWord_801020, baseEnd_801020] using wordTrace_append hprefix tailTrace_801020
  have hstable : (prefixWord ++ tailWord_801020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801020).length < 2 ^ (prefixWord ++ tailWord_801020).sum := by decide
  have hdescent : baseEnd_801020 < baseStart_801020 := by decide
  rcases family_descends (prefixWord ++ tailWord_801020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801023 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 2]
def baseStart_801023 : Nat := 118140960795 + 801023 * 2 ^ 59
def prefixEnd_801023 : Nat := 4983230072969 + 3 ^ 40 * 801023 * 2
def baseEnd_801023 : Nat := 365608723828021980025483

theorem tailTrace_801023 : CollatzResearch.WordTrace tailWord_801023 prefixEnd_801023 365608723828021980025483 := by
  unfold tailWord_801023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215708977037949681999723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19477139318025299787999815 29215708977037949681999723)
  ·
    refine ⟨43823563465556924522999585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29215708977037949681999723 43823563465556924522999585)
    ·
      refine ⟨32867672599167693392249689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43823563465556924522999585 32867672599167693392249689)
      ·
        refine ⟨24650754449375770044187267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32867672599167693392249689 24650754449375770044187267)
        ·
          refine ⟨36976131674063655066280901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24650754449375770044187267 36976131674063655066280901)
          ·
            refine ⟨6933024688886935324927669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36976131674063655066280901 6933024688886935324927669)
            ·
              refine ⟨649971064583150186711969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6933024688886935324927669 649971064583150186711969)
              ·
                refine ⟨487478298437362640033977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649971064583150186711969 487478298437362640033977)
                ·
                  refine ⟨365608723828021980025483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487478298437362640033977 365608723828021980025483)
                  ·
                    rfl

theorem cell20_801023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2].length) (baseStart_801023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801023 prefixEnd_801023 := by exact prefixLift 801023
  have htrace : WordTrace (prefixWord ++ tailWord_801023) baseStart_801023 baseEnd_801023 := by
    simpa [prefixWord, tailWord_801023, baseEnd_801023] using wordTrace_append hprefix tailTrace_801023
  have hstable : (prefixWord ++ tailWord_801023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801023).length < 2 ^ (prefixWord ++ tailWord_801023).sum := by decide
  have hdescent : baseEnd_801023 < baseStart_801023 := by decide
  rcases family_descends (prefixWord ++ tailWord_801023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801034 : List Nat := [3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_801034 : Nat := 118140960795 + 801034 * 2 ^ 59
def prefixEnd_801034 : Nat := 4983230072969 + 3 ^ 40 * 801034 * 2
def baseEnd_801034 : Nat := 121871248175918276886257

theorem tailTrace_801034 : CollatzResearch.WordTrace tailWord_801034 prefixEnd_801034 121871248175918276886257 := by
  unfold tailWord_801034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304027544999524640162539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19477406786665399040433437 7304027544999524640162539)
  ·
    refine ⟨10956041317499286960243809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304027544999524640162539 10956041317499286960243809)
    ·
      refine ⟨8217030988124465220182857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10956041317499286960243809 8217030988124465220182857)
      ·
        refine ⟨6162773241093348915137143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217030988124465220182857 6162773241093348915137143)
        ·
          refine ⟨9244159861640023372705715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162773241093348915137143 9244159861640023372705715)
          ·
            refine ⟨13866239792460035059058573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244159861640023372705715 13866239792460035059058573)
            ·
              refine ⟨5199839922172513147146965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13866239792460035059058573 5199839922172513147146965)
              ·
                refine ⟨121871248175918276886257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5199839922172513147146965 121871248175918276886257)
                ·
                  rfl

theorem cell20_801034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_801034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801034 prefixEnd_801034 := by exact prefixLift 801034
  have htrace : WordTrace (prefixWord ++ tailWord_801034) baseStart_801034 baseEnd_801034 := by
    simpa [prefixWord, tailWord_801034, baseEnd_801034] using wordTrace_append hprefix tailTrace_801034
  have hstable : (prefixWord ++ tailWord_801034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801034).length < 2 ^ (prefixWord ++ tailWord_801034).sum := by decide
  have hdescent : baseEnd_801034 < baseStart_801034 := by decide
  rcases family_descends (prefixWord ++ tailWord_801034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801079 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_801079 : Nat := 118140960795 + 801079 * 2 ^ 59
def prefixEnd_801079 : Nat := 4983230072969 + 3 ^ 40 * 801079 * 2
def baseEnd_801079 : Nat := 365634283753934674158587

theorem tailTrace_801079 : CollatzResearch.WordTrace tailWord_801079 prefixEnd_801079 365634283753934674158587 := by
  unfold tailWord_801079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217751464835071246038291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19478500976556714164025527 29217751464835071246038291)
  ·
    refine ⟨43826627197252606869057437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217751464835071246038291 43826627197252606869057437)
    ·
      refine ⟨16434985198969727575896539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43826627197252606869057437 16434985198969727575896539)
      ·
        refine ⟨24652477798454591363844809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434985198969727575896539 24652477798454591363844809)
        ·
          refine ⟨18489358348840943522883607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24652477798454591363844809 18489358348840943522883607)
          ·
            refine ⟨27734037523261415284325411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489358348840943522883607 27734037523261415284325411)
            ·
              refine ⟨41601056284892122926488117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27734037523261415284325411 41601056284892122926488117)
              ·
                refine ⟨3900099026708636524358261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41601056284892122926488117 3900099026708636524358261)
                ·
                  refine ⟨365634283753934674158587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3900099026708636524358261 365634283753934674158587)
                  ·
                    rfl

theorem cell20_801079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_801079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801079 prefixEnd_801079 := by exact prefixLift 801079
  have htrace : WordTrace (prefixWord ++ tailWord_801079) baseStart_801079 baseEnd_801079 := by
    simpa [prefixWord, tailWord_801079, baseEnd_801079] using wordTrace_append hprefix tailTrace_801079
  have hstable : (prefixWord ++ tailWord_801079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801079).length < 2 ^ (prefixWord ++ tailWord_801079).sum := by decide
  have hdescent : baseEnd_801079 < baseStart_801079 := by decide
  rcases family_descends (prefixWord ++ tailWord_801079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801096 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_801096 : Nat := 118140960795 + 801096 * 2 ^ 59
def prefixEnd_801096 : Nat := 4983230072969 + 3 ^ 40 * 801096 * 2
def baseEnd_801096 : Nat := 365642043017158170591851

theorem tailTrace_801096 : CollatzResearch.WordTrace tailWord_801096 prefixEnd_801096 365642043017158170591851 := by
  unfold tailWord_801096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609185752886741574703571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19478914337182322099604761 14609185752886741574703571)
  ·
    refine ⟨21913778629330112362055357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609185752886741574703571 21913778629330112362055357)
    ·
      refine ⟨8217666985998792135770759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21913778629330112362055357 8217666985998792135770759)
      ·
        refine ⟨12326500478998188203656139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217666985998792135770759 12326500478998188203656139)
        ·
          refine ⟨18489750718497282305484209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326500478998188203656139 18489750718497282305484209)
          ·
            refine ⟨13867313038872961729113157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18489750718497282305484209 13867313038872961729113157)
            ·
              refine ⟨2600121194788680324208717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13867313038872961729113157 2600121194788680324208717)
              ·
                refine ⟨975045448045755121578269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600121194788680324208717 975045448045755121578269)
                ·
                  refine ⟨365642043017158170591851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975045448045755121578269 365642043017158170591851)
                  ·
                    rfl

theorem cell20_801096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_801096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801096 prefixEnd_801096 := by exact prefixLift 801096
  have htrace : WordTrace (prefixWord ++ tailWord_801096) baseStart_801096 baseEnd_801096 := by
    simpa [prefixWord, tailWord_801096, baseEnd_801096] using wordTrace_append hprefix tailTrace_801096
  have hstable : (prefixWord ++ tailWord_801096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801096).length < 2 ^ (prefixWord ++ tailWord_801096).sum := by decide
  have hdescent : baseEnd_801096 < baseStart_801096 := by decide
  rcases family_descends (prefixWord ++ tailWord_801096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801130 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_801130 : Nat := 118140960795 + 801130 * 2 ^ 59
def prefixEnd_801130 : Nat := 4983230072969 + 3 ^ 40 * 801130 * 2
def baseEnd_801130 : Nat := 365657561543605163458379

theorem tailTrace_801130 : CollatzResearch.WordTrace tailWord_801130 prefixEnd_801130 365657561543605163458379 := by
  unfold tailWord_801130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304902896912576739036211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19479741058433537970763229 7304902896912576739036211)
  ·
    refine ⟨10957354345368865108554317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304902896912576739036211 10957354345368865108554317)
    ·
      refine ⟨4109007879513324415707869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10957354345368865108554317 4109007879513324415707869)
      ·
        refine ⟨1540877954817496655890451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4109007879513324415707869 1540877954817496655890451)
        ·
          refine ⟨2311316932226244983835677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540877954817496655890451 2311316932226244983835677)
          ·
            refine ⟨866743849584841868938379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2311316932226244983835677 866743849584841868938379)
            ·
              refine ⟨1300115774377262803407569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866743849584841868938379 1300115774377262803407569)
              ·
                refine ⟨975086830782947102555677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300115774377262803407569 975086830782947102555677)
                ·
                  refine ⟨365657561543605163458379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975086830782947102555677 365657561543605163458379)
                  ·
                    rfl

theorem cell20_801130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_801130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801130 prefixEnd_801130 := by exact prefixLift 801130
  have htrace : WordTrace (prefixWord ++ tailWord_801130) baseStart_801130 baseEnd_801130 := by
    simpa [prefixWord, tailWord_801130, baseEnd_801130] using wordTrace_append hprefix tailTrace_801130
  have hstable : (prefixWord ++ tailWord_801130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801130).length < 2 ^ (prefixWord ++ tailWord_801130).sum := by decide
  have hdescent : baseEnd_801130 < baseStart_801130 := by decide
  rcases family_descends (prefixWord ++ tailWord_801130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801182 : List Nat := [4, 3, 1, 2, 1, 3, 6]
def baseStart_801182 : Nat := 118140960795 + 801182 * 2 ^ 59
def prefixEnd_801182 : Nat := 4983230072969 + 3 ^ 40 * 801182 * 2
def baseEnd_801182 : Nat := 40631255084502677080537

theorem tailTrace_801182 : CollatzResearch.WordTrace tailWord_801182 prefixEnd_801182 40631255084502677080537 := by
  unfold tailWord_801182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652688522932739979629725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19481005455641279891358533 3652688522932739979629725)
  ·
    refine ⟨1369758196099777492361147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3652688522932739979629725 1369758196099777492361147)
    ·
      refine ⟨2054637294149666238541721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369758196099777492361147 2054637294149666238541721)
      ·
        refine ⟨1540977970612249678906291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2054637294149666238541721 1540977970612249678906291)
        ·
          refine ⟨2311466955918374518359437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540977970612249678906291 2311466955918374518359437)
          ·
            refine ⟨866800108469390444384789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2311466955918374518359437 866800108469390444384789)
            ·
              refine ⟨40631255084502677080537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 866800108469390444384789 40631255084502677080537)
              ·
                rfl

theorem cell20_801182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_801182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801182 prefixEnd_801182 := by exact prefixLift 801182
  have htrace : WordTrace (prefixWord ++ tailWord_801182) baseStart_801182 baseEnd_801182 := by
    simpa [prefixWord, tailWord_801182, baseEnd_801182] using wordTrace_append hprefix tailTrace_801182
  have hstable : (prefixWord ++ tailWord_801182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801182).length < 2 ^ (prefixWord ++ tailWord_801182).sum := by decide
  have hdescent : baseEnd_801182 < baseStart_801182 := by decide
  rcases family_descends (prefixWord ++ tailWord_801182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801224 : List Nat := [2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_801224 : Nat := 118140960795 + 801224 * 2 ^ 59
def prefixEnd_801224 : Nat := 4983230072969 + 3 ^ 40 * 801224 * 2
def baseEnd_801224 : Nat := 121900155234986204774887

theorem tailTrace_801224 : CollatzResearch.WordTrace tailWord_801224 prefixEnd_801224 121900155234986204774887 := by
  unfold tailWord_801224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611520024654880505033363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19482026699539840673377817 14611520024654880505033363)
  ·
    refine ⟨21917280036982320757550045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14611520024654880505033363 21917280036982320757550045)
    ·
      refine ⟨8218980013868370284081267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21917280036982320757550045 8218980013868370284081267)
      ·
        refine ⟨12328470020802555426121901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218980013868370284081267 12328470020802555426121901)
        ·
          refine ⟨4623176257800958284795713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12328470020802555426121901 4623176257800958284795713)
          ·
            refine ⟨3467382193350718713596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4623176257800958284795713 3467382193350718713596785)
            ·
              refine ⟨2600536645013039035197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467382193350718713596785 2600536645013039035197589)
              ·
                refine ⟨121900155234986204774887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2600536645013039035197589 121900155234986204774887)
                ·
                  rfl

theorem cell20_801224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_801224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801224 prefixEnd_801224 := by exact prefixLift 801224
  have htrace : WordTrace (prefixWord ++ tailWord_801224) baseStart_801224 baseEnd_801224 := by
    simpa [prefixWord, tailWord_801224, baseEnd_801224] using wordTrace_append hprefix tailTrace_801224
  have hstable : (prefixWord ++ tailWord_801224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801224).length < 2 ^ (prefixWord ++ tailWord_801224).sum := by decide
  have hdescent : baseEnd_801224 < baseStart_801224 := by decide
  rcases family_descends (prefixWord ++ tailWord_801224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801248 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_801248 : Nat := 118140960795 + 801248 * 2 ^ 59
def prefixEnd_801248 : Nat := 4983230072969 + 3 ^ 40 * 801248 * 2
def baseEnd_801248 : Nat := 365711419958921197524563

theorem tailTrace_801248 : CollatzResearch.WordTrace tailWord_801248 prefixEnd_801248 365711419958921197524563 := by
  unfold tailWord_801248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611957700611406554470199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19482610267481875405960265 14611957700611406554470199)
  ·
    refine ⟨21917936550917109831705299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14611957700611406554470199 21917936550917109831705299)
    ·
      refine ⟨32876904826375664747557949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21917936550917109831705299 32876904826375664747557949)
      ·
        refine ⟨12328839309890874280334231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32876904826375664747557949 12328839309890874280334231)
        ·
          refine ⟨18493258964836311420501347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12328839309890874280334231 18493258964836311420501347)
          ·
            refine ⟨27739888447254467130752021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18493258964836311420501347 27739888447254467130752021)
            ·
              refine ⟨1300307270965053146754001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27739888447254467130752021 1300307270965053146754001)
              ·
                refine ⟨975230453223789860065501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300307270965053146754001 975230453223789860065501)
                ·
                  refine ⟨365711419958921197524563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975230453223789860065501 365711419958921197524563)
                  ·
                    rfl

theorem cell20_801248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_801248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801248 prefixEnd_801248 := by exact prefixLift 801248
  have htrace : WordTrace (prefixWord ++ tailWord_801248) baseStart_801248 baseEnd_801248 := by
    simpa [prefixWord, tailWord_801248, baseEnd_801248] using wordTrace_append hprefix tailTrace_801248
  have hstable : (prefixWord ++ tailWord_801248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801248).length < 2 ^ (prefixWord ++ tailWord_801248).sum := by decide
  have hdescent : baseEnd_801248 < baseStart_801248 := by decide
  rcases family_descends (prefixWord ++ tailWord_801248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801251 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 2]
def baseStart_801251 : Nat := 118140960795 + 801251 * 2 ^ 59
def prefixEnd_801251 : Nat := 4983230072969 + 3 ^ 40 * 801251 * 2
def baseEnd_801251 : Nat := 365712789240666520424551

theorem tailTrace_801251 : CollatzResearch.WordTrace tailWord_801251 prefixEnd_801251 365712789240666520424551 := by
  unfold tailWord_801251
  simp only [CollatzResearch.WordTrace]
  refine ⟨29224024820211944621299607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19482683213474629747533071 29224024820211944621299607)
  ·
    refine ⟨43836037230317916931949411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29224024820211944621299607 43836037230317916931949411)
    ·
      refine ⟨65754055845476875397924117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43836037230317916931949411 65754055845476875397924117)
      ·
        refine ⟨3082221367756728534277693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65754055845476875397924117 3082221367756728534277693)
        ·
          refine ⟨1155833012908773200354135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3082221367756728534277693 1155833012908773200354135)
          ·
            refine ⟨1733749519363159800531203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155833012908773200354135 1733749519363159800531203)
            ·
              refine ⟨2600624279044739700796805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733749519363159800531203 2600624279044739700796805)
              ·
                refine ⟨487617052320888693899401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2600624279044739700796805 487617052320888693899401)
                ·
                  refine ⟨365712789240666520424551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487617052320888693899401 365712789240666520424551)
                  ·
                    rfl

theorem cell20_801251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2].length) (baseStart_801251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801251 prefixEnd_801251 := by exact prefixLift 801251
  have htrace : WordTrace (prefixWord ++ tailWord_801251) baseStart_801251 baseEnd_801251 := by
    simpa [prefixWord, tailWord_801251, baseEnd_801251] using wordTrace_append hprefix tailTrace_801251
  have hstable : (prefixWord ++ tailWord_801251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801251).length < 2 ^ (prefixWord ++ tailWord_801251).sum := by decide
  have hdescent : baseEnd_801251 < baseStart_801251 := by decide
  rcases family_descends (prefixWord ++ tailWord_801251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801255 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_801255 : Nat := 118140960795 + 801255 * 2 ^ 59
def prefixEnd_801255 : Nat := 4983230072969 + 3 ^ 40 * 801255 * 2
def baseEnd_801255 : Nat := 365714614949660284291201

theorem tailTrace_801255 : CollatzResearch.WordTrace tailWord_801255 prefixEnd_801255 365714614949660284291201 := by
  unfold tailWord_801255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29224170712197453304445219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19482780474798302202963479 29224170712197453304445219)
  ·
    refine ⟨43836256068296179956667829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29224170712197453304445219 43836256068296179956667829)
    ·
      refine ⟨4109649006402766870937609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43836256068296179956667829 4109649006402766870937609)
      ·
        refine ⟨3082236754802075153203207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4109649006402766870937609 3082236754802075153203207)
        ·
          refine ⟨4623355132203112729804811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082236754802075153203207 4623355132203112729804811)
          ·
            refine ⟨6935032698304669094707217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623355132203112729804811 6935032698304669094707217)
            ·
              refine ⟨5201274523728501821030413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935032698304669094707217 5201274523728501821030413)
              ·
                refine ⟨1950477946398188182886405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5201274523728501821030413 1950477946398188182886405)
                ·
                  refine ⟨365714614949660284291201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950477946398188182886405 365714614949660284291201)
                  ·
                    rfl

theorem cell20_801255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_801255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801255 prefixEnd_801255 := by exact prefixLift 801255
  have htrace : WordTrace (prefixWord ++ tailWord_801255) baseStart_801255 baseEnd_801255 := by
    simpa [prefixWord, tailWord_801255, baseEnd_801255] using wordTrace_append hprefix tailTrace_801255
  have hstable : (prefixWord ++ tailWord_801255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801255).length < 2 ^ (prefixWord ++ tailWord_801255).sum := by decide
  have hdescent : baseEnd_801255 < baseStart_801255 := by decide
  rcases family_descends (prefixWord ++ tailWord_801255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801303 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_801303 : Nat := 118140960795 + 801303 * 2 ^ 59
def prefixEnd_801303 : Nat := 4983230072969 + 3 ^ 40 * 801303 * 2
def baseEnd_801303 : Nat := 365736523457585450691005

theorem tailTrace_801303 : CollatzResearch.WordTrace tailWord_801303 prefixEnd_801303 365736523457585450691005 := by
  unfold tailWord_801303
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225921416023557502192563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19483947610682371668128375 29225921416023557502192563)
  ·
    refine ⟨43838882124035336253288845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29225921416023557502192563 43838882124035336253288845)
    ·
      refine ⟨16439580796513251094983317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43838882124035336253288845 16439580796513251094983317)
      ·
        refine ⟨770605349836558645077343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16439580796513251094983317 770605349836558645077343)
        ·
          refine ⟨1155908024754837967616015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770605349836558645077343 1155908024754837967616015)
          ·
            refine ⟨1733862037132256951424023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155908024754837967616015 1733862037132256951424023)
            ·
              refine ⟨2600793055698385427136035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733862037132256951424023 2600793055698385427136035)
              ·
                refine ⟨3901189583547578140704053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600793055698385427136035 3901189583547578140704053)
                ·
                  refine ⟨365736523457585450691005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3901189583547578140704053 365736523457585450691005)
                  ·
                    rfl

theorem cell20_801303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_801303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801303 prefixEnd_801303 := by exact prefixLift 801303
  have htrace : WordTrace (prefixWord ++ tailWord_801303) baseStart_801303 baseEnd_801303 := by
    simpa [prefixWord, tailWord_801303, baseEnd_801303] using wordTrace_append hprefix tailTrace_801303
  have hstable : (prefixWord ++ tailWord_801303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801303).length < 2 ^ (prefixWord ++ tailWord_801303).sum := by decide
  have hdescent : baseEnd_801303 < baseStart_801303 := by decide
  rcases family_descends (prefixWord ++ tailWord_801303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801320 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_801320 : Nat := 118140960795 + 801320 * 2 ^ 59
def prefixEnd_801320 : Nat := 4983230072969 + 3 ^ 40 * 801320 * 2
def baseEnd_801320 : Nat := 365744282720808947124269

theorem tailTrace_801320 : CollatzResearch.WordTrace tailWord_801320 prefixEnd_801320 365744282720808947124269 := by
  unfold tailWord_801320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613270728480984702780707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19484360971307979603707609 14613270728480984702780707)
  ·
    refine ⟨21919906092721477054171061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14613270728480984702780707 21919906092721477054171061)
    ·
      refine ⟨2054991196192638473828537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21919906092721477054171061 2054991196192638473828537)
      ·
        refine ⟨1541243397144478855371403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2054991196192638473828537 1541243397144478855371403)
        ·
          refine ⟨2311865095716718283057105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541243397144478855371403 2311865095716718283057105)
          ·
            refine ⟨1733898821787538712292829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2311865095716718283057105 1733898821787538712292829)
            ·
              refine ⟨650212058170327017109811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1733898821787538712292829 650212058170327017109811)
              ·
                refine ⟨975318087255490525664717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650212058170327017109811 975318087255490525664717)
                ·
                  refine ⟨365744282720808947124269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975318087255490525664717 365744282720808947124269)
                  ·
                    rfl

theorem cell20_801320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_801320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801320 prefixEnd_801320 := by exact prefixLift 801320
  have htrace : WordTrace (prefixWord ++ tailWord_801320) baseStart_801320 baseEnd_801320 := by
    simpa [prefixWord, tailWord_801320, baseEnd_801320] using wordTrace_append hprefix tailTrace_801320
  have hstable : (prefixWord ++ tailWord_801320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801320).length < 2 ^ (prefixWord ++ tailWord_801320).sum := by decide
  have hdescent : baseEnd_801320 < baseStart_801320 := by decide
  rcases family_descends (prefixWord ++ tailWord_801320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801334 : List Nat := [5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_801334 : Nat := 118140960795 + 801334 * 2 ^ 59
def prefixEnd_801334 : Nat := 4983230072969 + 3 ^ 40 * 801334 * 2
def baseEnd_801334 : Nat := 121916890900762373552515

theorem tailTrace_801334 : CollatzResearch.WordTrace tailWord_801334 prefixEnd_801334 121916890900762373552515 := by
  unfold tailWord_801334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826690754931953112285691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19484701385940833197714037 1826690754931953112285691)
  ·
    refine ⟨2740036132397929668428537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826690754931953112285691 2740036132397929668428537)
    ·
      refine ⟨2055027099298447251321403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740036132397929668428537 2055027099298447251321403)
      ·
        refine ⟨3082540648947670876982105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055027099298447251321403 3082540648947670876982105)
        ·
          refine ⟨2311905486710753157736579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3082540648947670876982105 2311905486710753157736579)
          ·
            refine ⟨3467858230066129736604869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311905486710753157736579 3467858230066129736604869)
            ·
              refine ⟨650223418137399325613413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3467858230066129736604869 650223418137399325613413)
              ·
                refine ⟨121916890900762373552515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650223418137399325613413 121916890900762373552515)
                ·
                  rfl

theorem cell20_801334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_801334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801334 prefixEnd_801334 := by exact prefixLift 801334
  have htrace : WordTrace (prefixWord ++ tailWord_801334) baseStart_801334 baseEnd_801334 := by
    simpa [prefixWord, tailWord_801334, baseEnd_801334] using wordTrace_append hprefix tailTrace_801334
  have hstable : (prefixWord ++ tailWord_801334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801334).length < 2 ^ (prefixWord ++ tailWord_801334).sum := by decide
  have hdescent : baseEnd_801334 < baseStart_801334 := by decide
  rcases family_descends (prefixWord ++ tailWord_801334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801338 : List Nat := [3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_801338 : Nat := 118140960795 + 801338 * 2 ^ 59
def prefixEnd_801338 : Nat := 4983230072969 + 3 ^ 40 * 801338 * 2
def baseEnd_801338 : Nat := 121917499470426961508065

theorem tailTrace_801338 : CollatzResearch.WordTrace tailWord_801338 prefixEnd_801338 121917499470426961508065 := by
  unfold tailWord_801338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306799492724189619929167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19484798647264505653144445 7306799492724189619929167)
  ·
    refine ⟨10960199239086284429893751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7306799492724189619929167 10960199239086284429893751)
    ·
      refine ⟨16440298858629426644840627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10960199239086284429893751 16440298858629426644840627)
      ·
        refine ⟨24660448287944139967260941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16440298858629426644840627 24660448287944139967260941)
        ·
          refine ⟨9247668107979052487722853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24660448287944139967260941 9247668107979052487722853)
          ·
            refine ⟨1733937770246072341448035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9247668107979052487722853 1733937770246072341448035)
            ·
              refine ⟨2600906655369108512172053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733937770246072341448035 2600906655369108512172053)
              ·
                refine ⟨121917499470426961508065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2600906655369108512172053 121917499470426961508065)
                ·
                  rfl

theorem cell20_801338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_801338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801338 prefixEnd_801338 := by exact prefixLift 801338
  have htrace : WordTrace (prefixWord ++ tailWord_801338) baseStart_801338 baseEnd_801338 := by
    simpa [prefixWord, tailWord_801338, baseEnd_801338] using wordTrace_append hprefix tailTrace_801338
  have hstable : (prefixWord ++ tailWord_801338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801338).length < 2 ^ (prefixWord ++ tailWord_801338).sum := by decide
  have hdescent : baseEnd_801338 < baseStart_801338 := by decide
  rcases family_descends (prefixWord ++ tailWord_801338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801352 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_801352 : Nat := 118140960795 + 801352 * 2 ^ 59
def prefixEnd_801352 : Nat := 4983230072969 + 3 ^ 40 * 801352 * 2
def baseEnd_801352 : Nat := 365758888392759058057471

theorem tailTrace_801352 : CollatzResearch.WordTrace tailWord_801352 prefixEnd_801352 365758888392759058057471 := by
  unfold tailWord_801352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613854296423019435363155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19485139061897359247150873 14613854296423019435363155)
  ·
    refine ⟨21920781444634529153044733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14613854296423019435363155 21920781444634529153044733)
    ·
      refine ⟨8220293041737948432391775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21920781444634529153044733 8220293041737948432391775)
      ·
        refine ⟨12330439562606922648587663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220293041737948432391775 12330439562606922648587663)
        ·
          refine ⟨18495659343910383972881495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12330439562606922648587663 18495659343910383972881495)
          ·
            refine ⟨27743489015865575959322243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18495659343910383972881495 27743489015865575959322243)
            ·
              refine ⟨41615233523798363938983365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27743489015865575959322243 41615233523798363938983365)
              ·
                refine ⟨7802856285712193238559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41615233523798363938983365 7802856285712193238559381)
                ·
                  refine ⟨365758888392759058057471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7802856285712193238559381 365758888392759058057471)
                  ·
                    rfl

theorem cell20_801352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_801352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801352 prefixEnd_801352 := by exact prefixLift 801352
  have htrace : WordTrace (prefixWord ++ tailWord_801352) baseStart_801352 baseEnd_801352 := by
    simpa [prefixWord, tailWord_801352, baseEnd_801352] using wordTrace_append hprefix tailTrace_801352
  have hstable : (prefixWord ++ tailWord_801352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801352).length < 2 ^ (prefixWord ++ tailWord_801352).sum := by decide
  have hdescent : baseEnd_801352 < baseStart_801352 := by decide
  rcases family_descends (prefixWord ++ tailWord_801352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801359 : List Nat := [1, 1, 2, 1, 1, 2, 12]
def baseStart_801359 : Nat := 118140960795 + 801359 * 2 ^ 59
def prefixEnd_801359 : Nat := 4983230072969 + 3 ^ 40 * 801359 * 2
def baseEnd_801359 : Nat := 40640231487055349424901

theorem tailTrace_801359 : CollatzResearch.WordTrace tailWord_801359 prefixEnd_801359 40640231487055349424901 := by
  unfold tailWord_801359
  simp only [CollatzResearch.WordTrace]
  refine ⟨29227963903820679066231131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19485309269213786044154087 29227963903820679066231131)
  ·
    refine ⟨43841945855731018599346697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29227963903820679066231131 43841945855731018599346697)
    ·
      refine ⟨32881459391798263949510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43841945855731018599346697 32881459391798263949510023)
      ·
        refine ⟨49322189087697395924265035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32881459391798263949510023 49322189087697395924265035)
        ·
          refine ⟨73983283631546093886397553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49322189087697395924265035 73983283631546093886397553)
          ·
            refine ⟨55487462723659570414798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73983283631546093886397553 55487462723659570414798165)
            ·
              refine ⟨40640231487055349424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55487462723659570414798165 40640231487055349424901)
              ·
                rfl

theorem cell20_801359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_801359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801359 prefixEnd_801359 := by exact prefixLift 801359
  have htrace : WordTrace (prefixWord ++ tailWord_801359) baseStart_801359 baseEnd_801359 := by
    simpa [prefixWord, tailWord_801359, baseEnd_801359] using wordTrace_append hprefix tailTrace_801359
  have hstable : (prefixWord ++ tailWord_801359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801359).length < 2 ^ (prefixWord ++ tailWord_801359).sum := by decide
  have hdescent : baseEnd_801359 < baseStart_801359 := by decide
  rcases family_descends (prefixWord ++ tailWord_801359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801362 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_801362 : Nat := 118140960795 + 801362 * 2 ^ 59
def prefixEnd_801362 : Nat := 4983230072969 + 3 ^ 40 * 801362 * 2
def baseEnd_801362 : Nat := 365763452665243467724097

theorem tailTrace_801362 : CollatzResearch.WordTrace tailWord_801362 prefixEnd_801362 365763452665243467724097 := by
  unfold tailWord_801362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307018330702452644647585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19485382215206540385726893 7307018330702452644647585)
  ·
    refine ⟨5480263748026839483485689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7307018330702452644647585 5480263748026839483485689)
    ·
      refine ⟨4110197811020129612614267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5480263748026839483485689 4110197811020129612614267)
      ·
        refine ⟨6165296716530194418921401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110197811020129612614267 6165296716530194418921401)
        ·
          refine ⟨4623972537397645814191051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165296716530194418921401 4623972537397645814191051)
          ·
            refine ⟨6935958806096468721286577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623972537397645814191051 6935958806096468721286577)
            ·
              refine ⟨5201969104572351540964933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935958806096468721286577 5201969104572351540964933)
              ·
                refine ⟨975369207107315913930925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5201969104572351540964933 975369207107315913930925)
                ·
                  refine ⟨365763452665243467724097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975369207107315913930925 365763452665243467724097)
                  ·
                    rfl

theorem cell20_801362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_801362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801362 prefixEnd_801362 := by exact prefixLift 801362
  have htrace : WordTrace (prefixWord ++ tailWord_801362) baseStart_801362 baseEnd_801362 := by
    simpa [prefixWord, tailWord_801362, baseEnd_801362] using wordTrace_append hprefix tailTrace_801362
  have hstable : (prefixWord ++ tailWord_801362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801362).length < 2 ^ (prefixWord ++ tailWord_801362).sum := by decide
  have hdescent : baseEnd_801362 < baseStart_801362 := by decide
  rcases family_descends (prefixWord ++ tailWord_801362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801410 : List Nat := [3, 4, 3, 1, 9]
def baseStart_801410 : Nat := 118140960795 + 801410 * 2 ^ 59
def prefixEnd_801410 : Nat := 4983230072969 + 3 ^ 40 * 801410 * 2
def baseEnd_801410 : Nat := 4515868656458872026221

theorem tailTrace_801410 : CollatzResearch.WordTrace tailWord_801410 prefixEnd_801410 4515868656458872026221 := by
  unfold tailWord_801410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307456006658978694084421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19486549351090609850891789 7307456006658978694084421)
  ·
    refine ⟨1370148001248558505140829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7307456006658978694084421 1370148001248558505140829)
    ·
      refine ⟨513805500468209439427811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1370148001248558505140829 513805500468209439427811)
      ·
        refine ⟨770708250702314159141717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513805500468209439427811 770708250702314159141717)
        ·
          refine ⟨4515868656458872026221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 770708250702314159141717 4515868656458872026221)
          ·
            rfl

theorem cell20_801410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 9].length) (baseStart_801410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801410 prefixEnd_801410 := by exact prefixLift 801410
  have htrace : WordTrace (prefixWord ++ tailWord_801410) baseStart_801410 baseEnd_801410 := by
    simpa [prefixWord, tailWord_801410, baseEnd_801410] using wordTrace_append hprefix tailTrace_801410
  have hstable : (prefixWord ++ tailWord_801410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801410).length < 2 ^ (prefixWord ++ tailWord_801410).sum := by decide
  have hdescent : baseEnd_801410 < baseStart_801410 := by decide
  rcases family_descends (prefixWord ++ tailWord_801410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801466 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_801466 : Nat := 118140960795 + 801466 * 2 ^ 59
def prefixEnd_801466 : Nat := 4983230072969 + 3 ^ 40 * 801466 * 2
def baseEnd_801466 : Nat := 365810921099081328257005

theorem tailTrace_801466 : CollatzResearch.WordTrace tailWord_801466 prefixEnd_801466 365810921099081328257005 := by
  unfold tailWord_801466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307966628608259085094063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19487911009622024226917501 7307966628608259085094063)
  ·
    refine ⟨10961949942912388627641095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307966628608259085094063 10961949942912388627641095)
    ·
      refine ⟨16442924914368582941461643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961949942912388627641095 16442924914368582941461643)
      ·
        refine ⟨24664387371552874412192465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16442924914368582941461643 24664387371552874412192465)
        ·
          refine ⟨18498290528664655809144349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24664387371552874412192465 18498290528664655809144349)
          ·
            refine ⟨6936858948249245928429131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18498290528664655809144349 6936858948249245928429131)
            ·
              refine ⟨10405288422373868892643697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936858948249245928429131 10405288422373868892643697)
              ·
                refine ⟨7803966316780401669482773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10405288422373868892643697 7803966316780401669482773)
                ·
                  refine ⟨365810921099081328257005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7803966316780401669482773 365810921099081328257005)
                  ·
                    rfl

theorem cell20_801466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_801466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801466 prefixEnd_801466 := by exact prefixLift 801466
  have htrace : WordTrace (prefixWord ++ tailWord_801466) baseStart_801466 baseEnd_801466 := by
    simpa [prefixWord, tailWord_801466, baseEnd_801466] using wordTrace_append hprefix tailTrace_801466
  have hstable : (prefixWord ++ tailWord_801466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801466).length < 2 ^ (prefixWord ++ tailWord_801466).sum := by decide
  have hdescent : baseEnd_801466 < baseStart_801466 := by decide
  rcases family_descends (prefixWord ++ tailWord_801466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801476 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_801476 : Nat := 118140960795 + 801476 * 2 ^ 59
def prefixEnd_801476 : Nat := 4983230072969 + 3 ^ 40 * 801476 * 2
def baseEnd_801476 : Nat := 365815485371565737923631

theorem tailTrace_801476 : CollatzResearch.WordTrace tailWord_801476 prefixEnd_801476 365815485371565737923631 := by
  unfold tailWord_801476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616115622198404024120141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19488154162931205365493521 14616115622198404024120141)
  ·
    refine ⟨5481043358324401509045053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14616115622198404024120141 5481043358324401509045053)
    ·
      refine ⟨2055391259371650565891895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5481043358324401509045053 2055391259371650565891895)
      ·
        refine ⟨3083086889057475848837843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055391259371650565891895 3083086889057475848837843)
        ·
          refine ⟨4624630333586213773256765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083086889057475848837843 4624630333586213773256765)
          ·
            refine ⟨1734236375094830164971287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4624630333586213773256765 1734236375094830164971287)
            ·
              refine ⟨2601354562642245247456931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734236375094830164971287 2601354562642245247456931)
              ·
                refine ⟨3902031843963367871185397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601354562642245247456931 3902031843963367871185397)
                ·
                  refine ⟨365815485371565737923631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902031843963367871185397 365815485371565737923631)
                  ·
                    rfl

theorem cell20_801476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_801476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801476 prefixEnd_801476 := by exact prefixLift 801476
  have htrace : WordTrace (prefixWord ++ tailWord_801476) baseStart_801476 baseEnd_801476 := by
    simpa [prefixWord, tailWord_801476, baseEnd_801476] using wordTrace_append hprefix tailTrace_801476
  have hstable : (prefixWord ++ tailWord_801476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801476).length < 2 ^ (prefixWord ++ tailWord_801476).sum := by decide
  have hdescent : baseEnd_801476 < baseStart_801476 := by decide
  rcases family_descends (prefixWord ++ tailWord_801476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801500 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_801500 : Nat := 118140960795 + 801500 * 2 ^ 59
def prefixEnd_801500 : Nat := 4983230072969 + 3 ^ 40 * 801500 * 2
def baseEnd_801500 : Nat := 365826439625528321123533

theorem tailTrace_801500 : CollatzResearch.WordTrace tailWord_801500 prefixEnd_801500 365826439625528321123533 := by
  unfold tailWord_801500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616553298154930073556977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19488737730873240098075969 14616553298154930073556977)
  ·
    refine ⟨10962414973616197555167733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14616553298154930073556977 10962414973616197555167733)
    ·
      refine ⟨1027726403776518520796975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10962414973616197555167733 1027726403776518520796975)
      ·
        refine ⟨1541589605664777781195463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027726403776518520796975 1541589605664777781195463)
        ·
          refine ⟨2312384408497166671793195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541589605664777781195463 2312384408497166671793195)
          ·
            refine ⟨3468576612745750007689793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312384408497166671793195 3468576612745750007689793)
            ·
              refine ⟨2601432459559312505767345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468576612745750007689793 2601432459559312505767345)
              ·
                refine ⟨1951074344669484379325509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601432459559312505767345 1951074344669484379325509)
                ·
                  refine ⟨365826439625528321123533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951074344669484379325509 365826439625528321123533)
                  ·
                    rfl

theorem cell20_801500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_801500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801500 prefixEnd_801500 := by exact prefixLift 801500
  have htrace : WordTrace (prefixWord ++ tailWord_801500) baseStart_801500 baseEnd_801500 := by
    simpa [prefixWord, tailWord_801500, baseEnd_801500] using wordTrace_append hprefix tailTrace_801500
  have hstable : (prefixWord ++ tailWord_801500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801500).length < 2 ^ (prefixWord ++ tailWord_801500).sum := by decide
  have hdescent : baseEnd_801500 < baseStart_801500 := by decide
  rcases family_descends (prefixWord ++ tailWord_801500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801507 : List Nat := [1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_801507 : Nat := 118140960795 + 801507 * 2 ^ 59
def prefixEnd_801507 : Nat := 4983230072969 + 3 ^ 40 * 801507 * 2
def baseEnd_801507 : Nat := 121943211538755802630057

theorem tailTrace_801507 : CollatzResearch.WordTrace tailWord_801507 prefixEnd_801507 121943211538755802630057 := by
  unfold tailWord_801507
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233361907284500342618775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19488907938189666895079183 29233361907284500342618775)
  ·
    refine ⟨43850042860926750513928163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29233361907284500342618775 43850042860926750513928163)
    ·
      refine ⟨65775064291390125770892245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43850042860926750513928163 65775064291390125770892245)
      ·
        refine ⟨1541603069329456072755287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65775064291390125770892245 1541603069329456072755287)
        ·
          refine ⟨2312404603994184109132931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541603069329456072755287 2312404603994184109132931)
          ·
            refine ⟨3468606905991276163699397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312404603994184109132931 3468606905991276163699397)
            ·
              refine ⟨650363794873364280693637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3468606905991276163699397 650363794873364280693637)
              ·
                refine ⟨121943211538755802630057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650363794873364280693637 121943211538755802630057)
                ·
                  rfl

theorem cell20_801507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_801507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801507 prefixEnd_801507 := by exact prefixLift 801507
  have htrace : WordTrace (prefixWord ++ tailWord_801507) baseStart_801507 baseEnd_801507 := by
    simpa [prefixWord, tailWord_801507, baseEnd_801507] using wordTrace_append hprefix tailTrace_801507
  have hstable : (prefixWord ++ tailWord_801507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801507).length < 2 ^ (prefixWord ++ tailWord_801507).sum := by decide
  have hdescent : baseEnd_801507 < baseStart_801507 := by decide
  rcases family_descends (prefixWord ++ tailWord_801507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801534 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_801534 : Nat := 118140960795 + 801534 * 2 ^ 59
def prefixEnd_801534 : Nat := 4983230072969 + 3 ^ 40 * 801534 * 2
def baseEnd_801534 : Nat := 365841958151975313990061

theorem tailTrace_801534 : CollatzResearch.WordTrace tailWord_801534 prefixEnd_801534 365841958151975313990061 := by
  unfold tailWord_801534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654293334773335494231457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19489564452124455969234437 3654293334773335494231457)
  ·
    refine ⟨2740720001080001620673593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3654293334773335494231457 2740720001080001620673593)
    ·
      refine ⟨2055540000810001215505195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740720001080001620673593 2055540000810001215505195)
      ·
        refine ⟨3083310001215001823257793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055540000810001215505195 3083310001215001823257793)
        ·
          refine ⟨2312482500911251367443345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3083310001215001823257793 2312482500911251367443345)
          ·
            refine ⟨1734361875683438525582509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312482500911251367443345 1734361875683438525582509)
            ·
              refine ⟨650385703381289447093441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734361875683438525582509 650385703381289447093441)
              ·
                refine ⟨487789277535967085320081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650385703381289447093441 487789277535967085320081)
                ·
                  refine ⟨365841958151975313990061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487789277535967085320081 365841958151975313990061)
                  ·
                    rfl

theorem cell20_801534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_801534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801534 prefixEnd_801534 := by exact prefixLift 801534
  have htrace : WordTrace (prefixWord ++ tailWord_801534) baseStart_801534 baseEnd_801534 := by
    simpa [prefixWord, tailWord_801534, baseEnd_801534] using wordTrace_append hprefix tailTrace_801534
  have hstable : (prefixWord ++ tailWord_801534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801534).length < 2 ^ (prefixWord ++ tailWord_801534).sum := by decide
  have hdescent : baseEnd_801534 < baseStart_801534 := by decide
  rcases family_descends (prefixWord ++ tailWord_801534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801535 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_801535 : Nat := 118140960795 + 801535 * 2 ^ 59
def prefixEnd_801535 : Nat := 4983230072969 + 3 ^ 40 * 801535 * 2
def baseEnd_801535 : Nat := 365842414579223754956723

theorem tailTrace_801535 : CollatzResearch.WordTrace tailWord_801535 prefixEnd_801535 365842414579223754956723 := by
  unfold tailWord_801535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29234383151183061124638059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19489588767455374083092039 29234383151183061124638059)
  ·
    refine ⟨43851574726774591686957089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29234383151183061124638059 43851574726774591686957089)
    ·
      refine ⟨32888681045080943765217817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43851574726774591686957089 32888681045080943765217817)
      ·
        refine ⟨24666510783810707823913363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32888681045080943765217817 24666510783810707823913363)
        ·
          refine ⟨36999766175716061735870045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24666510783810707823913363 36999766175716061735870045)
          ·
            refine ⟨13874912315893523150951267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36999766175716061735870045 13874912315893523150951267)
            ·
              refine ⟨20812368473840284726426901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13874912315893523150951267 20812368473840284726426901)
              ·
                refine ⟨975579772211263346551261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20812368473840284726426901 975579772211263346551261)
                ·
                  refine ⟨365842414579223754956723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975579772211263346551261 365842414579223754956723)
                  ·
                    rfl

theorem cell20_801535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_801535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801535 prefixEnd_801535 := by exact prefixLift 801535
  have htrace : WordTrace (prefixWord ++ tailWord_801535) baseStart_801535 baseEnd_801535 := by
    simpa [prefixWord, tailWord_801535, baseEnd_801535] using wordTrace_append hprefix tailTrace_801535
  have hstable : (prefixWord ++ tailWord_801535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801535).length < 2 ^ (prefixWord ++ tailWord_801535).sum := by decide
  have hdescent : baseEnd_801535 < baseStart_801535 := by decide
  rcases family_descends (prefixWord ++ tailWord_801535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801538 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_801538 : Nat := 118140960795 + 801538 * 2 ^ 59
def prefixEnd_801538 : Nat := 4983230072969 + 3 ^ 40 * 801538 * 2
def baseEnd_801538 : Nat := 365843783860969077856711

theorem tailTrace_801538 : CollatzResearch.WordTrace tailWord_801538 prefixEnd_801538 365843783860969077856711 := by
  unfold tailWord_801538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308623142543048159249317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19489661713448128424664845 7308623142543048159249317)
  ·
    refine ⟨1370366839226821529859247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7308623142543048159249317 1370366839226821529859247)
    ·
      refine ⟨2055550258840232294788871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370366839226821529859247 2055550258840232294788871)
      ·
        refine ⟨3083325388260348442183307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055550258840232294788871 3083325388260348442183307)
        ·
          refine ⟨4624988082390522663274961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083325388260348442183307 4624988082390522663274961)
          ·
            refine ⟨3468741061792891997456221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624988082390522663274961 3468741061792891997456221)
            ·
              refine ⟨1300777898172334499046083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3468741061792891997456221 1300777898172334499046083)
              ·
                refine ⟨1951166847258501748569125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300777898172334499046083 1951166847258501748569125)
                ·
                  refine ⟨365843783860969077856711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951166847258501748569125 365843783860969077856711)
                  ·
                    rfl

theorem cell20_801538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_801538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801538 prefixEnd_801538 := by exact prefixLift 801538
  have htrace : WordTrace (prefixWord ++ tailWord_801538) baseStart_801538 baseEnd_801538 := by
    simpa [prefixWord, tailWord_801538, baseEnd_801538] using wordTrace_append hprefix tailTrace_801538
  have hstable : (prefixWord ++ tailWord_801538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801538).length < 2 ^ (prefixWord ++ tailWord_801538).sum := by decide
  have hdescent : baseEnd_801538 < baseStart_801538 := by decide
  rcases family_descends (prefixWord ++ tailWord_801538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801576 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_801576 : Nat := 118140960795 + 801576 * 2 ^ 59
def prefixEnd_801576 : Nat := 4983230072969 + 3 ^ 40 * 801576 * 2
def baseEnd_801576 : Nat := 365861128096409834589889

theorem tailTrace_801576 : CollatzResearch.WordTrace tailWord_801576 prefixEnd_801576 365861128096409834589889 := by
  unfold tailWord_801576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617939272017262563440291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19490585696023016751253721 14617939272017262563440291)
  ·
    refine ⟨21926908908025893845160437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14617939272017262563440291 21926908908025893845160437)
    ·
      refine ⟨2055647710127427547983791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21926908908025893845160437 2055647710127427547983791)
      ·
        refine ⟨3083471565191141321975687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055647710127427547983791 3083471565191141321975687)
        ·
          refine ⟨4625207347786711982963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083471565191141321975687 4625207347786711982963531)
          ·
            refine ⟨6937811021680067974445297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625207347786711982963531 6937811021680067974445297)
            ·
              refine ⟨5203358266260050980833973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6937811021680067974445297 5203358266260050980833973)
              ·
                refine ⟨487814837461879779453185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5203358266260050980833973 487814837461879779453185)
                ·
                  refine ⟨365861128096409834589889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487814837461879779453185 365861128096409834589889)
                  ·
                    rfl

theorem cell20_801576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_801576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801576 prefixEnd_801576 := by exact prefixLift 801576
  have htrace : WordTrace (prefixWord ++ tailWord_801576) baseStart_801576 baseEnd_801576 := by
    simpa [prefixWord, tailWord_801576, baseEnd_801576] using wordTrace_append hprefix tailTrace_801576
  have hstable : (prefixWord ++ tailWord_801576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801576).length < 2 ^ (prefixWord ++ tailWord_801576).sum := by decide
  have hdescent : baseEnd_801576 < baseStart_801576 := by decide
  rcases family_descends (prefixWord ++ tailWord_801576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801587 : List Nat := [1, 1, 1, 2, 6, 9]
def baseStart_801587 : Nat := 118140960795 + 801587 * 2 ^ 59
def prefixEnd_801587 : Nat := 4983230072969 + 3 ^ 40 * 801587 * 2
def baseEnd_801587 : Nat := 13550598103560840193451

theorem tailTrace_801587 : CollatzResearch.WordTrace tailWord_801587 prefixEnd_801587 13550598103560840193451 := by
  unfold tailWord_801587
  simp only [CollatzResearch.WordTrace]
  refine ⟨29236279746994674005531015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490853164663116003687343 29236279746994674005531015)
  ·
    refine ⟨43854419620492011008296523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29236279746994674005531015 43854419620492011008296523)
    ·
      refine ⟨65781629430738016512444785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43854419620492011008296523 65781629430738016512444785)
      ·
        refine ⟨49336222073053512384333589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65781629430738016512444785 49336222073053512384333589)
        ·
          refine ⟨2312635409674383393015637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49336222073053512384333589 2312635409674383393015637)
          ·
            refine ⟨13550598103560840193451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2312635409674383393015637 13550598103560840193451)
            ·
              rfl

theorem cell20_801587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_801587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801587 prefixEnd_801587 := by exact prefixLift 801587
  have htrace : WordTrace (prefixWord ++ tailWord_801587) baseStart_801587 baseEnd_801587 := by
    simpa [prefixWord, tailWord_801587, baseEnd_801587] using wordTrace_append hprefix tailTrace_801587
  have hstable : (prefixWord ++ tailWord_801587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801587).length < 2 ^ (prefixWord ++ tailWord_801587).sum := by decide
  have hdescent : baseEnd_801587 < baseStart_801587 := by decide
  rcases family_descends (prefixWord ++ tailWord_801587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801649 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_801649 : Nat := 118140960795 + 801649 * 2 ^ 59
def prefixEnd_801649 : Nat := 4983230072969 + 3 ^ 40 * 801649 * 2
def baseEnd_801649 : Nat := 365894447285546025156257

theorem tailTrace_801649 : CollatzResearch.WordTrace tailWord_801649 prefixEnd_801649 365894447285546025156257 := by
  unfold tailWord_801649
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238541072770058594288001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19492360715180039062858667 29238541072770058594288001)
  ·
    refine ⟨21928905804577543945716001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29238541072770058594288001 21928905804577543945716001)
    ·
      refine ⟨16446679353433157959287001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21928905804577543945716001 16446679353433157959287001)
      ·
        refine ⟨12335009515074868469465251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16446679353433157959287001 12335009515074868469465251)
        ·
          refine ⟨18502514272612302704197877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335009515074868469465251 18502514272612302704197877)
          ·
            refine ⟨1734610713057403378518551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18502514272612302704197877 1734610713057403378518551)
            ·
              refine ⟨2601916069586105067777827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734610713057403378518551 2601916069586105067777827)
              ·
                refine ⟨3902874104379157601666741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601916069586105067777827 3902874104379157601666741)
                ·
                  refine ⟨365894447285546025156257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902874104379157601666741 365894447285546025156257)
                  ·
                    rfl

theorem cell20_801649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_801649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801649 prefixEnd_801649 := by exact prefixLift 801649
  have htrace : WordTrace (prefixWord ++ tailWord_801649) baseStart_801649 baseEnd_801649 := by
    simpa [prefixWord, tailWord_801649, baseEnd_801649] using wordTrace_append hprefix tailTrace_801649
  have hstable : (prefixWord ++ tailWord_801649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801649).length < 2 ^ (prefixWord ++ tailWord_801649).sum := by decide
  have hdescent : baseEnd_801649 < baseStart_801649 := by decide
  rcases family_descends (prefixWord ++ tailWord_801649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801721 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_801721 : Nat := 118140960795 + 801721 * 2 ^ 59
def prefixEnd_801721 : Nat := 4983230072969 + 3 ^ 40 * 801721 * 2
def baseEnd_801721 : Nat := 365927310047433774755963

theorem tailTrace_801721 : CollatzResearch.WordTrace tailWord_801721 prefixEnd_801721 365927310047433774755963 := by
  unfold tailWord_801721
  simp only [CollatzResearch.WordTrace]
  refine ⟨29241167128509214890909017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19494111419006143260606011 29241167128509214890909017)
  ·
    refine ⟨21930875346381911168181763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29241167128509214890909017 21930875346381911168181763)
    ·
      refine ⟨32896313019572866752272645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21930875346381911168181763 32896313019572866752272645)
      ·
        refine ⟨6168058691169912516051121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32896313019572866752272645 6168058691169912516051121)
        ·
          refine ⟨4626044018377434387038341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168058691169912516051121 4626044018377434387038341)
          ·
            refine ⟨867383253445768947569689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4626044018377434387038341 867383253445768947569689)
            ·
              refine ⟨650537440084326710677267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867383253445768947569689 650537440084326710677267)
              ·
                refine ⟨975806160126490066015901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650537440084326710677267 975806160126490066015901)
                ·
                  refine ⟨365927310047433774755963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975806160126490066015901 365927310047433774755963)
                  ·
                    rfl

theorem cell20_801721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_801721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801721 prefixEnd_801721 := by exact prefixLift 801721
  have htrace : WordTrace (prefixWord ++ tailWord_801721) baseStart_801721 baseEnd_801721 := by
    simpa [prefixWord, tailWord_801721, baseEnd_801721] using wordTrace_append hprefix tailTrace_801721
  have hstable : (prefixWord ++ tailWord_801721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801721).length < 2 ^ (prefixWord ++ tailWord_801721).sum := by decide
  have hdescent : baseEnd_801721 < baseStart_801721 := by decide
  rcases family_descends (prefixWord ++ tailWord_801721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801739 : List Nat := [1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_801739 : Nat := 118140960795 + 801739 * 2 ^ 59
def prefixEnd_801739 : Nat := 4983230072969 + 3 ^ 40 * 801739 * 2
def baseEnd_801739 : Nat := 121978508579301904051963

theorem tailTrace_801739 : CollatzResearch.WordTrace tailWord_801739 prefixEnd_801739 121978508579301904051963 := by
  unfold tailWord_801739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29241823642444003965064271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19494549094962669310042847 29241823642444003965064271)
  ·
    refine ⟨43862735463666005947596407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29241823642444003965064271 43862735463666005947596407)
    ·
      refine ⟨65794103195499008921394611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43862735463666005947596407 65794103195499008921394611)
      ·
        refine ⟨98691154793248513382091917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65794103195499008921394611 98691154793248513382091917)
        ·
          refine ⟨37009183047468192518284469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98691154793248513382091917 37009183047468192518284469)
          ·
            refine ⟨3469610910700143048589169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37009183047468192518284469 3469610910700143048589169)
            ·
              refine ⟨2602208183025107286441877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469610910700143048589169 2602208183025107286441877)
              ·
                refine ⟨121978508579301904051963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2602208183025107286441877 121978508579301904051963)
                ·
                  rfl

theorem cell20_801739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_801739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801739 prefixEnd_801739 := by exact prefixLift 801739
  have htrace : WordTrace (prefixWord ++ tailWord_801739) baseStart_801739 baseEnd_801739 := by
    simpa [prefixWord, tailWord_801739, baseEnd_801739] using wordTrace_append hprefix tailTrace_801739
  have hstable : (prefixWord ++ tailWord_801739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801739).length < 2 ^ (prefixWord ++ tailWord_801739).sum := by decide
  have hdescent : baseEnd_801739 < baseStart_801739 := by decide
  rcases family_descends (prefixWord ++ tailWord_801739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801756 : List Nat := [2, 2, 6, 10]
def baseStart_801756 : Nat := 118140960795 + 801756 * 2 ^ 59
def prefixEnd_801756 : Nat := 4983230072969 + 3 ^ 40 * 801756 * 2
def baseEnd_801756 : Nat := 1505939444449091393371

theorem tailTrace_801756 : CollatzResearch.WordTrace tailWord_801756 prefixEnd_801756 1505939444449091393371 := by
  unfold tailWord_801756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621221841691207934216561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19494962455588277245622081 14621221841691207934216561)
  ·
    refine ⟨10965916381268405950662421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14621221841691207934216561 10965916381268405950662421)
    ·
      refine ⟨514027330371956528937301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10965916381268405950662421 514027330371956528937301)
      ·
        refine ⟨1505939444449091393371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 514027330371956528937301 1505939444449091393371)
        ·
          rfl

theorem cell20_801756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 10].length) (baseStart_801756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801756 prefixEnd_801756 := by exact prefixLift 801756
  have htrace : WordTrace (prefixWord ++ tailWord_801756) baseStart_801756 baseEnd_801756 := by
    simpa [prefixWord, tailWord_801756, baseEnd_801756] using wordTrace_append hprefix tailTrace_801756
  have hstable : (prefixWord ++ tailWord_801756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801756).length < 2 ^ (prefixWord ++ tailWord_801756).sum := by decide
  have hdescent : baseEnd_801756 < baseStart_801756 := by decide
  rcases family_descends (prefixWord ++ tailWord_801756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801762 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_801762 : Nat := 118140960795 + 801762 * 2 ^ 59
def prefixEnd_801762 : Nat := 4983230072969 + 3 ^ 40 * 801762 * 2
def baseEnd_801762 : Nat := 365946023564619854389129

theorem tailTrace_801762 : CollatzResearch.WordTrace tailWord_801762 prefixEnd_801762 365946023564619854389129 := by
  unfold tailWord_801762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310665630340169723287885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19495108347573785928767693 7310665630340169723287885)
  ·
    refine ⟨2741499611377563646232957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7310665630340169723287885 2741499611377563646232957)
    ·
      refine ⟨1028062354266586367337359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2741499611377563646232957 1028062354266586367337359)
      ·
        refine ⟨1542093531399879551006039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028062354266586367337359 1542093531399879551006039)
        ·
          refine ⟨2313140297099819326509059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542093531399879551006039 2313140297099819326509059)
          ·
            refine ⟨3469710445649728989763589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313140297099819326509059 3469710445649728989763589)
            ·
              refine ⟨650570708559324185580673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3469710445649728989763589 650570708559324185580673)
              ·
                refine ⟨487928031419493139185505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650570708559324185580673 487928031419493139185505)
                ·
                  refine ⟨365946023564619854389129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487928031419493139185505 365946023564619854389129)
                  ·
                    rfl

theorem cell20_801762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_801762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801762 prefixEnd_801762 := by exact prefixLift 801762
  have htrace : WordTrace (prefixWord ++ tailWord_801762) baseStart_801762 baseEnd_801762 := by
    simpa [prefixWord, tailWord_801762, baseEnd_801762] using wordTrace_append hprefix tailTrace_801762
  have hstable : (prefixWord ++ tailWord_801762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801762).length < 2 ^ (prefixWord ++ tailWord_801762).sum := by decide
  have hdescent : baseEnd_801762 < baseStart_801762 := by decide
  rcases family_descends (prefixWord ++ tailWord_801762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801784 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_801784 : Nat := 118140960795 + 801784 * 2 ^ 59
def prefixEnd_801784 : Nat := 4983230072969 + 3 ^ 40 * 801784 * 2
def baseEnd_801784 : Nat := 365956064964085555655705

theorem tailTrace_801784 : CollatzResearch.WordTrace tailWord_801784 prefixEnd_801784 365956064964085555655705 := by
  unfold tailWord_801784
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621732463640488325226203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19495643284853984433634937 14621732463640488325226203)
  ·
    refine ⟨21932598695460732487839305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14621732463640488325226203 21932598695460732487839305)
    ·
      refine ⟨16449449021595549365879479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21932598695460732487839305 16449449021595549365879479)
      ·
        refine ⟨24674173532393324048819219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449449021595549365879479 24674173532393324048819219)
        ·
          refine ⟨37011260298589986073228829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674173532393324048819219 37011260298589986073228829)
          ·
            refine ⟨13879222611971244777460811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37011260298589986073228829 13879222611971244777460811)
            ·
              refine ⟨20818833917956867166191217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13879222611971244777460811 20818833917956867166191217)
              ·
                refine ⟨15614125438467650374643413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20818833917956867166191217 15614125438467650374643413)
                ·
                  refine ⟨365956064964085555655705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15614125438467650374643413 365956064964085555655705)
                  ·
                    rfl

theorem cell20_801784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_801784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801784 prefixEnd_801784 := by exact prefixLift 801784
  have htrace : WordTrace (prefixWord ++ tailWord_801784) baseStart_801784 baseEnd_801784 := by
    simpa [prefixWord, tailWord_801784, baseEnd_801784] using wordTrace_append hprefix tailTrace_801784
  have hstable : (prefixWord ++ tailWord_801784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801784).length < 2 ^ (prefixWord ++ tailWord_801784).sum := by decide
  have hdescent : baseEnd_801784 < baseStart_801784 := by decide
  rcases family_descends (prefixWord ++ tailWord_801784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801790 : List Nat := [4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_801790 : Nat := 118140960795 + 801790 * 2 ^ 59
def prefixEnd_801790 : Nat := 4983230072969 + 3 ^ 40 * 801790 * 2
def baseEnd_801790 : Nat := 121986267842525400485227

theorem tailTrace_801790 : CollatzResearch.WordTrace tailWord_801790 prefixEnd_801790 121986267842525400485227 := by
  unfold tailWord_801790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655460470657404959396353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19495789176839493116780549 3655460470657404959396353)
  ·
    refine ⟨2741595352993053719547265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3655460470657404959396353 2741595352993053719547265)
    ·
      refine ⟨2056196514744790289660449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2741595352993053719547265 2056196514744790289660449)
      ·
        refine ⟨1542147386058592717245337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056196514744790289660449 1542147386058592717245337)
        ·
          refine ⟨1156610539543944537934003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542147386058592717245337 1156610539543944537934003)
          ·
            refine ⟨1734915809315916806901005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156610539543944537934003 1734915809315916806901005)
            ·
              refine ⟨650593428493468802587877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734915809315916806901005 650593428493468802587877)
              ·
                refine ⟨121986267842525400485227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650593428493468802587877 121986267842525400485227)
                ·
                  rfl

theorem cell20_801790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_801790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801790 prefixEnd_801790 := by exact prefixLift 801790
  have htrace : WordTrace (prefixWord ++ tailWord_801790) baseStart_801790 baseEnd_801790 := by
    simpa [prefixWord, tailWord_801790, baseEnd_801790] using wordTrace_append hprefix tailTrace_801790
  have hstable : (prefixWord ++ tailWord_801790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801790).length < 2 ^ (prefixWord ++ tailWord_801790).sum := by decide
  have hdescent : baseEnd_801790 < baseStart_801790 := by decide
  rcases family_descends (prefixWord ++ tailWord_801790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801804 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_801804 : Nat := 118140960795 + 801804 * 2 ^ 59
def prefixEnd_801804 : Nat := 4983230072969 + 3 ^ 40 * 801804 * 2
def baseEnd_801804 : Nat := 365965193509054374988957

theorem tailTrace_801804 : CollatzResearch.WordTrace tailWord_801804 prefixEnd_801804 365965193509054374988957 := by
  unfold tailWord_801804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622097193604260033090233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19496129591472346710786977 14622097193604260033090233)
  ·
    refine ⟨10966572895203195024817675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14622097193604260033090233 10966572895203195024817675)
    ·
      refine ⟨16449859342804792537226513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10966572895203195024817675 16449859342804792537226513)
      ·
        refine ⟨12337394507103594402919885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16449859342804792537226513 12337394507103594402919885)
        ·
          refine ⟨4626522940163847901094957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12337394507103594402919885 4626522940163847901094957)
          ·
            refine ⟨1734946102561442962910609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4626522940163847901094957 1734946102561442962910609)
            ·
              refine ⟨1301209576921082222182957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734946102561442962910609 1301209576921082222182957)
              ·
                refine ⟨487953591345405833318609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1301209576921082222182957 487953591345405833318609)
                ·
                  refine ⟨365965193509054374988957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487953591345405833318609 365965193509054374988957)
                  ·
                    rfl

theorem cell20_801804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_801804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801804 prefixEnd_801804 := by exact prefixLift 801804
  have htrace : WordTrace (prefixWord ++ tailWord_801804) baseStart_801804 baseEnd_801804 := by
    simpa [prefixWord, tailWord_801804, baseEnd_801804] using wordTrace_append hprefix tailTrace_801804
  have hstable : (prefixWord ++ tailWord_801804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801804).length < 2 ^ (prefixWord ++ tailWord_801804).sum := by decide
  have hdescent : baseEnd_801804 < baseStart_801804 := by decide
  rcases family_descends (prefixWord ++ tailWord_801804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801810 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_801810 : Nat := 118140960795 + 801810 * 2 ^ 59
def prefixEnd_801810 : Nat := 4983230072969 + 3 ^ 40 * 801810 * 2
def baseEnd_801810 : Nat := 365967932072545020788933

theorem tailTrace_801810 : CollatzResearch.WordTrace tailWord_801810 prefixEnd_801810 365967932072545020788933 := by
  unfold tailWord_801810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311103306296695772724721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19496275483457855393932589 7311103306296695772724721)
  ·
    refine ⟨5483327479722521829543541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7311103306296695772724721 5483327479722521829543541)
    ·
      refine ⟨514061951223986421519707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5483327479722521829543541 514061951223986421519707)
      ·
        refine ⟨771092926835979632279561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514061951223986421519707 771092926835979632279561)
        ·
          refine ⟨578319695126984724209671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771092926835979632279561 578319695126984724209671)
          ·
            refine ⟨867479542690477086314507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578319695126984724209671 867479542690477086314507)
            ·
              refine ⟨1301219314035715629471761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867479542690477086314507 1301219314035715629471761)
              ·
                refine ⟨975914485526786722103821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301219314035715629471761 975914485526786722103821)
                ·
                  refine ⟨365967932072545020788933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975914485526786722103821 365967932072545020788933)
                  ·
                    rfl

theorem cell20_801810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_801810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801810 prefixEnd_801810 := by exact prefixLift 801810
  have htrace : WordTrace (prefixWord ++ tailWord_801810) baseStart_801810 baseEnd_801810 := by
    simpa [prefixWord, tailWord_801810, baseEnd_801810] using wordTrace_append hprefix tailTrace_801810
  have hstable : (prefixWord ++ tailWord_801810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801810).length < 2 ^ (prefixWord ++ tailWord_801810).sum := by decide
  have hdescent : baseEnd_801810 < baseStart_801810 := by decide
  rcases family_descends (prefixWord ++ tailWord_801810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801825 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_801825 : Nat := 118140960795 + 801825 * 2 ^ 59
def prefixEnd_801825 : Nat := 4983230072969 + 3 ^ 40 * 801825 * 2
def baseEnd_801825 : Nat := 365974778481271635288871

theorem tailTrace_801825 : CollatzResearch.WordTrace tailWord_801825 prefixEnd_801825 365974778481271635288871 := by
  unfold tailWord_801825
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244960320132440652694929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19496640213421627101796619 29244960320132440652694929)
  ·
    refine ⟨21933720240099330489521197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29244960320132440652694929 21933720240099330489521197)
    ·
      refine ⟨8225145090037248933570449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21933720240099330489521197 8225145090037248933570449)
      ·
        refine ⟨6168858817527936700177837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8225145090037248933570449 6168858817527936700177837)
        ·
          refine ⟨2313322056572976262566689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6168858817527936700177837 2313322056572976262566689)
          ·
            refine ⟨1734991542429732196925017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2313322056572976262566689 1734991542429732196925017)
            ·
              refine ⟨1301243656822299147693763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734991542429732196925017 1301243656822299147693763)
              ·
                refine ⟨1951865485233448721540645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301243656822299147693763 1951865485233448721540645)
                ·
                  refine ⟨365974778481271635288871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951865485233448721540645 365974778481271635288871)
                  ·
                    rfl

theorem cell20_801825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_801825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801825 prefixEnd_801825 := by exact prefixLift 801825
  have htrace : WordTrace (prefixWord ++ tailWord_801825) baseStart_801825 baseEnd_801825 := by
    simpa [prefixWord, tailWord_801825, baseEnd_801825] using wordTrace_append hprefix tailTrace_801825
  have hstable : (prefixWord ++ tailWord_801825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801825).length < 2 ^ (prefixWord ++ tailWord_801825).sum := by decide
  have hdescent : baseEnd_801825 < baseStart_801825 := by decide
  rcases family_descends (prefixWord ++ tailWord_801825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801849 : List Nat := [1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_801849 : Nat := 118140960795 + 801849 * 2 ^ 59
def prefixEnd_801849 : Nat := 4983230072969 + 3 ^ 40 * 801849 * 2
def baseEnd_801849 : Nat := 121995244245078072829591

theorem tailTrace_801849 : CollatzResearch.WordTrace tailWord_801849 prefixEnd_801849 121995244245078072829591 := by
  unfold tailWord_801849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245835672045492751568601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19497223781363661834379067 29245835672045492751568601)
  ·
    refine ⟨21934376754034119563676451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29245835672045492751568601 21934376754034119563676451)
    ·
      refine ⟨32901565131051179345514677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21934376754034119563676451 32901565131051179345514677)
      ·
        refine ⟨3084521731036048063642001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32901565131051179345514677 3084521731036048063642001)
        ·
          refine ⟨2313391298277036047731501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084521731036048063642001 2313391298277036047731501)
          ·
            refine ⟨867521736853888517899313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2313391298277036047731501 867521736853888517899313)
            ·
              refine ⟨650641302640416388424485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867521736853888517899313 650641302640416388424485)
              ·
                refine ⟨121995244245078072829591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650641302640416388424485 121995244245078072829591)
                ·
                  rfl

theorem cell20_801849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_801849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801849 prefixEnd_801849 := by exact prefixLift 801849
  have htrace : WordTrace (prefixWord ++ tailWord_801849) baseStart_801849 baseEnd_801849 := by
    simpa [prefixWord, tailWord_801849, baseEnd_801849] using wordTrace_append hprefix tailTrace_801849
  have hstable : (prefixWord ++ tailWord_801849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801849).length < 2 ^ (prefixWord ++ tailWord_801849).sum := by decide
  have hdescent : baseEnd_801849 < baseStart_801849 := by decide
  rcases family_descends (prefixWord ++ tailWord_801849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801877 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_801877 : Nat := 118140960795 + 801877 * 2 ^ 59
def prefixEnd_801877 : Nat := 4983230072969 + 3 ^ 40 * 801877 * 2
def baseEnd_801877 : Nat := 365998512698190565555325

theorem tailTrace_801877 : CollatzResearch.WordTrace tailWord_801877 prefixEnd_801877 365998512698190565555325 := by
  unfold tailWord_801877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246856915944053533587885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19497904610629369022391923 29246856915944053533587885)
  ·
    refine ⟨10967571343479020075095457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29246856915944053533587885 10967571343479020075095457)
    ·
      refine ⟨8225678507609265056321593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10967571343479020075095457 8225678507609265056321593)
      ·
        refine ⟨6169258880706948792241195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8225678507609265056321593 6169258880706948792241195)
        ·
          refine ⟨9253888321060423188361793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169258880706948792241195 9253888321060423188361793)
          ·
            refine ⟨6940416240795317391271345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9253888321060423188361793 6940416240795317391271345)
            ·
              refine ⟨5205312180596488043453509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940416240795317391271345 5205312180596488043453509)
              ·
                refine ⟨975996033861841508147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5205312180596488043453509 975996033861841508147533)
                ·
                  refine ⟨365998512698190565555325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975996033861841508147533 365998512698190565555325)
                  ·
                    rfl

theorem cell20_801877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_801877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801877 prefixEnd_801877 := by exact prefixLift 801877
  have htrace : WordTrace (prefixWord ++ tailWord_801877) baseStart_801877 baseEnd_801877 := by
    simpa [prefixWord, tailWord_801877, baseEnd_801877] using wordTrace_append hprefix tailTrace_801877
  have hstable : (prefixWord ++ tailWord_801877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801877).length < 2 ^ (prefixWord ++ tailWord_801877).sum := by decide
  have hdescent : baseEnd_801877 < baseStart_801877 := by decide
  rcases family_descends (prefixWord ++ tailWord_801877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801880 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_801880 : Nat := 118140960795 + 801880 * 2 ^ 59
def prefixEnd_801880 : Nat := 4983230072969 + 3 ^ 40 * 801880 * 2
def baseEnd_801880 : Nat := 365999881979935888455313

theorem tailTrace_801880 : CollatzResearch.WordTrace tailWord_801880 prefixEnd_801880 365999881979935888455313 := by
  unfold tailWord_801880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623483167466592522973547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19497977556622123363964729 14623483167466592522973547)
  ·
    refine ⟨21935224751199888784460321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623483167466592522973547 21935224751199888784460321)
    ·
      refine ⟨16451418563399916588345241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21935224751199888784460321 16451418563399916588345241)
      ·
        refine ⟨12338563922549937441258931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16451418563399916588345241 12338563922549937441258931)
        ·
          refine ⟨18507845883824906161888397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338563922549937441258931 18507845883824906161888397)
          ·
            refine ⟨6940442206434339810708149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18507845883824906161888397 6940442206434339810708149)
            ·
              refine ⟨650666456853219357253889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6940442206434339810708149 650666456853219357253889)
              ·
                refine ⟨487999842639914517940417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650666456853219357253889 487999842639914517940417)
                ·
                  refine ⟨365999881979935888455313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487999842639914517940417 365999881979935888455313)
                  ·
                    rfl

theorem cell20_801880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_801880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801880 prefixEnd_801880 := by exact prefixLift 801880
  have htrace : WordTrace (prefixWord ++ tailWord_801880) baseStart_801880 baseEnd_801880 := by
    simpa [prefixWord, tailWord_801880, baseEnd_801880] using wordTrace_append hprefix tailTrace_801880
  have hstable : (prefixWord ++ tailWord_801880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801880).length < 2 ^ (prefixWord ++ tailWord_801880).sum := by decide
  have hdescent : baseEnd_801880 < baseStart_801880 := by decide
  rcases family_descends (prefixWord ++ tailWord_801880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801890 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_801890 : Nat := 118140960795 + 801890 * 2 ^ 59
def prefixEnd_801890 : Nat := 4983230072969 + 3 ^ 40 * 801890 * 2
def baseEnd_801890 : Nat := 366004446252420298121939

theorem tailTrace_801890 : CollatzResearch.WordTrace tailWord_801890 prefixEnd_801890 366004446252420298121939 := by
  unfold tailWord_801890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311832766224239188452781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19498220709931304502540749 7311832766224239188452781)
  ·
    refine ⟨2741937287334089695669793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7311832766224239188452781 2741937287334089695669793)
    ·
      refine ⟨2056452965500567271752345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2741937287334089695669793 2056452965500567271752345)
      ·
        refine ⟨1542339724125425453814259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056452965500567271752345 1542339724125425453814259)
        ·
          refine ⟨2313509586188138180721389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542339724125425453814259 2313509586188138180721389)
          ·
            refine ⟨867566094820551817770521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2313509586188138180721389 867566094820551817770521)
            ·
              refine ⟨650674571115413863327891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867566094820551817770521 650674571115413863327891)
              ·
                refine ⟨976011856673120794991837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650674571115413863327891 976011856673120794991837)
                ·
                  refine ⟨366004446252420298121939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976011856673120794991837 366004446252420298121939)
                  ·
                    rfl

theorem cell20_801890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_801890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801890 prefixEnd_801890 := by exact prefixLift 801890
  have htrace : WordTrace (prefixWord ++ tailWord_801890) baseStart_801890 baseEnd_801890 := by
    simpa [prefixWord, tailWord_801890, baseEnd_801890] using wordTrace_append hprefix tailTrace_801890
  have hstable : (prefixWord ++ tailWord_801890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801890).length < 2 ^ (prefixWord ++ tailWord_801890).sum := by decide
  have hdescent : baseEnd_801890 < baseStart_801890 := by decide
  rcases family_descends (prefixWord ++ tailWord_801890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801946 : List Nat := [3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_801946 : Nat := 118140960795 + 801946 * 2 ^ 59
def prefixEnd_801946 : Nat := 4983230072969 + 3 ^ 40 * 801946 * 2
def baseEnd_801946 : Nat := 122010002059444330751681

theorem tailTrace_801946 : CollatzResearch.WordTrace tailWord_801946 prefixEnd_801946 122010002059444330751681 := by
  unfold tailWord_801946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312343388173519579462423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19499582368462718878566461 7312343388173519579462423)
  ·
    refine ⟨10968515082260279369193635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312343388173519579462423 10968515082260279369193635)
    ·
      refine ⟨16452772623390419053790453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968515082260279369193635 16452772623390419053790453)
      ·
        refine ⟨1542447433442851786292855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16452772623390419053790453 1542447433442851786292855)
        ·
          refine ⟨2313671150164277679439283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542447433442851786292855 2313671150164277679439283)
          ·
            refine ⟨3470506725246416519158925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313671150164277679439283 3470506725246416519158925)
            ·
              refine ⟨1301440021967406194684597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3470506725246416519158925 1301440021967406194684597)
              ·
                refine ⟨122010002059444330751681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1301440021967406194684597 122010002059444330751681)
                ·
                  rfl

theorem cell20_801946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_801946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801946 prefixEnd_801946 := by exact prefixLift 801946
  have htrace : WordTrace (prefixWord ++ tailWord_801946) baseStart_801946 baseEnd_801946 := by
    simpa [prefixWord, tailWord_801946, baseEnd_801946] using wordTrace_append hprefix tailTrace_801946
  have hstable : (prefixWord ++ tailWord_801946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801946).length < 2 ^ (prefixWord ++ tailWord_801946).sum := by decide
  have hdescent : baseEnd_801946 < baseStart_801946 := by decide
  rcases family_descends (prefixWord ++ tailWord_801946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801953 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_801953 : Nat := 118140960795 + 801953 * 2 ^ 59
def prefixEnd_801953 : Nat := 4983230072969 + 3 ^ 40 * 801953 * 2
def baseEnd_801953 : Nat := 366033201169072079021681

theorem tailTrace_801953 : CollatzResearch.WordTrace tailWord_801953 prefixEnd_801953 366033201169072079021681 := by
  unfold tailWord_801953
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249628863668718513354513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19499752575779145675569675 29249628863668718513354513)
  ·
    refine ⟨21937221647751538885015885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29249628863668718513354513 21937221647751538885015885)
    ·
      refine ⟨8226458117906827081880957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21937221647751538885015885 8226458117906827081880957)
      ·
        refine ⟨3084921794215060155705359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8226458117906827081880957 3084921794215060155705359)
        ·
          refine ⟨4627382691322590233558039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084921794215060155705359 4627382691322590233558039)
          ·
            refine ⟨6941074036983885350337059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627382691322590233558039 6941074036983885350337059)
            ·
              refine ⟨10411611055475828025505589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941074036983885350337059 10411611055475828025505589)
              ·
                refine ⟨976088536450858877391149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10411611055475828025505589 976088536450858877391149)
                ·
                  refine ⟨366033201169072079021681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976088536450858877391149 366033201169072079021681)
                  ·
                    rfl

theorem cell20_801953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_801953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801953 prefixEnd_801953 := by exact prefixLift 801953
  have htrace : WordTrace (prefixWord ++ tailWord_801953) baseStart_801953 baseEnd_801953 := by
    simpa [prefixWord, tailWord_801953, baseEnd_801953] using wordTrace_append hprefix tailTrace_801953
  have hstable : (prefixWord ++ tailWord_801953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801953).length < 2 ^ (prefixWord ++ tailWord_801953).sum := by decide
  have hdescent : baseEnd_801953 < baseStart_801953 := by decide
  rcases family_descends (prefixWord ++ tailWord_801953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801977 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 2]
def baseStart_801977 : Nat := 118140960795 + 801977 * 2 ^ 59
def prefixEnd_801977 : Nat := 4983230072969 + 3 ^ 40 * 801977 * 2
def baseEnd_801977 : Nat := 366044155423034662221583

theorem tailTrace_801977 : CollatzResearch.WordTrace tailWord_801977 prefixEnd_801977 366044155423034662221583 := by
  unfold tailWord_801977
  simp only [CollatzResearch.WordTrace]
  refine ⟨29250504215581770612228185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19500336143721180408152123 29250504215581770612228185)
  ·
    refine ⟨21937878161686327959171139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29250504215581770612228185 21937878161686327959171139)
    ·
      refine ⟨32906817242529491938756709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21937878161686327959171139 32906817242529491938756709)
      ·
        refine ⟨6170028232974279738516883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32906817242529491938756709 6170028232974279738516883)
        ·
          refine ⟨9255042349461419607775325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170028232974279738516883 9255042349461419607775325)
          ·
            refine ⟨3470640881048032352915747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9255042349461419607775325 3470640881048032352915747)
            ·
              refine ⟨5205961321572048529373621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470640881048032352915747 5205961321572048529373621)
              ·
                refine ⟨488058873897379549628777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5205961321572048529373621 488058873897379549628777)
                ·
                  refine ⟨366044155423034662221583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488058873897379549628777 366044155423034662221583)
                  ·
                    rfl

theorem cell20_801977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_801977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801977 prefixEnd_801977 := by exact prefixLift 801977
  have htrace : WordTrace (prefixWord ++ tailWord_801977) baseStart_801977 baseEnd_801977 := by
    simpa [prefixWord, tailWord_801977, baseEnd_801977] using wordTrace_append hprefix tailTrace_801977
  have hstable : (prefixWord ++ tailWord_801977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801977).length < 2 ^ (prefixWord ++ tailWord_801977).sum := by decide
  have hdescent : baseEnd_801977 < baseStart_801977 := by decide
  rcases family_descends (prefixWord ++ tailWord_801977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801990 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_801990 : Nat := 118140960795 + 801990 * 2 ^ 59
def prefixEnd_801990 : Nat := 4983230072969 + 3 ^ 40 * 801990 * 2
def baseEnd_801990 : Nat := 366050088977264394788197

theorem tailTrace_801990 : CollatzResearch.WordTrace tailWord_801990 prefixEnd_801990 366050088977264394788197 := by
  unfold tailWord_801990
  simp only [CollatzResearch.WordTrace]
  refine ⟨914093073891708557264107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19500652243023115888300949 914093073891708557264107)
  ·
    refine ⟨1371139610837562835896161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914093073891708557264107 1371139610837562835896161)
    ·
      refine ⟨1028354708128172126922121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371139610837562835896161 1028354708128172126922121)
      ·
        refine ⟨771266031096129095191591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028354708128172126922121 771266031096129095191591)
        ·
          refine ⟨1156899046644193642787387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771266031096129095191591 1156899046644193642787387)
          ·
            refine ⟨1735348569966290464181081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156899046644193642787387 1735348569966290464181081)
            ·
              refine ⟨1301511427474717848135811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735348569966290464181081 1301511427474717848135811)
              ·
                refine ⟨1952267141212076772203717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301511427474717848135811 1952267141212076772203717)
                ·
                  refine ⟨366050088977264394788197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952267141212076772203717 366050088977264394788197)
                  ·
                    rfl

theorem cell20_801990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_801990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_801990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_801990 prefixEnd_801990 := by exact prefixLift 801990
  have htrace : WordTrace (prefixWord ++ tailWord_801990) baseStart_801990 baseEnd_801990 := by
    simpa [prefixWord, tailWord_801990, baseEnd_801990] using wordTrace_append hprefix tailTrace_801990
  have hstable : (prefixWord ++ tailWord_801990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801990).length < 2 ^ (prefixWord ++ tailWord_801990).sum := by decide
  have hdescent : baseEnd_801990 < baseStart_801990 := by decide
  rcases family_descends (prefixWord ++ tailWord_801990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802004 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_802004 : Nat := 118140960795 + 802004 * 2 ^ 59
def prefixEnd_802004 : Nat := 4983230072969 + 3 ^ 40 * 802004 * 2
def baseEnd_802004 : Nat := 366056478958742568321473

theorem tailTrace_802004 : CollatzResearch.WordTrace tailWord_802004 prefixEnd_802004 366056478958742568321473 := by
  unfold tailWord_802004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14625744493241977111730533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19500992657655969482307377 14625744493241977111730533)
  ·
    refine ⟨2742327092482870708449475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14625744493241977111730533 2742327092482870708449475)
    ·
      refine ⟨4113490638724306062674213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742327092482870708449475 4113490638724306062674213)
      ·
        refine ⟨771279494760807386751415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4113490638724306062674213 771279494760807386751415)
        ·
          refine ⟨1156919242141211080127123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771279494760807386751415 1156919242141211080127123)
          ·
            refine ⟨1735378863211816620190685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156919242141211080127123 1735378863211816620190685)
            ·
              refine ⟨650767073704431232571507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1735378863211816620190685 650767073704431232571507)
              ·
                refine ⟨976150610556646848857261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650767073704431232571507 976150610556646848857261)
                ·
                  refine ⟨366056478958742568321473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976150610556646848857261 366056478958742568321473)
                  ·
                    rfl

theorem cell20_802004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_802004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802004 prefixEnd_802004 := by exact prefixLift 802004
  have htrace : WordTrace (prefixWord ++ tailWord_802004) baseStart_802004 baseEnd_802004 := by
    simpa [prefixWord, tailWord_802004, baseEnd_802004] using wordTrace_append hprefix tailTrace_802004
  have hstable : (prefixWord ++ tailWord_802004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802004).length < 2 ^ (prefixWord ++ tailWord_802004).sum := by decide
  have hdescent : baseEnd_802004 < baseStart_802004 := by decide
  rcases family_descends (prefixWord ++ tailWord_802004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
