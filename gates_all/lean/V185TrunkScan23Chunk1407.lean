import V185TrunkScan23Chunk1406

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8333947 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_8333947 : Nat := 118140960795 + 8333947 * 2 ^ 59
def prefixEnd_8333947 : Nat := 4983230072969 + 3 ^ 40 * 8333947 * 2
def baseEnd_8333947 : Nat := 4279320560095810127735381

theorem tailTrace_8333947 : CollatzResearch.WordTrace tailWord_8333947 prefixEnd_8333947 4279320560095810127735381 := by
  unfold tailWord_8333947
  simp only [CollatzResearch.WordTrace]
  refine ⟨303964018738540818676032095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202642679159027212450688063 303964018738540818676032095)
  ·
    refine ⟨455946028107811228014048143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303964018738540818676032095 455946028107811228014048143)
    ·
      refine ⟨683919042161716842021072215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455946028107811228014048143 683919042161716842021072215)
      ·
        refine ⟨1025878563242575263031608323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683919042161716842021072215 1025878563242575263031608323)
        ·
          refine ⟨1538817844863862894547412485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025878563242575263031608323 1538817844863862894547412485)
          ·
            refine ⟨288528345911974292727639841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1538817844863862894547412485 288528345911974292727639841)
            ·
              refine ⟨216396259433980719545729881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288528345911974292727639841 216396259433980719545729881)
              ·
                refine ⟨162297194575485539659297411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216396259433980719545729881 162297194575485539659297411)
                ·
                  refine ⟨243445791863228309488946117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162297194575485539659297411 243445791863228309488946117)
                  ·
                    refine ⟨45646085974355308029177397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243445791863228309488946117 45646085974355308029177397)
                    ·
                      refine ⟨4279320560095810127735381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45646085974355308029177397 4279320560095810127735381)
                      ·
                        rfl

theorem cell23_8333947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_8333947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333947 prefixEnd_8333947 := by exact prefixLift 8333947
  have htrace : WordTrace (prefixWord ++ tailWord_8333947) baseStart_8333947 baseEnd_8333947 := by
    simpa [prefixWord, tailWord_8333947, baseEnd_8333947] using wordTrace_append hprefix tailTrace_8333947
  have hstable : (prefixWord ++ tailWord_8333947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333947).length < 2 ^ (prefixWord ++ tailWord_8333947).sum := by decide
  have hdescent : baseEnd_8333947 < baseStart_8333947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333967 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 8]
def baseStart_8333967 : Nat := 118140960795 + 8333967 * 2 ^ 59
def prefixEnd_8333967 : Nat := 4983230072969 + 3 ^ 40 * 8333967 * 2
def baseEnd_8333967 : Nat := 1426443609902966683161763

theorem tailTrace_8333967 : CollatzResearch.WordTrace tailWord_8333967 prefixEnd_8333967 1426443609902966683161763 := by
  unfold tailWord_8333967
  simp only [CollatzResearch.WordTrace]
  refine ⟨303964748198468362091760155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202643165465645574727840103 303964748198468362091760155)
  ·
    refine ⟨455947122297702543137640233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303964748198468362091760155 455947122297702543137640233)
    ·
      refine ⟨341960341723276907353230175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455947122297702543137640233 341960341723276907353230175)
      ·
        refine ⟨512940512584915361029845263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341960341723276907353230175 512940512584915361029845263)
        ·
          refine ⟨769410768877373041544767895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512940512584915361029845263 769410768877373041544767895)
          ·
            refine ⟨1154116153316059562317151843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769410768877373041544767895 1154116153316059562317151843)
            ·
              refine ⟨1731174229974089343475727765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154116153316059562317151843 1731174229974089343475727765)
              ·
                refine ⟨81148792030035437975424739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1731174229974089343475727765 81148792030035437975424739)
                ·
                  refine ⟨121723188045053156963137109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81148792030035437975424739 121723188045053156963137109)
                  ·
                    refine ⟨1426443609902966683161763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121723188045053156963137109 1426443609902966683161763)
                    ·
                      rfl

theorem cell23_8333967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_8333967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333967 prefixEnd_8333967 := by exact prefixLift 8333967
  have htrace : WordTrace (prefixWord ++ tailWord_8333967) baseStart_8333967 baseEnd_8333967 := by
    simpa [prefixWord, tailWord_8333967, baseEnd_8333967] using wordTrace_append hprefix tailTrace_8333967
  have hstable : (prefixWord ++ tailWord_8333967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333967).length < 2 ^ (prefixWord ++ tailWord_8333967).sum := by decide
  have hdescent : baseEnd_8333967 < baseStart_8333967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333985 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_8333985 : Nat := 118140960795 + 8333985 * 2 ^ 59
def prefixEnd_8333985 : Nat := 4983230072969 + 3 ^ 40 * 8333985 * 2
def baseEnd_8333985 : Nat := 4279340072360680979060207

theorem tailTrace_8333985 : CollatzResearch.WordTrace tailWord_8333985 prefixEnd_8333985 4279340072360680979060207 := by
  unfold tailWord_8333985
  simp only [CollatzResearch.WordTrace]
  refine ⟨303965404712403151165915409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202643603141602100777276939 303965404712403151165915409)
  ·
    refine ⟨227974053534302363374436557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303965404712403151165915409 227974053534302363374436557)
    ·
      refine ⟨85490270075363386265413709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227974053534302363374436557 85490270075363386265413709)
      ·
        refine ⟨32058851278261269849530141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85490270075363386265413709 32058851278261269849530141)
        ·
          refine ⟨12022069229347976193573803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32058851278261269849530141 12022069229347976193573803)
          ·
            refine ⟨18033103844021964290360705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022069229347976193573803 18033103844021964290360705)
            ·
              refine ⟨13524827883016473217770529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18033103844021964290360705 13524827883016473217770529)
              ·
                refine ⟨10143620912262354913327897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13524827883016473217770529 10143620912262354913327897)
                ·
                  refine ⟨7607715684196766184995923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10143620912262354913327897 7607715684196766184995923)
                  ·
                    refine ⟨11411573526295149277493885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607715684196766184995923 11411573526295149277493885)
                    ·
                      refine ⟨4279340072360680979060207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411573526295149277493885 4279340072360680979060207)
                      ·
                        rfl

theorem cell23_8333985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_8333985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333985 prefixEnd_8333985 := by exact prefixLift 8333985
  have htrace : WordTrace (prefixWord ++ tailWord_8333985) baseStart_8333985 baseEnd_8333985 := by
    simpa [prefixWord, tailWord_8333985, baseEnd_8333985] using wordTrace_append hprefix tailTrace_8333985
  have hstable : (prefixWord ++ tailWord_8333985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333985).length < 2 ^ (prefixWord ++ tailWord_8333985).sum := by decide
  have hdescent : baseEnd_8333985 < baseStart_8333985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334064 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_8334064 : Nat := 118140960795 + 8334064 * 2 ^ 59
def prefixEnd_8334064 : Nat := 4983230072969 + 3 ^ 40 * 8334064 * 2
def baseEnd_8334064 : Nat := 4279380637332386169972343

theorem tailTrace_8334064 : CollatzResearch.WordTrace tailWord_8334064 prefixEnd_8334064 4279380637332386169972343 := by
  unfold tailWord_8334064
  simp only [CollatzResearch.WordTrace]
  refine ⟨151984143039558473829020623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202645524052744631772027497 151984143039558473829020623)
  ·
    refine ⟨227976214559337710743530935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151984143039558473829020623 227976214559337710743530935)
    ·
      refine ⟨341964321839006566115296403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227976214559337710743530935 341964321839006566115296403)
      ·
        refine ⟨512946482758509849172944605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341964321839006566115296403 512946482758509849172944605)
        ·
          refine ⟨192354931034441193439854227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512946482758509849172944605 192354931034441193439854227)
          ·
            refine ⟨288532396551661790159781341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192354931034441193439854227 288532396551661790159781341)
            ·
              refine ⟨108199648706873171309918003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288532396551661790159781341 108199648706873171309918003)
              ·
                refine ⟨162299473060309756964877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108199648706873171309918003 162299473060309756964877005)
                ·
                  refine ⟨60862302397616158861828877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162299473060309756964877005 60862302397616158861828877)
                  ·
                    refine ⟨22823363399106059573185829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60862302397616158861828877 22823363399106059573185829)
                    ·
                      refine ⟨4279380637332386169972343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22823363399106059573185829 4279380637332386169972343)
                      ·
                        rfl

theorem cell23_8334064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_8334064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334064 prefixEnd_8334064 := by exact prefixLift 8334064
  have htrace : WordTrace (prefixWord ++ tailWord_8334064) baseStart_8334064 baseEnd_8334064 := by
    simpa [prefixWord, tailWord_8334064, baseEnd_8334064] using wordTrace_append hprefix tailTrace_8334064
  have hstable : (prefixWord ++ tailWord_8334064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334064).length < 2 ^ (prefixWord ++ tailWord_8334064).sum := by decide
  have hdescent : baseEnd_8334064 < baseStart_8334064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334081 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_8334081 : Nat := 118140960795 + 8334081 * 2 ^ 59
def prefixEnd_8334081 : Nat := 4983230072969 + 3 ^ 40 * 8334081 * 2
def baseEnd_8334081 : Nat := 4279389366503512603459765

theorem tailTrace_8334081 : CollatzResearch.WordTrace tailWord_8334081 prefixEnd_8334081 4279389366503512603459765 := by
  unfold tailWord_8334081
  simp only [CollatzResearch.WordTrace]
  refine ⟨303968906120055359561410097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202645937413370239707606731 303968906120055359561410097)
  ·
    refine ⟨227976679590041519671057573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303968906120055359561410097 227976679590041519671057573)
    ·
      refine ⟨42745627423132784938323295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227976679590041519671057573 42745627423132784938323295)
      ·
        refine ⟨64118441134699177407484943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42745627423132784938323295 64118441134699177407484943)
        ·
          refine ⟨96177661702048766111227415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64118441134699177407484943 96177661702048766111227415)
          ·
            refine ⟨144266492553073149166841123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96177661702048766111227415 144266492553073149166841123)
            ·
              refine ⟨216399738829609723750261685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144266492553073149166841123 216399738829609723750261685)
              ·
                refine ⟨20287475515275911601587033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216399738829609723750261685 20287475515275911601587033)
                ·
                  refine ⟨15215606636456933701190275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20287475515275911601587033 15215606636456933701190275)
                  ·
                    refine ⟨22823409954685400551785413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15215606636456933701190275 22823409954685400551785413)
                    ·
                      refine ⟨4279389366503512603459765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22823409954685400551785413 4279389366503512603459765)
                      ·
                        rfl

theorem cell23_8334081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_8334081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334081 prefixEnd_8334081 := by exact prefixLift 8334081
  have htrace : WordTrace (prefixWord ++ tailWord_8334081) baseStart_8334081 baseEnd_8334081 := by
    simpa [prefixWord, tailWord_8334081, baseEnd_8334081] using wordTrace_append hprefix tailTrace_8334081
  have hstable : (prefixWord ++ tailWord_8334081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334081).length < 2 ^ (prefixWord ++ tailWord_8334081).sum := by decide
  have hdescent : baseEnd_8334081 < baseStart_8334081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334108 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_8334108 : Nat := 118140960795 + 8334108 * 2 ^ 59
def prefixEnd_8334108 : Nat := 4983230072969 + 3 ^ 40 * 8334108 * 2
def baseEnd_8334108 : Nat := 1426467743493727999274047

theorem tailTrace_8334108 : CollatzResearch.WordTrace tailWord_8334108 prefixEnd_8334108 1426467743493727999274047 := by
  unfold tailWord_8334108
  simp only [CollatzResearch.WordTrace]
  refine ⟨151984945445478771586321489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202646593927305028781761985 151984945445478771586321489)
  ·
    refine ⟨113988709084109078689741117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151984945445478771586321489 113988709084109078689741117)
    ·
      refine ⟨42745765906540904508652919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113988709084109078689741117 42745765906540904508652919)
      ·
        refine ⟨64118648859811356762979379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42745765906540904508652919 64118648859811356762979379)
        ·
          refine ⟨96177973289717035144469069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64118648859811356762979379 96177973289717035144469069)
          ·
            refine ⟨36066739983643888179175901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96177973289717035144469069 36066739983643888179175901)
            ·
              refine ⟨13525027493866458067190963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36066739983643888179175901 13525027493866458067190963)
              ·
                refine ⟨20287541240799687100786445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13525027493866458067190963 20287541240799687100786445)
                ·
                  refine ⟨7607827965299882662794917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20287541240799687100786445 7607827965299882662794917)
                  ·
                    refine ⟨1426467743493727999274047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607827965299882662794917 1426467743493727999274047)
                    ·
                      rfl

theorem cell23_8334108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_8334108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334108 prefixEnd_8334108 := by exact prefixLift 8334108
  have htrace : WordTrace (prefixWord ++ tailWord_8334108) baseStart_8334108 baseEnd_8334108 := by
    simpa [prefixWord, tailWord_8334108, baseEnd_8334108] using wordTrace_append hprefix tailTrace_8334108
  have hstable : (prefixWord ++ tailWord_8334108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334108).length < 2 ^ (prefixWord ++ tailWord_8334108).sum := by decide
  have hdescent : baseEnd_8334108 < baseStart_8334108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334144 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_8334144 : Nat := 118140960795 + 8334144 * 2 ^ 59
def prefixEnd_8334144 : Nat := 4983230072969 + 3 ^ 40 * 8334144 * 2
def baseEnd_8334144 : Nat := 4279421715784745856971975

theorem tailTrace_8334144 : CollatzResearch.WordTrace tailWord_8334144 prefixEnd_8334144 4279421715784745856971975 := by
  unfold tailWord_8334144
  simp only [CollatzResearch.WordTrace]
  refine ⟨151985601959413560660476743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202647469279218080880635657 151985601959413560660476743)
  ·
    refine ⟨227978402939120340990715115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151985601959413560660476743 227978402939120340990715115)
    ·
      refine ⟨341967604408680511486072673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227978402939120340990715115 341967604408680511486072673)
      ·
        refine ⟨256475703306510383614554505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341967604408680511486072673 256475703306510383614554505)
        ·
          refine ⟨192356777479882787710915879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256475703306510383614554505 192356777479882787710915879)
          ·
            refine ⟨288535166219824181566373819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192356777479882787710915879 288535166219824181566373819)
            ·
              refine ⟨432802749329736272349560729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288535166219824181566373819 432802749329736272349560729)
              ·
                refine ⟨324602061997302204262170547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432802749329736272349560729 324602061997302204262170547)
                ·
                  refine ⟨486903092995953306393255821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324602061997302204262170547 486903092995953306393255821)
                  ·
                    refine ⟨182588659873482489897470933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486903092995953306393255821 182588659873482489897470933)
                    ·
                      refine ⟨4279421715784745856971975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182588659873482489897470933 4279421715784745856971975)
                      ·
                        rfl

theorem cell23_8334144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_8334144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334144 prefixEnd_8334144 := by exact prefixLift 8334144
  have htrace : WordTrace (prefixWord ++ tailWord_8334144) baseStart_8334144 baseEnd_8334144 := by
    simpa [prefixWord, tailWord_8334144, baseEnd_8334144] using wordTrace_append hprefix tailTrace_8334144
  have hstable : (prefixWord ++ tailWord_8334144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334144).length < 2 ^ (prefixWord ++ tailWord_8334144).sum := by decide
  have hdescent : baseEnd_8334144 < baseStart_8334144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334181 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_8334181 : Nat := 118140960795 + 8334181 * 2 ^ 59
def prefixEnd_8334181 : Nat := 4983230072969 + 3 ^ 40 * 8334181 * 2
def baseEnd_8334181 : Nat := 1426480238189654070736435

theorem tailTrace_8334181 : CollatzResearch.WordTrace tailWord_8334181 prefixEnd_8334181 1426480238189654070736435 := by
  unfold tailWord_8334181
  simp only [CollatzResearch.WordTrace]
  refine ⟨303972553419693076640050397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202648368946462051093366931 303972553419693076640050397)
  ·
    refine ⟨113989707532384903740018899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303972553419693076640050397 113989707532384903740018899)
    ·
      refine ⟨170984561298577355610028349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113989707532384903740018899 170984561298577355610028349)
      ·
        refine ⟨64119210486966508353760631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170984561298577355610028349 64119210486966508353760631)
        ·
          refine ⟨96178815730449762530640947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64119210486966508353760631 96178815730449762530640947)
          ·
            refine ⟨144268223595674643795961421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96178815730449762530640947 144268223595674643795961421)
            ·
              refine ⟨54100583848377991423485533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144268223595674643795961421 54100583848377991423485533)
              ·
                refine ⟨20287718943141746783807075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54100583848377991423485533 20287718943141746783807075)
                ·
                  refine ⟨30431578414712620175710613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20287718943141746783807075 30431578414712620175710613)
                  ·
                    refine ⟨1426480238189654070736435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30431578414712620175710613 1426480238189654070736435)
                    ·
                      rfl

theorem cell23_8334181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_8334181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334181 prefixEnd_8334181 := by exact prefixLift 8334181
  have htrace : WordTrace (prefixWord ++ tailWord_8334181) baseStart_8334181 baseEnd_8334181 := by
    simpa [prefixWord, tailWord_8334181, baseEnd_8334181] using wordTrace_append hprefix tailTrace_8334181
  have hstable : (prefixWord ++ tailWord_8334181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334181).length < 2 ^ (prefixWord ++ tailWord_8334181).sum := by decide
  have hdescent : baseEnd_8334181 < baseStart_8334181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334188 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_8334188 : Nat := 118140960795 + 8334188 * 2 ^ 59
def prefixEnd_8334188 : Nat := 4983230072969 + 3 ^ 40 * 8334188 * 2
def baseEnd_8334188 : Nat := 4279444308933543684821773

theorem tailTrace_8334188 : CollatzResearch.WordTrace tailWord_8334188 prefixEnd_8334188 4279444308933543684821773 := by
  unfold tailWord_8334188
  simp only [CollatzResearch.WordTrace]
  refine ⟨151986404365333858417777609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202648539153778477890370145 151986404365333858417777609)
  ·
    refine ⟨113989803274000393813333207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151986404365333858417777609 113989803274000393813333207)
    ·
      refine ⟨170984704911000590719999811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113989803274000393813333207 170984704911000590719999811)
      ·
        refine ⟨256477057366500886079999717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170984704911000590719999811 256477057366500886079999717)
        ·
          refine ⟨48089448256218916139999947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256477057366500886079999717 48089448256218916139999947)
          ·
            refine ⟨72134172384328374209999921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48089448256218916139999947 72134172384328374209999921)
            ·
              refine ⟨54100629288246280657499941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72134172384328374209999921 54100629288246280657499941)
              ·
                refine ⟨10143867991546177623281239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54100629288246280657499941 10143867991546177623281239)
                ·
                  refine ⟨15215801987319266434921859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143867991546177623281239 15215801987319266434921859)
                  ·
                    refine ⟨22823702980978899652382789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15215801987319266434921859 22823702980978899652382789)
                    ·
                      refine ⟨4279444308933543684821773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22823702980978899652382789 4279444308933543684821773)
                      ·
                        rfl

theorem cell23_8334188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_8334188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334188 prefixEnd_8334188 := by exact prefixLift 8334188
  have htrace : WordTrace (prefixWord ++ tailWord_8334188) baseStart_8334188 baseEnd_8334188 := by
    simpa [prefixWord, tailWord_8334188, baseEnd_8334188] using wordTrace_append hprefix tailTrace_8334188
  have hstable : (prefixWord ++ tailWord_8334188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334188).length < 2 ^ (prefixWord ++ tailWord_8334188).sum := by decide
  have hdescent : baseEnd_8334188 < baseStart_8334188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334205 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_8334205 : Nat := 118140960795 + 8334205 * 2 ^ 59
def prefixEnd_8334205 : Nat := 4983230072969 + 3 ^ 40 * 8334205 * 2
def baseEnd_8334205 : Nat := 4279453038104670118309195

theorem tailTrace_8334205 : CollatzResearch.WordTrace tailWord_8334205 prefixEnd_8334205 4279453038104670118309195 := by
  unfold tailWord_8334205
  simp only [CollatzResearch.WordTrace]
  refine ⟨303973428771606128738924069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202648952514404085825949379 303973428771606128738924069)
  ·
    refine ⟨56995017894676149138548263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303973428771606128738924069 56995017894676149138548263)
    ·
      refine ⟨85492526842014223707822395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56995017894676149138548263 85492526842014223707822395)
      ·
        refine ⟨128238790263021335561733593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85492526842014223707822395 128238790263021335561733593)
        ·
          refine ⟨96179092697266001671300195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128238790263021335561733593 96179092697266001671300195)
          ·
            refine ⟨144268639045899002506950293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96179092697266001671300195 144268639045899002506950293)
            ·
              refine ⟨6762592455276515742513295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144268639045899002506950293 6762592455276515742513295)
              ·
                refine ⟨10143888682914773613769943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762592455276515742513295 10143888682914773613769943)
                ·
                  refine ⟨15215833024372160420654915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143888682914773613769943 15215833024372160420654915)
                  ·
                    refine ⟨22823749536558240630982373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15215833024372160420654915 22823749536558240630982373)
                    ·
                      refine ⟨4279453038104670118309195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22823749536558240630982373 4279453038104670118309195)
                      ·
                        rfl

theorem cell23_8334205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_8334205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334205 prefixEnd_8334205 := by exact prefixLift 8334205
  have htrace : WordTrace (prefixWord ++ tailWord_8334205) baseStart_8334205 baseEnd_8334205 := by
    simpa [prefixWord, tailWord_8334205, baseEnd_8334205] using wordTrace_append hprefix tailTrace_8334205
  have hstable : (prefixWord ++ tailWord_8334205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334205).length < 2 ^ (prefixWord ++ tailWord_8334205).sum := by decide
  have hdescent : baseEnd_8334205 < baseStart_8334205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334215 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 2, 4]
def baseStart_8334215 : Nat := 118140960795 + 8334215 * 2 ^ 59
def prefixEnd_8334215 : Nat := 4983230072969 + 3 ^ 40 * 8334215 * 2
def baseEnd_8334215 : Nat := 1426486057637071693061383

theorem tailTrace_8334215 : CollatzResearch.WordTrace tailWord_8334215 prefixEnd_8334215 1426486057637071693061383 := by
  unfold tailWord_8334215
  simp only [CollatzResearch.WordTrace]
  refine ⟨303973793501569900446788099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202649195667713266964525399 303973793501569900446788099)
  ·
    refine ⟨455960690252354850670182149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303973793501569900446788099 455960690252354850670182149)
    ·
      refine ⟨85492629422316534500659153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455960690252354850670182149 85492629422316534500659153)
      ·
        refine ⟨64119472066737400875494365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85492629422316534500659153 64119472066737400875494365)
        ·
          refine ⟨24044802025026525328310387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64119472066737400875494365 24044802025026525328310387)
          ·
            refine ⟨36067203037539787992465581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24044802025026525328310387 36067203037539787992465581)
            ·
              refine ⟨13525201139077420497174593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36067203037539787992465581 13525201139077420497174593)
              ·
                refine ⟨10143900854308065372880945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13525201139077420497174593 10143900854308065372880945)
                ·
                  refine ⟨7607925640731049029660709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10143900854308065372880945 7607925640731049029660709)
                  ·
                    refine ⟨1426486057637071693061383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607925640731049029660709 1426486057637071693061383)
                    ·
                      rfl

theorem cell23_8334215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_8334215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334215 prefixEnd_8334215 := by exact prefixLift 8334215
  have htrace : WordTrace (prefixWord ++ tailWord_8334215) baseStart_8334215 baseEnd_8334215 := by
    simpa [prefixWord, tailWord_8334215, baseEnd_8334215] using wordTrace_append hprefix tailTrace_8334215
  have hstable : (prefixWord ++ tailWord_8334215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334215).length < 2 ^ (prefixWord ++ tailWord_8334215).sum := by decide
  have hdescent : baseEnd_8334215 < baseStart_8334215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334242 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_8334242 : Nat := 118140960795 + 8334242 * 2 ^ 59
def prefixEnd_8334242 : Nat := 4983230072969 + 3 ^ 40 * 8334242 * 2
def baseEnd_8334242 : Nat := 4279472036888886473546525

theorem tailTrace_8334242 : CollatzResearch.WordTrace tailWord_8334242 prefixEnd_8334242 4279472036888886473546525 := by
  unfold tailWord_8334242
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993694568118021014505245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202649852181648056038680653 75993694568118021014505245)
  ·
    refine ⟨28497635463044257880439467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75993694568118021014505245 28497635463044257880439467)
    ·
      refine ⟨42746453194566386820659201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497635463044257880439467 42746453194566386820659201)
      ·
        refine ⟨32059839895924790115494401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42746453194566386820659201 32059839895924790115494401)
        ·
          refine ⟨24044879921943592586620801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32059839895924790115494401 24044879921943592586620801)
          ·
            refine ⟨18033659941457694439965601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24044879921943592586620801 18033659941457694439965601)
            ·
              refine ⟨13525244956093270829974201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18033659941457694439965601 13525244956093270829974201)
              ·
                refine ⟨10143933717069953122480651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13525244956093270829974201 10143933717069953122480651)
                ·
                  refine ⟨15215900575604929683720977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143933717069953122480651 15215900575604929683720977)
                  ·
                    refine ⟨11411925431703697262790733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15215900575604929683720977 11411925431703697262790733)
                    ·
                      refine ⟨4279472036888886473546525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411925431703697262790733 4279472036888886473546525)
                      ·
                        rfl

theorem cell23_8334242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_8334242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334242 prefixEnd_8334242 := by exact prefixLift 8334242
  have htrace : WordTrace (prefixWord ++ tailWord_8334242) baseStart_8334242 baseEnd_8334242 := by
    simpa [prefixWord, tailWord_8334242, baseEnd_8334242] using wordTrace_append hprefix tailTrace_8334242
  have hstable : (prefixWord ++ tailWord_8334242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334242).length < 2 ^ (prefixWord ++ tailWord_8334242).sum := by decide
  have hdescent : baseEnd_8334242 < baseStart_8334242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334271 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 6]
def baseStart_8334271 : Nat := 118140960795 + 8334271 * 2 ^ 59
def prefixEnd_8334271 : Nat := 4983230072969 + 3 ^ 40 * 8334271 * 2
def baseEnd_8334271 : Nat := 1426495642609288953361297

theorem tailTrace_8334271 : CollatzResearch.WordTrace tailWord_8334271 prefixEnd_8334271 1426495642609288953361297 := by
  unfold tailWord_8334271
  simp only [CollatzResearch.WordTrace]
  refine ⟨303975835989367022010826667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202650557326244681340551111 303975835989367022010826667)
  ·
    refine ⟨455963753984050533016240001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303975835989367022010826667 455963753984050533016240001)
    ·
      refine ⟨341972815488037899762180001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455963753984050533016240001 341972815488037899762180001)
      ·
        refine ⟨256479611616028424821635001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341972815488037899762180001 256479611616028424821635001)
        ·
          refine ⟨192359708712021318616226251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256479611616028424821635001 192359708712021318616226251)
          ·
            refine ⟨288539563068031977924339377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192359708712021318616226251 288539563068031977924339377)
            ·
              refine ⟨216404672301023983443254533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288539563068031977924339377 216404672301023983443254533)
              ·
                refine ⟨40575876056441996895610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216404672301023983443254533 40575876056441996895610225)
                ·
                  refine ⟨30431907042331497671707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40575876056441996895610225 30431907042331497671707669)
                  ·
                    refine ⟨1426495642609288953361297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30431907042331497671707669 1426495642609288953361297)
                    ·
                      rfl

theorem cell23_8334271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_8334271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334271 prefixEnd_8334271 := by exact prefixLift 8334271
  have htrace : WordTrace (prefixWord ++ tailWord_8334271) baseStart_8334271 baseEnd_8334271 := by
    simpa [prefixWord, tailWord_8334271, baseEnd_8334271] using wordTrace_append hprefix tailTrace_8334271
  have hstable : (prefixWord ++ tailWord_8334271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334271).length < 2 ^ (prefixWord ++ tailWord_8334271).sum := by decide
  have hdescent : baseEnd_8334271 < baseStart_8334271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334281 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_8334281 : Nat := 118140960795 + 8334281 * 2 ^ 59
def prefixEnd_8334281 : Nat := 4983230072969 + 3 ^ 40 * 8334281 * 2
def baseEnd_8334281 : Nat := 4279492062634411820958845

theorem tailTrace_8334281 : CollatzResearch.WordTrace tailWord_8334281 prefixEnd_8334281 4279492062634411820958845 := by
  unfold tailWord_8334281
  simp only [CollatzResearch.WordTrace]
  refine ⟨303976200719330793718690697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202650800479553862479127131 303976200719330793718690697)
  ·
    refine ⟨227982150539498095289018023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303976200719330793718690697 227982150539498095289018023)
    ·
      refine ⟨341973225809247142933527035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227982150539498095289018023 341973225809247142933527035)
      ·
        refine ⟨512959838713870714400290553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341973225809247142933527035 512959838713870714400290553)
        ·
          refine ⟨384719879035403035800217915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512959838713870714400290553 384719879035403035800217915)
          ·
            refine ⟨577079818553104553700326873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384719879035403035800217915 577079818553104553700326873)
            ·
              refine ⟨432809863914828415275245155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577079818553104553700326873 432809863914828415275245155)
              ·
                refine ⟨649214795872242622912867733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432809863914828415275245155 649214795872242622912867733)
                ·
                  refine ⟨30431943556511372949040675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 649214795872242622912867733 30431943556511372949040675)
                  ·
                    refine ⟨45647915334767059423561013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30431943556511372949040675 45647915334767059423561013)
                    ·
                      refine ⟨4279492062634411820958845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45647915334767059423561013 4279492062634411820958845)
                      ·
                        rfl

theorem cell23_8334281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_8334281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334281 prefixEnd_8334281 := by exact prefixLift 8334281
  have htrace : WordTrace (prefixWord ++ tailWord_8334281) baseStart_8334281 baseEnd_8334281 := by
    simpa [prefixWord, tailWord_8334281, baseEnd_8334281] using wordTrace_append hprefix tailTrace_8334281
  have hstable : (prefixWord ++ tailWord_8334281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334281).length < 2 ^ (prefixWord ++ tailWord_8334281).sum := by decide
  have hdescent : baseEnd_8334281 < baseStart_8334281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334295 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_8334295 : Nat := 118140960795 + 8334295 * 2 ^ 59
def prefixEnd_8334295 : Nat := 4983230072969 + 3 ^ 40 * 8334295 * 2
def baseEnd_8334295 : Nat := 4279499251363574766183781

theorem tailTrace_8334295 : CollatzResearch.WordTrace tailWord_8334295 prefixEnd_8334295 4279499251363574766183781 := by
  unfold tailWord_8334295
  simp only [CollatzResearch.WordTrace]
  refine ⟨303976711341280074109700339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202651140894186716073133559 303976711341280074109700339)
  ·
    refine ⟨455965067011920111164550509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303976711341280074109700339 455965067011920111164550509)
    ·
      refine ⟨170986900129470041686706441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455965067011920111164550509 170986900129470041686706441)
      ·
        refine ⟨128240175097102531265029831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170986900129470041686706441 128240175097102531265029831)
        ·
          refine ⟨192360262645653796897544747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128240175097102531265029831 192360262645653796897544747)
          ·
            refine ⟨288540393968480695346317121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192360262645653796897544747 288540393968480695346317121)
            ·
              refine ⟨216405295476360521509737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288540393968480695346317121 216405295476360521509737841)
              ·
                refine ⟨162303971607270391132303381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216405295476360521509737841 162303971607270391132303381)
                ·
                  refine ⟨7607998669090799584326721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162303971607270391132303381 7607998669090799584326721)
                  ·
                    refine ⟨5705999001818099688245041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607998669090799584326721 5705999001818099688245041)
                    ·
                      refine ⟨4279499251363574766183781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705999001818099688245041 4279499251363574766183781)
                      ·
                        rfl

theorem cell23_8334295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_8334295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334295 prefixEnd_8334295 := by exact prefixLift 8334295
  have htrace : WordTrace (prefixWord ++ tailWord_8334295) baseStart_8334295 baseEnd_8334295 := by
    simpa [prefixWord, tailWord_8334295, baseEnd_8334295] using wordTrace_append hprefix tailTrace_8334295
  have hstable : (prefixWord ++ tailWord_8334295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334295).length < 2 ^ (prefixWord ++ tailWord_8334295).sum := by decide
  have hdescent : baseEnd_8334295 < baseStart_8334295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334298 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_8334298 : Nat := 118140960795 + 8334298 * 2 ^ 59
def prefixEnd_8334298 : Nat := 4983230072969 + 3 ^ 40 * 8334298 * 2
def baseEnd_8334298 : Nat := 4279500791805538254446267

theorem tailTrace_8334298 : CollatzResearch.WordTrace tailWord_8334298 prefixEnd_8334298 4279500791805538254446267 := by
  unfold tailWord_8334298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75994205190067301405514887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202651213840179470414706365 75994205190067301405514887)
  ·
    refine ⟨113991307785100952108272331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75994205190067301405514887 113991307785100952108272331)
    ·
      refine ⟨170986961677651428162408497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113991307785100952108272331 170986961677651428162408497)
      ·
        refine ⟨128240221258238571121806373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170986961677651428162408497 128240221258238571121806373)
        ·
          refine ⟨24045041485919732085338695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128240221258238571121806373 24045041485919732085338695)
          ·
            refine ⟨36067562228879598128008043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24045041485919732085338695 36067562228879598128008043)
            ·
              refine ⟨54101343343319397192012065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36067562228879598128008043 54101343343319397192012065)
              ·
                refine ⟨40576007507489547894009049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54101343343319397192012065 40576007507489547894009049)
                ·
                  refine ⟨30432005630617160920506787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40576007507489547894009049 30432005630617160920506787)
                  ·
                    refine ⟨45648008445925741380760181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30432005630617160920506787 45648008445925741380760181)
                    ·
                      refine ⟨4279500791805538254446267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45648008445925741380760181 4279500791805538254446267)
                      ·
                        rfl

theorem cell23_8334298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_8334298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334298 prefixEnd_8334298 := by exact prefixLift 8334298
  have htrace : WordTrace (prefixWord ++ tailWord_8334298) baseStart_8334298 baseEnd_8334298 := by
    simpa [prefixWord, tailWord_8334298, baseEnd_8334298] using wordTrace_append hprefix tailTrace_8334298
  have hstable : (prefixWord ++ tailWord_8334298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334298).length < 2 ^ (prefixWord ++ tailWord_8334298).sum := by decide
  have hdescent : baseEnd_8334298 < baseStart_8334298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334324 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8334324 : Nat := 118140960795 + 8334324 * 2 ^ 59
def prefixEnd_8334324 : Nat := 4983230072969 + 3 ^ 40 * 8334324 * 2
def baseEnd_8334324 : Nat := 4279514142302555152721149

theorem tailTrace_8334324 : CollatzResearch.WordTrace tailWord_8334324 prefixEnd_8334324 4279514142302555152721149 := by
  unfold tailWord_8334324
  simp only [CollatzResearch.WordTrace]
  refine ⟨151988884529087506031253013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202651846038783341375004017 151988884529087506031253013)
  ·
    refine ⟨7124478962300976845214985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151988884529087506031253013 7124478962300976845214985)
    ·
      refine ⟨5343359221725732633911239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124478962300976845214985 5343359221725732633911239)
      ·
        refine ⟨8015038832588598950866859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343359221725732633911239 8015038832588598950866859)
        ·
          refine ⟨12022558248882898426300289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015038832588598950866859 12022558248882898426300289)
          ·
            refine ⟨9016918686662173819725217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022558248882898426300289 9016918686662173819725217)
            ·
              refine ⟨6762689014996630364793913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016918686662173819725217 6762689014996630364793913)
              ·
                refine ⟨5072016761247472773595435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762689014996630364793913 5072016761247472773595435)
                ·
                  refine ⟨7608025141871209160393153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072016761247472773595435 7608025141871209160393153)
                  ·
                    refine ⟨5706018856403406870294865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608025141871209160393153 5706018856403406870294865)
                    ·
                      refine ⟨4279514142302555152721149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706018856403406870294865 4279514142302555152721149)
                      ·
                        rfl

theorem cell23_8334324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8334324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334324 prefixEnd_8334324 := by exact prefixLift 8334324
  have htrace : WordTrace (prefixWord ++ tailWord_8334324) baseStart_8334324 baseEnd_8334324 := by
    simpa [prefixWord, tailWord_8334324, baseEnd_8334324] using wordTrace_append hprefix tailTrace_8334324
  have hstable : (prefixWord ++ tailWord_8334324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334324).length < 2 ^ (prefixWord ++ tailWord_8334324).sum := by decide
  have hdescent : baseEnd_8334324 < baseStart_8334324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334328 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_8334328 : Nat := 118140960795 + 8334328 * 2 ^ 59
def prefixEnd_8334328 : Nat := 4983230072969 + 3 ^ 40 * 8334328 * 2
def baseEnd_8334328 : Nat := 4279516196225173137071129

theorem tailTrace_8334328 : CollatzResearch.WordTrace tailWord_8334328 prefixEnd_8334328 4279516196225173137071129 := by
  unfold tailWord_8334328
  simp only [CollatzResearch.WordTrace]
  refine ⟨151988957475080260372825819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202651943300107013830434425 151988957475080260372825819)
  ·
    refine ⟨227983436212620390559238729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151988957475080260372825819 227983436212620390559238729)
    ·
      refine ⟨170987577159465292919429047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227983436212620390559238729 170987577159465292919429047)
      ·
        refine ⟨256481365739197939379143571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170987577159465292919429047 256481365739197939379143571)
        ·
          refine ⟨384722048608796909068715357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256481365739197939379143571 384722048608796909068715357)
          ·
            refine ⟨144270768228298840900768259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384722048608796909068715357 144270768228298840900768259)
            ·
              refine ⟨216406152342448261351152389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144270768228298840900768259 216406152342448261351152389)
              ·
                refine ⟨40576153564209049003341073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216406152342448261351152389 40576153564209049003341073)
                ·
                  refine ⟨30432115173156786752505805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40576153564209049003341073 30432115173156786752505805)
                  ·
                    refine ⟨11412043189933795032189677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30432115173156786752505805 11412043189933795032189677)
                    ·
                      refine ⟨4279516196225173137071129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412043189933795032189677 4279516196225173137071129)
                      ·
                        rfl

theorem cell23_8334328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_8334328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334328 prefixEnd_8334328 := by exact prefixLift 8334328
  have htrace : WordTrace (prefixWord ++ tailWord_8334328) baseStart_8334328 baseEnd_8334328 := by
    simpa [prefixWord, tailWord_8334328, baseEnd_8334328] using wordTrace_append hprefix tailTrace_8334328
  have hstable : (prefixWord ++ tailWord_8334328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334328).length < 2 ^ (prefixWord ++ tailWord_8334328).sum := by decide
  have hdescent : baseEnd_8334328 < baseStart_8334328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334331 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 7]
def baseStart_8334331 : Nat := 118140960795 + 8334331 * 2 ^ 59
def prefixEnd_8334331 : Nat := 4983230072969 + 3 ^ 40 * 8334331 * 2
def baseEnd_8334331 : Nat := 1426505912222378875111205

theorem tailTrace_8334331 : CollatzResearch.WordTrace tailWord_8334331 prefixEnd_8334331 1426505912222378875111205 := by
  unfold tailWord_8334331
  simp only [CollatzResearch.WordTrace]
  refine ⟨303978024369149652258010847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202652016246099768172007231 303978024369149652258010847)
  ·
    refine ⟨455967036553724478387016271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303978024369149652258010847 455967036553724478387016271)
    ·
      refine ⟨683950554830586717580524407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455967036553724478387016271 683950554830586717580524407)
      ·
        refine ⟨1025925832245880076370786611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683950554830586717580524407 1025925832245880076370786611)
        ·
          refine ⟨1538888748368820114556179917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025925832245880076370786611 1538888748368820114556179917)
          ·
            refine ⟨577083280638307542958567469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1538888748368820114556179917 577083280638307542958567469)
            ·
              refine ⟨216406230239365328609462801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577083280638307542958567469 216406230239365328609462801)
              ·
                refine ⟨162304672679523996457097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216406230239365328609462801 162304672679523996457097101)
                ·
                  refine ⟨60864252254821498671411413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162304672679523996457097101 60864252254821498671411413)
                  ·
                    refine ⟨1426505912222378875111205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60864252254821498671411413 1426505912222378875111205)
                    ·
                      rfl

theorem cell23_8334331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_8334331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334331 prefixEnd_8334331 := by exact prefixLift 8334331
  have htrace : WordTrace (prefixWord ++ tailWord_8334331) baseStart_8334331 baseEnd_8334331 := by
    simpa [prefixWord, tailWord_8334331, baseEnd_8334331] using wordTrace_append hprefix tailTrace_8334331
  have hstable : (prefixWord ++ tailWord_8334331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334331).length < 2 ^ (prefixWord ++ tailWord_8334331).sum := by decide
  have hdescent : baseEnd_8334331 < baseStart_8334331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334365 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_8334365 : Nat := 118140960795 + 8334365 * 2 ^ 59
def prefixEnd_8334365 : Nat := 4983230072969 + 3 ^ 40 * 8334365 * 2
def baseEnd_8334365 : Nat := 1426511731669796497436153

theorem tailTrace_8334365 : CollatzResearch.WordTrace tailWord_8334365 prefixEnd_8334365 1426511731669796497436153 := by
  unfold tailWord_8334365
  simp only [CollatzResearch.WordTrace]
  refine ⟨303979264451026476064748549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202652842967350984043165699 303979264451026476064748549)
  ·
    refine ⟨56996112084567464262140353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303979264451026476064748549 56996112084567464262140353)
    ·
      refine ⟨42747084063425598196605265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56996112084567464262140353 42747084063425598196605265)
      ·
        refine ⟨32060313047569198647453949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42747084063425598196605265 32060313047569198647453949)
        ·
          refine ⟨12022617392838449492795231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32060313047569198647453949 12022617392838449492795231)
          ·
            refine ⟨18033926089257674239192847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022617392838449492795231 18033926089257674239192847)
            ·
              refine ⟨27050889133886511358789271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18033926089257674239192847 27050889133886511358789271)
              ·
                refine ⟨40576333700829767038183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27050889133886511358789271 40576333700829767038183907)
                ·
                  refine ⟨60864500551244650557275861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40576333700829767038183907 60864500551244650557275861)
                  ·
                    refine ⟨1426511731669796497436153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60864500551244650557275861 1426511731669796497436153)
                    ·
                      rfl

theorem cell23_8334365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_8334365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334365 prefixEnd_8334365 := by exact prefixLift 8334365
  have htrace : WordTrace (prefixWord ++ tailWord_8334365) baseStart_8334365 baseEnd_8334365 := by
    simpa [prefixWord, tailWord_8334365, baseEnd_8334365] using wordTrace_append hprefix tailTrace_8334365
  have hstable : (prefixWord ++ tailWord_8334365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334365).length < 2 ^ (prefixWord ++ tailWord_8334365).sum := by decide
  have hdescent : baseEnd_8334365 < baseStart_8334365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334385 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_8334385 : Nat := 118140960795 + 8334385 * 2 ^ 59
def prefixEnd_8334385 : Nat := 4983230072969 + 3 ^ 40 * 8334385 * 2
def baseEnd_8334385 : Nat := 4279545464622479414058367

theorem tailTrace_8334385 : CollatzResearch.WordTrace tailWord_8334385 prefixEnd_8334385 4279545464622479414058367 := by
  unfold tailWord_8334385
  simp only [CollatzResearch.WordTrace]
  refine ⟨303979993910954019480476609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202653329273969346320317739 303979993910954019480476609)
  ·
    refine ⟨227984995433215514610357457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303979993910954019480476609 227984995433215514610357457)
    ·
      refine ⟨170988746574911635957768093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227984995433215514610357457 170988746574911635957768093)
      ·
        refine ⟨64120779965591863484163035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170988746574911635957768093 64120779965591863484163035)
        ·
          refine ⟨96181169948387795226244553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64120779965591863484163035 96181169948387795226244553)
          ·
            refine ⟨72135877461290846419683415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96181169948387795226244553 72135877461290846419683415)
            ·
              refine ⟨108203816191936269629525123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72135877461290846419683415 108203816191936269629525123)
              ·
                refine ⟨162305724287904404444287685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108203816191936269629525123 162305724287904404444287685)
                ·
                  refine ⟨30432323303982075833303941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162305724287904404444287685 30432323303982075833303941)
                  ·
                    refine ⟨5706060619496639218744489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30432323303982075833303941 5706060619496639218744489)
                    ·
                      refine ⟨4279545464622479414058367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706060619496639218744489 4279545464622479414058367)
                      ·
                        rfl

theorem cell23_8334385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_8334385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334385 prefixEnd_8334385 := by exact prefixLift 8334385
  have htrace : WordTrace (prefixWord ++ tailWord_8334385) baseStart_8334385 baseEnd_8334385 := by
    simpa [prefixWord, tailWord_8334385, baseEnd_8334385] using wordTrace_append hprefix tailTrace_8334385
  have hstable : (prefixWord ++ tailWord_8334385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334385).length < 2 ^ (prefixWord ++ tailWord_8334385).sum := by decide
  have hdescent : baseEnd_8334385 < baseStart_8334385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334446 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_8334446 : Nat := 118140960795 + 8334446 * 2 ^ 59
def prefixEnd_8334446 : Nat := 4983230072969 + 3 ^ 40 * 8334446 * 2
def baseEnd_8334446 : Nat := 1426525595647467891798529

theorem tailTrace_8334446 : CollatzResearch.WordTrace tailWord_8334446 prefixEnd_8334446 1426525595647467891798529 := by
  unfold tailWord_8334446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997777345466628362305899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202654812509155351265631461 37997777345466628362305899)
  ·
    refine ⟨56996666018199942543458849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37997777345466628362305899 56996666018199942543458849)
    ·
      refine ⟨42747499513649956907594137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56996666018199942543458849 42747499513649956907594137)
      ·
        refine ⟨32060624635237467680695603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42747499513649956907594137 32060624635237467680695603)
        ·
          refine ⟨48090936952856201521043405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32060624635237467680695603 48090936952856201521043405)
          ·
            refine ⟨18034101357321075570391277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48090936952856201521043405 18034101357321075570391277)
            ·
              refine ⟨6762788008995403338896729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18034101357321075570391277 6762788008995403338896729)
              ·
                refine ⟨5072091006746552504172547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762788008995403338896729 5072091006746552504172547)
                ·
                  refine ⟨7608136510119828756258821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072091006746552504172547 7608136510119828756258821)
                  ·
                    refine ⟨1426525595647467891798529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608136510119828756258821 1426525595647467891798529)
                    ·
                      rfl

theorem cell23_8334446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_8334446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334446 prefixEnd_8334446 := by exact prefixLift 8334446
  have htrace : WordTrace (prefixWord ++ tailWord_8334446) baseStart_8334446 baseEnd_8334446 := by
    simpa [prefixWord, tailWord_8334446, baseEnd_8334446] using wordTrace_append hprefix tailTrace_8334446
  have hstable : (prefixWord ++ tailWord_8334446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334446).length < 2 ^ (prefixWord ++ tailWord_8334446).sum := by decide
  have hdescent : baseEnd_8334446 < baseStart_8334446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334472 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_8334472 : Nat := 118140960795 + 8334472 * 2 ^ 59
def prefixEnd_8334472 : Nat := 4983230072969 + 3 ^ 40 * 8334472 * 2
def baseEnd_8334472 : Nat := 1426530045813140191223489

theorem tailTrace_8334472 : CollatzResearch.WordTrace tailWord_8334472 prefixEnd_8334472 1426530045813140191223489 := by
  unfold tailWord_8334472
  simp only [CollatzResearch.WordTrace]
  refine ⟨151991583530819416669446835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202655444707759222225929113 151991583530819416669446835)
  ·
    refine ⟨227987375296229125004170253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151991583530819416669446835 227987375296229125004170253)
    ·
      refine ⟨85495265736085921876563845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227987375296229125004170253 85495265736085921876563845)
      ·
        refine ⟨16030362325516110351855721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85495265736085921876563845 16030362325516110351855721)
        ·
          refine ⟨12022771744137082763891791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030362325516110351855721 12022771744137082763891791)
          ·
            refine ⟨18034157616205624145837687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022771744137082763891791 18034157616205624145837687)
            ·
              refine ⟨27051236424308436218756531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034157616205624145837687 27051236424308436218756531)
              ·
                refine ⟨40576854636462654328134797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27051236424308436218756531 40576854636462654328134797)
                ·
                  refine ⟨15216320488673495373050549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40576854636462654328134797 15216320488673495373050549)
                  ·
                    refine ⟨1426530045813140191223489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15216320488673495373050549 1426530045813140191223489)
                    ·
                      rfl

theorem cell23_8334472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_8334472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334472 prefixEnd_8334472 := by exact prefixLift 8334472
  have htrace : WordTrace (prefixWord ++ tailWord_8334472) baseStart_8334472 baseEnd_8334472 := by
    simpa [prefixWord, tailWord_8334472, baseEnd_8334472] using wordTrace_append hprefix tailTrace_8334472
  have hstable : (prefixWord ++ tailWord_8334472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334472).length < 2 ^ (prefixWord ++ tailWord_8334472).sum := by decide
  have hdescent : baseEnd_8334472 < baseStart_8334472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334475 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 6, 2]
def baseStart_8334475 : Nat := 118140960795 + 8334475 * 2 ^ 59
def prefixEnd_8334475 : Nat := 4983230072969 + 3 ^ 40 * 8334475 * 2
def baseEnd_8334475 : Nat := 4279591677881384061932953

theorem tailTrace_8334475 : CollatzResearch.WordTrace tailWord_8334475 prefixEnd_8334475 4279591677881384061932953 := by
  unfold tailWord_8334475
  simp only [CollatzResearch.WordTrace]
  refine ⟨303983276480627964851252879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202655517653751976567501919 303983276480627964851252879)
  ·
    refine ⟨455974914720941947276879319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303983276480627964851252879 455974914720941947276879319)
    ·
      refine ⟨683962372081412920915318979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455974914720941947276879319 683962372081412920915318979)
      ·
        refine ⟨1025943558122119381372978469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683962372081412920915318979 1025943558122119381372978469)
        ·
          refine ⟨192364417147897384007433463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1025943558122119381372978469 192364417147897384007433463)
          ·
            refine ⟨288546625721846076011150195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192364417147897384007433463 288546625721846076011150195)
            ·
              refine ⟨432819938582769114016725293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288546625721846076011150195 432819938582769114016725293)
              ·
                refine ⟨162307476968538417756271985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432819938582769114016725293 162307476968538417756271985)
                ·
                  refine ⟨121730607726403813317203989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162307476968538417756271985 121730607726403813317203989)
                  ·
                    refine ⟨5706122237175178749243937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121730607726403813317203989 5706122237175178749243937)
                    ·
                      refine ⟨4279591677881384061932953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706122237175178749243937 4279591677881384061932953)
                      ·
                        rfl

theorem cell23_8334475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6, 2].length) (baseStart_8334475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334475 prefixEnd_8334475 := by exact prefixLift 8334475
  have htrace : WordTrace (prefixWord ++ tailWord_8334475) baseStart_8334475 baseEnd_8334475 := by
    simpa [prefixWord, tailWord_8334475, baseEnd_8334475] using wordTrace_append hprefix tailTrace_8334475
  have hstable : (prefixWord ++ tailWord_8334475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334475).length < 2 ^ (prefixWord ++ tailWord_8334475).sum := by decide
  have hdescent : baseEnd_8334475 < baseStart_8334475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334485 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_8334485 : Nat := 118140960795 + 8334485 * 2 ^ 59
def prefixEnd_8334485 : Nat := 4983230072969 + 3 ^ 40 * 8334485 * 2
def baseEnd_8334485 : Nat := 1426532270895976340935969

theorem tailTrace_8334485 : CollatzResearch.WordTrace tailWord_8334485 prefixEnd_8334485 1426532270895976340935969 := by
  unfold tailWord_8334485
  simp only [CollatzResearch.WordTrace]
  refine ⟨303983641210591736559116909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202655760807061157706077939 303983641210591736559116909)
  ·
    refine ⟨113993865453971901209668841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303983641210591736559116909 113993865453971901209668841)
    ·
      refine ⟨85495399090478925907251631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113993865453971901209668841 85495399090478925907251631)
      ·
        refine ⟨128243098635718388860877447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85495399090478925907251631 128243098635718388860877447)
        ·
          refine ⟨192364647953577583291316171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128243098635718388860877447 192364647953577583291316171)
          ·
            refine ⟨288546971930366374936974257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192364647953577583291316171 288546971930366374936974257)
            ·
              refine ⟨216410228947774781202730693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288546971930366374936974257 216410228947774781202730693)
              ·
                refine ⟨40576917927707771475512005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216410228947774781202730693 40576917927707771475512005)
                ·
                  refine ⟨7608172111445207151658501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40576917927707771475512005 7608172111445207151658501)
                  ·
                    refine ⟨1426532270895976340935969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608172111445207151658501 1426532270895976340935969)
                    ·
                      rfl

theorem cell23_8334485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_8334485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334485 prefixEnd_8334485 := by exact prefixLift 8334485
  have htrace : WordTrace (prefixWord ++ tailWord_8334485) baseStart_8334485 baseEnd_8334485 := by
    simpa [prefixWord, tailWord_8334485, baseEnd_8334485] using wordTrace_append hprefix tailTrace_8334485
  have hstable : (prefixWord ++ tailWord_8334485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334485).length < 2 ^ (prefixWord ++ tailWord_8334485).sum := by decide
  have hdescent : baseEnd_8334485 < baseStart_8334485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334503 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_8334503 : Nat := 118140960795 + 8334503 * 2 ^ 59
def prefixEnd_8334503 : Nat := 4983230072969 + 3 ^ 40 * 8334503 * 2
def baseEnd_8334503 : Nat := 4279606055339709952382825

theorem tailTrace_8334503 : CollatzResearch.WordTrace tailWord_8334503 prefixEnd_8334503 4279606055339709952382825 := by
  unfold tailWord_8334503
  simp only [CollatzResearch.WordTrace]
  refine ⟨303984297724526525633272163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202656198483017683755514775 303984297724526525633272163)
  ·
    refine ⟨455976446586789788449908245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303984297724526525633272163 455976446586789788449908245)
    ·
      refine ⟨21373895933755771333589449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455976446586789788449908245 21373895933755771333589449)
      ·
        refine ⟨16030421950316828500192087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21373895933755771333589449 16030421950316828500192087)
        ·
          refine ⟨24045632925475242750288131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16030421950316828500192087 24045632925475242750288131)
          ·
            refine ⟨36068449388212864125432197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24045632925475242750288131 36068449388212864125432197)
            ·
              refine ⟨6762834260289912023518537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36068449388212864125432197 6762834260289912023518537)
              ·
                refine ⟨5072125695217434017638903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762834260289912023518537 5072125695217434017638903)
                ·
                  refine ⟨7608188542826151026458355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072125695217434017638903 7608188542826151026458355)
                  ·
                    refine ⟨11412282814239226539687533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7608188542826151026458355 11412282814239226539687533)
                    ·
                      refine ⟨4279606055339709952382825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412282814239226539687533 4279606055339709952382825)
                      ·
                        rfl

theorem cell23_8334503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_8334503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334503 prefixEnd_8334503 := by exact prefixLift 8334503
  have htrace : WordTrace (prefixWord ++ tailWord_8334503) baseStart_8334503 baseEnd_8334503 := by
    simpa [prefixWord, tailWord_8334503, baseEnd_8334503] using wordTrace_append hprefix tailTrace_8334503
  have hstable : (prefixWord ++ tailWord_8334503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334503).length < 2 ^ (prefixWord ++ tailWord_8334503).sum := by decide
  have hdescent : baseEnd_8334503 < baseStart_8334503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334508 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_8334508 : Nat := 118140960795 + 8334508 * 2 ^ 59
def prefixEnd_8334508 : Nat := 4983230072969 + 3 ^ 40 * 8334508 * 2
def baseEnd_8334508 : Nat := 4279608622742982432820301

theorem tailTrace_8334508 : CollatzResearch.WordTrace tailWord_8334508 prefixEnd_8334508 4279608622742982432820301 := by
  unfold tailWord_8334508
  simp only [CollatzResearch.WordTrace]
  refine ⟨151992240044754205743602089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202656320059672274324802785 151992240044754205743602089)
  ·
    refine ⟨113994180033565654307701567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151992240044754205743602089 113994180033565654307701567)
    ·
      refine ⟨170991270050348481461552351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113994180033565654307701567 170991270050348481461552351)
      ·
        refine ⟨256486905075522722192328527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170991270050348481461552351 256486905075522722192328527)
        ·
          refine ⟨384730357613284083288492791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256486905075522722192328527 384730357613284083288492791)
          ·
            refine ⟨577095536419926124932739187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384730357613284083288492791 577095536419926124932739187)
            ·
              refine ⟨865643304629889187399108781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577095536419926124932739187 865643304629889187399108781)
              ·
                refine ⟨324616239236208445274665793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865643304629889187399108781 324616239236208445274665793)
                ·
                  refine ⟨243462179427156333955999345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324616239236208445274665793 243462179427156333955999345)
                  ·
                    refine ⟨182596634570367250466999509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243462179427156333955999345 182596634570367250466999509)
                    ·
                      refine ⟨4279608622742982432820301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182596634570367250466999509 4279608622742982432820301)
                      ·
                        rfl

theorem cell23_8334508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_8334508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334508 prefixEnd_8334508 := by exact prefixLift 8334508
  have htrace : WordTrace (prefixWord ++ tailWord_8334508) baseStart_8334508 baseEnd_8334508 := by
    simpa [prefixWord, tailWord_8334508, baseEnd_8334508] using wordTrace_append hprefix tailTrace_8334508
  have hstable : (prefixWord ++ tailWord_8334508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334508).length < 2 ^ (prefixWord ++ tailWord_8334508).sum := by decide
  have hdescent : baseEnd_8334508 < baseStart_8334508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334526 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_8334526 : Nat := 118140960795 + 8334526 * 2 ^ 59
def prefixEnd_8334526 : Nat := 4983230072969 + 3 ^ 40 * 8334526 * 2
def baseEnd_8334526 : Nat := 4279617865394763362395219

theorem tailTrace_8334526 : CollatzResearch.WordTrace tailWord_8334526 prefixEnd_8334526 4279617865394763362395219 := by
  unfold tailWord_8334526
  simp only [CollatzResearch.WordTrace]
  refine ⟨37998142075430400070169929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202656757735628800374239621 37998142075430400070169929)
  ·
    refine ⟨28498606556572800052627447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37998142075430400070169929 28498606556572800052627447)
    ·
      refine ⟨42747909834859200078941171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28498606556572800052627447 42747909834859200078941171)
      ·
        refine ⟨64121864752288800118411757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42747909834859200078941171 64121864752288800118411757)
        ·
          refine ⟨24045699282108300044404409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64121864752288800118411757 24045699282108300044404409)
          ·
            refine ⟨18034274461581225033303307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24045699282108300044404409 18034274461581225033303307)
            ·
              refine ⟨27051411692371837549954961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034274461581225033303307 27051411692371837549954961)
              ·
                refine ⟨20288558769278878162466221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27051411692371837549954961 20288558769278878162466221)
                ·
                  refine ⟨7608209538479579310924833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20288558769278878162466221 7608209538479579310924833)
                  ·
                    refine ⟨5706157153859684483193625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608209538479579310924833 5706157153859684483193625)
                    ·
                      refine ⟨4279617865394763362395219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706157153859684483193625 4279617865394763362395219)
                      ·
                        rfl

theorem cell23_8334526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_8334526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334526 prefixEnd_8334526 := by exact prefixLift 8334526
  have htrace : WordTrace (prefixWord ++ tailWord_8334526) baseStart_8334526 baseEnd_8334526 := by
    simpa [prefixWord, tailWord_8334526, baseEnd_8334526] using wordTrace_append hprefix tailTrace_8334526
  have hstable : (prefixWord ++ tailWord_8334526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334526).length < 2 ^ (prefixWord ++ tailWord_8334526).sum := by decide
  have hdescent : baseEnd_8334526 < baseStart_8334526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334529 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_8334529 : Nat := 118140960795 + 8334529 * 2 ^ 59
def prefixEnd_8334529 : Nat := 4983230072969 + 3 ^ 40 * 8334529 * 2
def baseEnd_8334529 : Nat := 4279619405836726850657705

theorem tailTrace_8334529 : CollatzResearch.WordTrace tailWord_8334529 prefixEnd_8334529 4279619405836726850657705 := by
  unfold tailWord_8334529
  simp only [CollatzResearch.WordTrace]
  refine ⟨303985246022432332073718641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202656830681621554715812427 303985246022432332073718641)
  ·
    refine ⟨227988934516824249055288981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303985246022432332073718641 227988934516824249055288981)
    ·
      refine ⟨10686981305476136674466671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227988934516824249055288981 10686981305476136674466671)
      ·
        refine ⟨16030471958214205011700007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686981305476136674466671 16030471958214205011700007)
        ·
          refine ⟨24045707937321307517550011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16030471958214205011700007 24045707937321307517550011)
          ·
            refine ⟨36068561905981961276325017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24045707937321307517550011 36068561905981961276325017)
            ·
              refine ⟨27051421429486470957243763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36068561905981961276325017 27051421429486470957243763)
              ·
                refine ⟨40577132144229706435865645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27051421429486470957243763 40577132144229706435865645)
                ·
                  refine ⟨15216424554086139913449617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40577132144229706435865645 15216424554086139913449617)
                  ·
                    refine ⟨11412318415564604935087213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15216424554086139913449617 11412318415564604935087213)
                    ·
                      refine ⟨4279619405836726850657705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412318415564604935087213 4279619405836726850657705)
                      ·
                        rfl

theorem cell23_8334529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_8334529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334529 prefixEnd_8334529 := by exact prefixLift 8334529
  have htrace : WordTrace (prefixWord ++ tailWord_8334529) baseStart_8334529 baseEnd_8334529 := by
    simpa [prefixWord, tailWord_8334529, baseEnd_8334529] using wordTrace_append hprefix tailTrace_8334529
  have hstable : (prefixWord ++ tailWord_8334529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334529).length < 2 ^ (prefixWord ++ tailWord_8334529).sum := by decide
  have hdescent : baseEnd_8334529 < baseStart_8334529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334530 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_8334530 : Nat := 118140960795 + 8334530 * 2 ^ 59
def prefixEnd_8334530 : Nat := 4983230072969 + 3 ^ 40 * 8334530 * 2
def baseEnd_8334530 : Nat := 4279619919317381346745201

theorem tailTrace_8334530 : CollatzResearch.WordTrace tailWord_8334530 prefixEnd_8334530 4279619919317381346745201 := by
  unfold tailWord_8334530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75996320623857177311126261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202656854996952472829670029 75996320623857177311126261)
  ·
    refine ⟨7124655058486610372918087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75996320623857177311126261 7124655058486610372918087)
    ·
      refine ⟨10686982587729915559377131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124655058486610372918087 10686982587729915559377131)
      ·
        refine ⟨16030473881594873339065697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686982587729915559377131 16030473881594873339065697)
        ·
          refine ⟨12022855411196155004299273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030473881594873339065697 12022855411196155004299273)
          ·
            refine ⟨9017141558397116253224455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022855411196155004299273 9017141558397116253224455)
            ·
              refine ⟨13525712337595674379836683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017141558397116253224455 13525712337595674379836683)
              ·
                refine ⟨20288568506393511569755025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13525712337595674379836683 20288568506393511569755025)
                ·
                  refine ⟨15216426379795133677316269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20288568506393511569755025 15216426379795133677316269)
                  ·
                    refine ⟨5706159892423175128993601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15216426379795133677316269 5706159892423175128993601)
                    ·
                      refine ⟨4279619919317381346745201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706159892423175128993601 4279619919317381346745201)
                      ·
                        rfl

theorem cell23_8334530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_8334530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334530 prefixEnd_8334530 := by exact prefixLift 8334530
  have htrace : WordTrace (prefixWord ++ tailWord_8334530) baseStart_8334530 baseEnd_8334530 := by
    simpa [prefixWord, tailWord_8334530, baseEnd_8334530] using wordTrace_append hprefix tailTrace_8334530
  have hstable : (prefixWord ++ tailWord_8334530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334530).length < 2 ^ (prefixWord ++ tailWord_8334530).sum := by decide
  have hdescent : baseEnd_8334530 < baseStart_8334530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334559 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_8334559 : Nat := 118140960795 + 8334559 * 2 ^ 59
def prefixEnd_8334559 : Nat := 4983230072969 + 3 ^ 40 * 8334559 * 2
def baseEnd_8334559 : Nat := 4279634810256361733282567

theorem tailTrace_8334559 : CollatzResearch.WordTrace tailWord_8334559 prefixEnd_8334559 4279634810256361733282567 := by
  unfold tailWord_8334559
  simp only [CollatzResearch.WordTrace]
  refine ⟨303986340212323647197310731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202657560141549098131540487 303986340212323647197310731)
  ·
    refine ⟨455979510318485470795966097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303986340212323647197310731 455979510318485470795966097)
    ·
      refine ⟨341984632738864103096974573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455979510318485470795966097 341984632738864103096974573)
      ·
        refine ⟨128244237277074038661365465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341984632738864103096974573 128244237277074038661365465)
        ·
          refine ⟨96183177957805528996024099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128244237277074038661365465 96183177957805528996024099)
          ·
            refine ⟨144274766936708293494036149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96183177957805528996024099 144274766936708293494036149)
            ·
              refine ⟨13525759400316402515065889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144274766936708293494036149 13525759400316402515065889)
              ·
                refine ⟨10144319550237301886299417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13525759400316402515065889 10144319550237301886299417)
                ·
                  refine ⟨7608239662677976414724563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10144319550237301886299417 7608239662677976414724563)
                  ·
                    refine ⟨11412359494016964622086845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7608239662677976414724563 11412359494016964622086845)
                    ·
                      refine ⟨4279634810256361733282567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412359494016964622086845 4279634810256361733282567)
                      ·
                        rfl

theorem cell23_8334559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_8334559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334559 prefixEnd_8334559 := by exact prefixLift 8334559
  have htrace : WordTrace (prefixWord ++ tailWord_8334559) baseStart_8334559 baseEnd_8334559 := by
    simpa [prefixWord, tailWord_8334559, baseEnd_8334559] using wordTrace_append hprefix tailTrace_8334559
  have hstable : (prefixWord ++ tailWord_8334559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334559).length < 2 ^ (prefixWord ++ tailWord_8334559).sum := by decide
  have hdescent : baseEnd_8334559 < baseStart_8334559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334580 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8334580 : Nat := 118140960795 + 8334580 * 2 ^ 59
def prefixEnd_8334580 : Nat := 4983230072969 + 3 ^ 40 * 8334580 * 2
def baseEnd_8334580 : Nat := 4279645593350106151119971

theorem tailTrace_8334580 : CollatzResearch.WordTrace tailWord_8334580 prefixEnd_8334580 4279645593350106151119971 := by
  unfold tailWord_8334580
  simp only [CollatzResearch.WordTrace]
  refine ⟨151993553072623783891912597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202658070763498378522550129 151993553072623783891912597)
  ·
    refine ⟨7124697800279239869933403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151993553072623783891912597 7124697800279239869933403)
    ·
      refine ⟨10687046700418859804900105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124697800279239869933403 10687046700418859804900105)
      ·
        refine ⟨8015285025314144853675079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10687046700418859804900105 8015285025314144853675079)
        ·
          refine ⟨12022927537971217280512619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015285025314144853675079 12022927537971217280512619)
          ·
            refine ⟨18034391306956825920768929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022927537971217280512619 18034391306956825920768929)
            ·
              refine ⟨13525793480217619440576697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18034391306956825920768929 13525793480217619440576697)
              ·
                refine ⟨10144345110163214580432523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13525793480217619440576697 10144345110163214580432523)
                ·
                  refine ⟨15216517665244821870648785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10144345110163214580432523 15216517665244821870648785)
                  ·
                    refine ⟨11412388248933616402986589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15216517665244821870648785 11412388248933616402986589)
                    ·
                      refine ⟨4279645593350106151119971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412388248933616402986589 4279645593350106151119971)
                      ·
                        rfl

theorem cell23_8334580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8334580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334580 prefixEnd_8334580 := by exact prefixLift 8334580
  have htrace : WordTrace (prefixWord ++ tailWord_8334580) baseStart_8334580 baseEnd_8334580 := by
    simpa [prefixWord, tailWord_8334580, baseEnd_8334580] using wordTrace_append hprefix tailTrace_8334580
  have hstable : (prefixWord ++ tailWord_8334580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334580).length < 2 ^ (prefixWord ++ tailWord_8334580).sum := by decide
  have hdescent : baseEnd_8334580 < baseStart_8334580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334585 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_8334585 : Nat := 118140960795 + 8334585 * 2 ^ 59
def prefixEnd_8334585 : Nat := 4983230072969 + 3 ^ 40 * 8334585 * 2
def baseEnd_8334585 : Nat := 4279648160753378631557447

theorem tailTrace_8334585 : CollatzResearch.WordTrace tailWord_8334585 prefixEnd_8334585 4279648160753378631557447 := by
  unfold tailWord_8334585
  simp only [CollatzResearch.WordTrace]
  refine ⟨303987288510229453637757209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202658192340152969091838139 303987288510229453637757209)
  ·
    refine ⟨227990466382672090228317907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303987288510229453637757209 227990466382672090228317907)
    ·
      refine ⟨341985699574008135342476861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227990466382672090228317907 341985699574008135342476861)
      ·
        refine ⟨128244637340253050753428823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341985699574008135342476861 128244637340253050753428823)
        ·
          refine ⟨192366956010379576130143235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128244637340253050753428823 192366956010379576130143235)
          ·
            refine ⟨288550434015569364195214853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192366956010379576130143235 288550434015569364195214853)
            ·
              refine ⟨54103206377919255786602785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288550434015569364195214853 54103206377919255786602785)
              ·
                refine ⟨40577404783439441839952089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54103206377919255786602785 40577404783439441839952089)
                ·
                  refine ⟨30433053587579581379964067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40577404783439441839952089 30433053587579581379964067)
                  ·
                    refine ⟨45649580381369372069946101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30433053587579581379964067 45649580381369372069946101)
                    ·
                      refine ⟨4279648160753378631557447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45649580381369372069946101 4279648160753378631557447)
                      ·
                        rfl

theorem cell23_8334585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_8334585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334585 prefixEnd_8334585 := by exact prefixLift 8334585
  have htrace : WordTrace (prefixWord ++ tailWord_8334585) baseStart_8334585 baseEnd_8334585 := by
    simpa [prefixWord, tailWord_8334585, baseEnd_8334585] using wordTrace_append hprefix tailTrace_8334585
  have hstable : (prefixWord ++ tailWord_8334585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334585).length < 2 ^ (prefixWord ++ tailWord_8334585).sum := by decide
  have hdescent : baseEnd_8334585 < baseStart_8334585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334615 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_8334615 : Nat := 118140960795 + 8334615 * 2 ^ 59
def prefixEnd_8334615 : Nat := 4983230072969 + 3 ^ 40 * 8334615 * 2
def baseEnd_8334615 : Nat := 4279663565173013514182309

theorem tailTrace_8334615 : CollatzResearch.WordTrace tailWord_8334615 prefixEnd_8334615 4279663565173013514182309 := by
  unfold tailWord_8334615
  simp only [CollatzResearch.WordTrace]
  refine ⟨303988382700120768761349299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202658921800080512507566199 303988382700120768761349299)
  ·
    refine ⟨455982574050181153142023949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303988382700120768761349299 455982574050181153142023949)
    ·
      refine ⟨170993465268817932428258981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455982574050181153142023949 170993465268817932428258981)
      ·
        refine ⟨32061274737903362330298559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170993465268817932428258981 32061274737903362330298559)
        ·
          refine ⟨48091912106855043495447839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32061274737903362330298559 48091912106855043495447839)
          ·
            refine ⟨72137868160282565243171759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48091912106855043495447839 72137868160282565243171759)
            ·
              refine ⟨108206802240423847864757639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72137868160282565243171759 108206802240423847864757639)
              ·
                refine ⟨162310203360635771797136459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108206802240423847864757639 162310203360635771797136459)
                ·
                  refine ⟨243465305040953657695704689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162310203360635771797136459 243465305040953657695704689)
                  ·
                    refine ⟨182598978780715243271778517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243465305040953657695704689 182598978780715243271778517)
                    ·
                      refine ⟨4279663565173013514182309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182598978780715243271778517 4279663565173013514182309)
                      ·
                        rfl

theorem cell23_8334615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_8334615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334615 prefixEnd_8334615 := by exact prefixLift 8334615
  have htrace : WordTrace (prefixWord ++ tailWord_8334615) baseStart_8334615 baseEnd_8334615 := by
    simpa [prefixWord, tailWord_8334615, baseEnd_8334615] using wordTrace_append hprefix tailTrace_8334615
  have hstable : (prefixWord ++ tailWord_8334615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334615).length < 2 ^ (prefixWord ++ tailWord_8334615).sum := by decide
  have hdescent : baseEnd_8334615 < baseStart_8334615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334652 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_8334652 : Nat := 118140960795 + 8334652 * 2 ^ 59
def prefixEnd_8334652 : Nat := 4983230072969 + 3 ^ 40 * 8334652 * 2
def baseEnd_8334652 : Nat := 1426560854652409956473213

theorem tailTrace_8334652 : CollatzResearch.WordTrace tailWord_8334652 prefixEnd_8334652 1426560854652409956473213 := by
  unfold tailWord_8334652
  simp only [CollatzResearch.WordTrace]
  refine ⟨151994866100493362040223105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202659821467324482720297473 151994866100493362040223105)
  ·
    refine ⟨113996149575370021530167329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151994866100493362040223105 113996149575370021530167329)
    ·
      refine ⟨85497112181527516147625497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113996149575370021530167329 85497112181527516147625497)
      ·
        refine ⟨64122834136145637110719123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85497112181527516147625497 64122834136145637110719123)
        ·
          refine ⟨96184251204218455666078685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64122834136145637110719123 96184251204218455666078685)
          ·
            refine ⟨36069094201581920874779507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96184251204218455666078685 36069094201581920874779507)
            ·
              refine ⟨54103641302372881312169261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36069094201581920874779507 54103641302372881312169261)
              ·
                refine ⟨20288865488389830492063473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54103641302372881312169261 20288865488389830492063473)
                ·
                  refine ⟨15216649116292372869047605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20288865488389830492063473 15216649116292372869047605)
                  ·
                    refine ⟨1426560854652409956473213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15216649116292372869047605 1426560854652409956473213)
                    ·
                      rfl

theorem cell23_8334652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_8334652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334652 prefixEnd_8334652 := by exact prefixLift 8334652
  have htrace : WordTrace (prefixWord ++ tailWord_8334652) baseStart_8334652 baseEnd_8334652 := by
    simpa [prefixWord, tailWord_8334652, baseEnd_8334652] using wordTrace_append hprefix tailTrace_8334652
  have hstable : (prefixWord ++ tailWord_8334652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334652).length < 2 ^ (prefixWord ++ tailWord_8334652).sum := by decide
  have hdescent : baseEnd_8334652 < baseStart_8334652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334672 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_8334672 : Nat := 118140960795 + 8334672 * 2 ^ 59
def prefixEnd_8334672 : Nat := 4983230072969 + 3 ^ 40 * 8334672 * 2
def baseEnd_8334672 : Nat := 4279692833570319791169547

theorem tailTrace_8334672 : CollatzResearch.WordTrace tailWord_8334672 prefixEnd_8334672 4279692833570319791169547 := by
  unfold tailWord_8334672
  simp only [CollatzResearch.WordTrace]
  refine ⟨151995230830457133748087135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202660307773942844997449513 151995230830457133748087135)
  ·
    refine ⟨227992846245685700622130703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151995230830457133748087135 227992846245685700622130703)
    ·
      refine ⟨341989269368528550933196055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227992846245685700622130703 341989269368528550933196055)
      ·
        refine ⟨512983904052792826399794083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341989269368528550933196055 512983904052792826399794083)
        ·
          refine ⟨769475856079189239599691125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512983904052792826399794083 769475856079189239599691125)
          ·
            refine ⟨72138361507423991212471043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 769475856079189239599691125 72138361507423991212471043)
            ·
              refine ⟨108207542261135986818706565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72138361507423991212471043 108207542261135986818706565)
              ·
                refine ⟨20288914173962997528507481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108207542261135986818706565 20288914173962997528507481)
                ·
                  refine ⟨15216685630472248146380611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20288914173962997528507481 15216685630472248146380611)
                  ·
                    refine ⟨22825028445708372219570917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15216685630472248146380611 22825028445708372219570917)
                    ·
                      refine ⟨4279692833570319791169547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22825028445708372219570917 4279692833570319791169547)
                      ·
                        rfl

theorem cell23_8334672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_8334672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334672 prefixEnd_8334672 := by exact prefixLift 8334672
  have htrace : WordTrace (prefixWord ++ tailWord_8334672) baseStart_8334672 baseEnd_8334672 := by
    simpa [prefixWord, tailWord_8334672, baseEnd_8334672] using wordTrace_append hprefix tailTrace_8334672
  have hstable : (prefixWord ++ tailWord_8334672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334672).length < 2 ^ (prefixWord ++ tailWord_8334672).sum := by decide
  have hdescent : baseEnd_8334672 < baseStart_8334672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334675 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_8334675 : Nat := 118140960795 + 8334675 * 2 ^ 59
def prefixEnd_8334675 : Nat := 4983230072969 + 3 ^ 40 * 8334675 * 2
def baseEnd_8334675 : Nat := 4279694374012283279432033

theorem tailTrace_8334675 : CollatzResearch.WordTrace tailWord_8334675 prefixEnd_8334675 4279694374012283279432033 := by
  unfold tailWord_8334675
  simp only [CollatzResearch.WordTrace]
  refine ⟨303990571079903399008533479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202660380719935599339022319 303990571079903399008533479)
  ·
    refine ⟨455985856619855098512800219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303990571079903399008533479 455985856619855098512800219)
    ·
      refine ⟨683978784929782647769200329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455985856619855098512800219 683978784929782647769200329)
      ·
        refine ⟨512984088697336985826900247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683978784929782647769200329 512984088697336985826900247)
        ·
          refine ⟨769476133046005478740350371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512984088697336985826900247 769476133046005478740350371)
          ·
            refine ⟨1154214199569008218110525557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769476133046005478740350371 1154214199569008218110525557)
            ·
              refine ⟨108207581209594520447861771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1154214199569008218110525557 108207581209594520447861771)
              ·
                refine ⟨162311371814391780671792657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108207581209594520447861771 162311371814391780671792657)
                ·
                  refine ⟨121733528860793835503844493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162311371814391780671792657 121733528860793835503844493)
                  ·
                    refine ⟨45650073322797688313941685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121733528860793835503844493 45650073322797688313941685)
                    ·
                      refine ⟨4279694374012283279432033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45650073322797688313941685 4279694374012283279432033)
                      ·
                        rfl

theorem cell23_8334675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_8334675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334675 prefixEnd_8334675 := by exact prefixLift 8334675
  have htrace : WordTrace (prefixWord ++ tailWord_8334675) baseStart_8334675 baseEnd_8334675 := by
    simpa [prefixWord, tailWord_8334675, baseEnd_8334675] using wordTrace_append hprefix tailTrace_8334675
  have hstable : (prefixWord ++ tailWord_8334675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334675).length < 2 ^ (prefixWord ++ tailWord_8334675).sum := by decide
  have hdescent : baseEnd_8334675 < baseStart_8334675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334716 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_8334716 : Nat := 118140960795 + 8334716 * 2 ^ 59
def prefixEnd_8334716 : Nat := 4983230072969 + 3 ^ 40 * 8334716 * 2
def baseEnd_8334716 : Nat := 1426571808906372539673115

theorem tailTrace_8334716 : CollatzResearch.WordTrace tailWord_8334716 prefixEnd_8334716 1426571808906372539673115 := by
  unfold tailWord_8334716
  simp only [CollatzResearch.WordTrace]
  refine ⟨151996033236377431505388001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202661377648503242007184001 151996033236377431505388001)
  ·
    refine ⟨113997024927283073629041001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151996033236377431505388001 113997024927283073629041001)
    ·
      refine ⟨85497768695462305221780751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113997024927283073629041001 85497768695462305221780751)
      ·
        refine ⟨128246653043193457832671127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85497768695462305221780751 128246653043193457832671127)
        ·
          refine ⟨192369979564790186749006691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128246653043193457832671127 192369979564790186749006691)
          ·
            refine ⟨288554969347185280123510037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192369979564790186749006691 288554969347185280123510037)
            ·
              refine ⟨13526014188149310005789533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288554969347185280123510037 13526014188149310005789533)
              ·
                refine ⟨5072255320555991252171075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13526014188149310005789533 5072255320555991252171075)
                ·
                  refine ⟨7608382980833986878256613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072255320555991252171075 7608382980833986878256613)
                  ·
                    refine ⟨1426571808906372539673115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608382980833986878256613 1426571808906372539673115)
                    ·
                      rfl

theorem cell23_8334716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_8334716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334716 prefixEnd_8334716 := by exact prefixLift 8334716
  have htrace : WordTrace (prefixWord ++ tailWord_8334716) baseStart_8334716 baseEnd_8334716 := by
    simpa [prefixWord, tailWord_8334716, baseEnd_8334716] using wordTrace_append hprefix tailTrace_8334716
  have hstable : (prefixWord ++ tailWord_8334716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334716).length < 2 ^ (prefixWord ++ tailWord_8334716).sum := by decide
  have hdescent : baseEnd_8334716 < baseStart_8334716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334792 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_8334792 : Nat := 118140960795 + 8334792 * 2 ^ 59
def prefixEnd_8334792 : Nat := 4983230072969 + 3 ^ 40 * 8334792 * 2
def baseEnd_8334792 : Nat := 4279754451248859321668995

theorem tailTrace_8334792 : CollatzResearch.WordTrace tailWord_8334792 prefixEnd_8334792 4279754451248859321668995 := by
  unfold tailWord_8334792
  simp only [CollatzResearch.WordTrace]
  refine ⟨151997419210239763995271315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202663225613653018660361753 151997419210239763995271315)
  ·
    refine ⟨227996128815359645992906973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151997419210239763995271315 227996128815359645992906973)
    ·
      refine ⟨85498548305759867247340115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227996128815359645992906973 85498548305759867247340115)
      ·
        refine ⟨128247822458639800871010173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85498548305759867247340115 128247822458639800871010173)
        ·
          refine ⟨48092933421989925326628815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128247822458639800871010173 48092933421989925326628815)
          ·
            refine ⟨72139400132984887989943223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48092933421989925326628815 72139400132984887989943223)
            ·
              refine ⟨108209100199477331984914835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72139400132984887989943223 108209100199477331984914835)
              ·
                refine ⟨162313650299215997977372253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108209100199477331984914835 162313650299215997977372253)
                ·
                  refine ⟨60867618862205999241514595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162313650299215997977372253 60867618862205999241514595)
                  ·
                    refine ⟨91301428293308998862271893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60867618862205999241514595 91301428293308998862271893)
                    ·
                      refine ⟨4279754451248859321668995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91301428293308998862271893 4279754451248859321668995)
                      ·
                        rfl

theorem cell23_8334792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_8334792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334792 prefixEnd_8334792 := by exact prefixLift 8334792
  have htrace : WordTrace (prefixWord ++ tailWord_8334792) baseStart_8334792 baseEnd_8334792 := by
    simpa [prefixWord, tailWord_8334792, baseEnd_8334792] using wordTrace_append hprefix tailTrace_8334792
  have hstable : (prefixWord ++ tailWord_8334792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334792).length < 2 ^ (prefixWord ++ tailWord_8334792).sum := by decide
  have hdescent : baseEnd_8334792 < baseStart_8334792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334813 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_8334813 : Nat := 118140960795 + 8334813 * 2 ^ 59
def prefixEnd_8334813 : Nat := 4983230072969 + 3 ^ 40 * 8334813 * 2
def baseEnd_8334813 : Nat := 4279765234342603739506399

theorem tailTrace_8334813 : CollatzResearch.WordTrace tailWord_8334813 prefixEnd_8334813 4279765234342603739506399 := by
  unfold tailWord_8334813
  simp only [CollatzResearch.WordTrace]
  refine ⟨303995604353403448577057093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202663736235602299051371395 303995604353403448577057093)
  ·
    refine ⟨56999175816263146608198205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303995604353403448577057093 56999175816263146608198205)
    ·
      refine ⟨21374690931098679978074327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56999175816263146608198205 21374690931098679978074327)
      ·
        refine ⟨32062036396648019967111491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374690931098679978074327 32062036396648019967111491)
        ·
          refine ⟨48093054594972029950667237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32062036396648019967111491 48093054594972029950667237)
          ·
            refine ⟨9017447736557255615750107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48093054594972029950667237 9017447736557255615750107)
            ·
              refine ⟨13526171604835883423625161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017447736557255615750107 13526171604835883423625161)
              ·
                refine ⟨10144628703626912567718871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13526171604835883423625161 10144628703626912567718871)
                ·
                  refine ⟨15216943055440368851578307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10144628703626912567718871 15216943055440368851578307)
                  ·
                    refine ⟨22825414583160553277367461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15216943055440368851578307 22825414583160553277367461)
                    ·
                      refine ⟨4279765234342603739506399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22825414583160553277367461 4279765234342603739506399)
                      ·
                        rfl

theorem cell23_8334813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_8334813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334813 prefixEnd_8334813 := by exact prefixLift 8334813
  have htrace : WordTrace (prefixWord ++ tailWord_8334813) baseStart_8334813 baseEnd_8334813 := by
    simpa [prefixWord, tailWord_8334813, baseEnd_8334813] using wordTrace_append hprefix tailTrace_8334813
  have hstable : (prefixWord ++ tailWord_8334813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334813).length < 2 ^ (prefixWord ++ tailWord_8334813).sum := by decide
  have hdescent : baseEnd_8334813 < baseStart_8334813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334826 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_8334826 : Nat := 118140960795 + 8334826 * 2 ^ 59
def prefixEnd_8334826 : Nat := 4983230072969 + 3 ^ 40 * 8334826 * 2
def baseEnd_8334826 : Nat := 4279771909591112188643839

theorem tailTrace_8334826 : CollatzResearch.WordTrace tailWord_8334826 prefixEnd_8334826 4279771909591112188643839 := by
  unfold tailWord_8334826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75999019625589087949320083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202664052334904234531520221 75999019625589087949320083)
  ·
    refine ⟨113998529438383631923980125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75999019625589087949320083 113998529438383631923980125)
    ·
      refine ⟨42749448539393861971492547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113998529438383631923980125 42749448539393861971492547)
      ·
        refine ⟨64124172809090792957238821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42749448539393861971492547 64124172809090792957238821)
        ·
          refine ⟨12023282401704523679482279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64124172809090792957238821 12023282401704523679482279)
          ·
            refine ⟨18034923602556785519223419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023282401704523679482279 18034923602556785519223419)
            ·
              refine ⟨27052385403835178278835129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034923602556785519223419 27052385403835178278835129)
              ·
                refine ⟨20289289052876383709126347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27052385403835178278835129 20289289052876383709126347)
                ·
                  refine ⟨30433933579314575563689521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20289289052876383709126347 30433933579314575563689521)
                  ·
                    refine ⟨22825450184485931672767141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30433933579314575563689521 22825450184485931672767141)
                    ·
                      refine ⟨4279771909591112188643839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22825450184485931672767141 4279771909591112188643839)
                      ·
                        rfl

theorem cell23_8334826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_8334826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334826 prefixEnd_8334826 := by exact prefixLift 8334826
  have htrace : WordTrace (prefixWord ++ tailWord_8334826) baseStart_8334826 baseEnd_8334826 := by
    simpa [prefixWord, tailWord_8334826, baseEnd_8334826] using wordTrace_append hprefix tailTrace_8334826
  have hstable : (prefixWord ++ tailWord_8334826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334826).length < 2 ^ (prefixWord ++ tailWord_8334826).sum := by decide
  have hdescent : baseEnd_8334826 < baseStart_8334826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334830 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_8334830 : Nat := 118140960795 + 8334830 * 2 ^ 59
def prefixEnd_8334830 : Nat := 4983230072969 + 3 ^ 40 * 8334830 * 2
def baseEnd_8334830 : Nat := 4279773963513730172993821

theorem tailTrace_8334830 : CollatzResearch.WordTrace tailWord_8334830 prefixEnd_8334830 4279773963513730172993821 := by
  unfold tailWord_8334830
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999528049292732560053243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202664149596227906986950629 37999528049292732560053243)
  ·
    refine ⟨56999292073939098840079865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37999528049292732560053243 56999292073939098840079865)
    ·
      refine ⟨42749469055454324130059899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56999292073939098840079865 42749469055454324130059899)
      ·
        refine ⟨64124203583181486195089849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42749469055454324130059899 64124203583181486195089849)
        ·
          refine ⟨48093152687386114646317387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64124203583181486195089849 48093152687386114646317387)
          ·
            refine ⟨72139729031079171969476081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48093152687386114646317387 72139729031079171969476081)
            ·
              refine ⟨54104796773309378977107061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72139729031079171969476081 54104796773309378977107061)
              ·
                refine ⟨5072324697497754279103787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54104796773309378977107061 5072324697497754279103787)
                ·
                  refine ⟨7608487046246631418655681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072324697497754279103787 7608487046246631418655681)
                  ·
                    refine ⟨5706365284684973563991761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608487046246631418655681 5706365284684973563991761)
                    ·
                      refine ⟨4279773963513730172993821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706365284684973563991761 4279773963513730172993821)
                      ·
                        rfl

theorem cell23_8334830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_8334830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334830 prefixEnd_8334830 := by exact prefixLift 8334830
  have htrace : WordTrace (prefixWord ++ tailWord_8334830) baseStart_8334830 baseEnd_8334830 := by
    simpa [prefixWord, tailWord_8334830, baseEnd_8334830] using wordTrace_append hprefix tailTrace_8334830
  have hstable : (prefixWord ++ tailWord_8334830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334830).length < 2 ^ (prefixWord ++ tailWord_8334830).sum := by decide
  have hdescent : baseEnd_8334830 < baseStart_8334830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334833 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_8334833 : Nat := 118140960795 + 8334833 * 2 ^ 59
def prefixEnd_8334833 : Nat := 4983230072969 + 3 ^ 40 * 8334833 * 2
def baseEnd_8334833 : Nat := 4279775503955693661256307

theorem tailTrace_8334833 : CollatzResearch.WordTrace tailWord_8334833 prefixEnd_8334833 4279775503955693661256307 := by
  unfold tailWord_8334833
  simp only [CollatzResearch.WordTrace]
  refine ⟨303996333813330991992785153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202664222542220661328523435 303996333813330991992785153)
  ·
    refine ⟨227997250359998243994588865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303996333813330991992785153 227997250359998243994588865)
    ·
      refine ⟨170997937769998682995941649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227997250359998243994588865 170997937769998682995941649)
      ·
        refine ⟨128248453327499012246956237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170997937769998682995941649 128248453327499012246956237)
        ·
          refine ⟨48093169997812129592608589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128248453327499012246956237 48093169997812129592608589)
          ·
            refine ⟨18034938749179548597228221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48093169997812129592608589 18034938749179548597228221)
            ·
              refine ⟨6763102030942330723960583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18034938749179548597228221 6763102030942330723960583)
              ·
                refine ⟨10144653046413496085940875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763102030942330723960583 10144653046413496085940875)
                ·
                  refine ⟨15216979569620244128911313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10144653046413496085940875 15216979569620244128911313)
                  ·
                    refine ⟨11412734677215183096683485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15216979569620244128911313 11412734677215183096683485)
                    ·
                      refine ⟨4279775503955693661256307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11412734677215183096683485 4279775503955693661256307)
                      ·
                        rfl

theorem cell23_8334833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_8334833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334833 prefixEnd_8334833 := by exact prefixLift 8334833
  have htrace : WordTrace (prefixWord ++ tailWord_8334833) baseStart_8334833 baseEnd_8334833 := by
    simpa [prefixWord, tailWord_8334833, baseEnd_8334833] using wordTrace_append hprefix tailTrace_8334833
  have hstable : (prefixWord ++ tailWord_8334833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334833).length < 2 ^ (prefixWord ++ tailWord_8334833).sum := by decide
  have hdescent : baseEnd_8334833 < baseStart_8334833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334856 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_8334856 : Nat := 118140960795 + 8334856 * 2 ^ 59
def prefixEnd_8334856 : Nat := 4983230072969 + 3 ^ 40 * 8334856 * 2
def baseEnd_8334856 : Nat := 4279787314010747071268701

theorem tailTrace_8334856 : CollatzResearch.WordTrace tailWord_8334856 prefixEnd_8334856 4279787314010747071268701 := by
  unfold tailWord_8334856
  simp only [CollatzResearch.WordTrace]
  refine ⟨151998586346123833460436211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202664781794831777947248281 151998586346123833460436211)
  ·
    refine ⟨227997879519185750190654317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151998586346123833460436211 227997879519185750190654317)
    ·
      refine ⟨85499204819694656321495369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227997879519185750190654317 85499204819694656321495369)
      ·
        refine ⟨64124403614770992241121527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85499204819694656321495369 64124403614770992241121527)
        ·
          refine ⟨96186605422156488361682291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64124403614770992241121527 96186605422156488361682291)
          ·
            refine ⟨144279908133234732542523437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96186605422156488361682291 144279908133234732542523437)
            ·
              refine ⟨54104965549963024703446289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144279908133234732542523437 54104965549963024703446289)
              ·
                refine ⟨40578724162472268527584717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54104965549963024703446289 40578724162472268527584717)
                ·
                  refine ⟨15217021560927100697844269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40578724162472268527584717 15217021560927100697844269)
                  ·
                    refine ⟨5706383085347662761691601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15217021560927100697844269 5706383085347662761691601)
                    ·
                      refine ⟨4279787314010747071268701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706383085347662761691601 4279787314010747071268701)
                      ·
                        rfl

theorem cell23_8334856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_8334856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334856 prefixEnd_8334856 := by exact prefixLift 8334856
  have htrace : WordTrace (prefixWord ++ tailWord_8334856) baseStart_8334856 baseEnd_8334856 := by
    simpa [prefixWord, tailWord_8334856, baseEnd_8334856] using wordTrace_append hprefix tailTrace_8334856
  have hstable : (prefixWord ++ tailWord_8334856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334856).length < 2 ^ (prefixWord ++ tailWord_8334856).sum := by decide
  have hdescent : baseEnd_8334856 < baseStart_8334856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334899 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_8334899 : Nat := 118140960795 + 8334899 * 2 ^ 59
def prefixEnd_8334899 : Nat := 4983230072969 + 3 ^ 40 * 8334899 * 2
def baseEnd_8334899 : Nat := 4279809393678890403031003

theorem tailTrace_8334899 : CollatzResearch.WordTrace tailWord_8334899 prefixEnd_8334899 4279809393678890403031003 := by
  unfold tailWord_8334899
  simp only [CollatzResearch.WordTrace]
  refine ⟨303998741031091885264687751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202665827354061256843125167 303998741031091885264687751)
  ·
    refine ⟨455998111546637827897031627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303998741031091885264687751 455998111546637827897031627)
    ·
      refine ⟨683997167319956741845547441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455998111546637827897031627 683997167319956741845547441)
      ·
        refine ⟨512997875489967556384160581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683997167319956741845547441 512997875489967556384160581)
        ·
          refine ⟨96187101654368916822030109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512997875489967556384160581 96187101654368916822030109)
          ·
            refine ⟨36070163120388343808261291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96187101654368916822030109 36070163120388343808261291)
            ·
              refine ⟨54105244680582515712391937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36070163120388343808261291 54105244680582515712391937)
              ·
                refine ⟨40578933510436886784293953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54105244680582515712391937 40578933510436886784293953)
                ·
                  refine ⟨30434200132827665088220465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40578933510436886784293953 30434200132827665088220465)
                  ·
                    refine ⟨22825650099620748816165349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30434200132827665088220465 22825650099620748816165349)
                    ·
                      refine ⟨4279809393678890403031003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22825650099620748816165349 4279809393678890403031003)
                      ·
                        rfl

theorem cell23_8334899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_8334899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334899 prefixEnd_8334899 := by exact prefixLift 8334899
  have htrace : WordTrace (prefixWord ++ tailWord_8334899) baseStart_8334899 baseEnd_8334899 := by
    simpa [prefixWord, tailWord_8334899, baseEnd_8334899] using wordTrace_append hprefix tailTrace_8334899
  have hstable : (prefixWord ++ tailWord_8334899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334899).length < 2 ^ (prefixWord ++ tailWord_8334899).sum := by decide
  have hdescent : baseEnd_8334899 < baseStart_8334899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334903 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_8334903 : Nat := 118140960795 + 8334903 * 2 ^ 59
def prefixEnd_8334903 : Nat := 4983230072969 + 3 ^ 40 * 8334903 * 2
def baseEnd_8334903 : Nat := 4279811447601508387380985

theorem tailTrace_8334903 : CollatzResearch.WordTrace tailWord_8334903 prefixEnd_8334903 4279811447601508387380985 := by
  unfold tailWord_8334903
  simp only [CollatzResearch.WordTrace]
  refine ⟨303998886923077393947833363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202665924615384929298555575 303998886923077393947833363)
  ·
    refine ⟨455998330384616090921750045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303998886923077393947833363 455998330384616090921750045)
    ·
      refine ⟨170999373894231034095656267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455998330384616090921750045 170999373894231034095656267)
      ·
        refine ⟨256499060841346551143484401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170999373894231034095656267 256499060841346551143484401)
        ·
          refine ⟨192374295631009913357613301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256499060841346551143484401 192374295631009913357613301)
          ·
            refine ⟨18035090215407179377276247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192374295631009913357613301 18035090215407179377276247)
            ·
              refine ⟨27052635323110769065914371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18035090215407179377276247 27052635323110769065914371)
              ·
                refine ⟨40578952984666153598871557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27052635323110769065914371 40578952984666153598871557)
                ·
                  refine ⟨7608553684624903799788417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40578952984666153598871557 7608553684624903799788417)
                  ·
                    refine ⟨5706415263468677849841313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608553684624903799788417 5706415263468677849841313)
                    ·
                      refine ⟨4279811447601508387380985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706415263468677849841313 4279811447601508387380985)
                      ·
                        rfl

theorem cell23_8334903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_8334903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334903 prefixEnd_8334903 := by exact prefixLift 8334903
  have htrace : WordTrace (prefixWord ++ tailWord_8334903) baseStart_8334903 baseEnd_8334903 := by
    simpa [prefixWord, tailWord_8334903, baseEnd_8334903] using wordTrace_append hprefix tailTrace_8334903
  have hstable : (prefixWord ++ tailWord_8334903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334903).length < 2 ^ (prefixWord ++ tailWord_8334903).sum := by decide
  have hdescent : baseEnd_8334903 < baseStart_8334903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334966 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8334966 : Nat := 118140960795 + 8334966 * 2 ^ 59
def prefixEnd_8334966 : Nat := 4983230072969 + 3 ^ 40 * 8334966 * 2
def baseEnd_8334966 : Nat := 4279843796882741640893195

theorem tailTrace_8334966 : CollatzResearch.WordTrace tailWord_8334966 prefixEnd_8334966 4279843796882741640893195 := by
  unfold tailWord_8334966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000074045115572231711047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202667456481232770471584501 19000074045115572231711047)
  ·
    refine ⟨28500111067673358347566571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19000074045115572231711047 28500111067673358347566571)
    ·
      refine ⟨42750166601510037521349857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28500111067673358347566571 42750166601510037521349857)
      ·
        refine ⟨32062624951132528141012393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42750166601510037521349857 32062624951132528141012393)
        ·
          refine ⟨24046968713349396105759295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32062624951132528141012393 24046968713349396105759295)
          ·
            refine ⟨36070453070024094158638943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24046968713349396105759295 36070453070024094158638943)
            ·
              refine ⟨54105679605036141237958415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36070453070024094158638943 54105679605036141237958415)
              ·
                refine ⟨81158519407554211856937623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54105679605036141237958415 81158519407554211856937623)
                ·
                  refine ⟨121737779111331317785406435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81158519407554211856937623 121737779111331317785406435)
                  ·
                    refine ⟨182606668666996976678109653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121737779111331317785406435 182606668666996976678109653)
                    ·
                      refine ⟨4279843796882741640893195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182606668666996976678109653 4279843796882741640893195)
                      ·
                        rfl

theorem cell23_8334966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8334966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334966 prefixEnd_8334966 := by exact prefixLift 8334966
  have htrace : WordTrace (prefixWord ++ tailWord_8334966) baseStart_8334966 baseEnd_8334966 := by
    simpa [prefixWord, tailWord_8334966, baseEnd_8334966] using wordTrace_append hprefix tailTrace_8334966
  have hstable : (prefixWord ++ tailWord_8334966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334966).length < 2 ^ (prefixWord ++ tailWord_8334966).sum := by decide
  have hdescent : baseEnd_8334966 < baseStart_8334966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8334976 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2]
def baseStart_8334976 : Nat := 118140960795 + 8334976 * 2 ^ 59
def prefixEnd_8334976 : Nat := 4983230072969 + 3 ^ 40 * 8334976 * 2
def baseEnd_8334976 : Nat := 4279848931689286601768149

theorem tailTrace_8334976 : CollatzResearch.WordTrace tailWord_8334976 prefixEnd_8334976 4279848931689286601768149 := by
  unfold tailWord_8334976
  simp only [CollatzResearch.WordTrace]
  refine ⟨152000774725906463707620391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202667699634541951610160521 152000774725906463707620391)
  ·
    refine ⟨228001162088859695561430587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152000774725906463707620391 228001162088859695561430587)
    ·
      refine ⟨342001743133289543342145881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228001162088859695561430587 342001743133289543342145881)
      ·
        refine ⟨256501307349967157506609411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342001743133289543342145881 256501307349967157506609411)
        ·
          refine ⟨384751961024950736259914117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256501307349967157506609411 384751961024950736259914117)
          ·
            refine ⟨72140992692178263048733897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384751961024950736259914117 72140992692178263048733897)
            ·
              refine ⟨54105744519133697286550423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72140992692178263048733897 54105744519133697286550423)
              ·
                refine ⟨81158616778700545929825635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54105744519133697286550423 81158616778700545929825635)
                ·
                  refine ⟨121737925168050818894738453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81158616778700545929825635 121737925168050818894738453)
                  ·
                    refine ⟨5706465242252382135690865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121737925168050818894738453 5706465242252382135690865)
                    ·
                      refine ⟨4279848931689286601768149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706465242252382135690865 4279848931689286601768149)
                      ·
                        rfl

theorem cell23_8334976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_8334976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8334976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8334976 prefixEnd_8334976 := by exact prefixLift 8334976
  have htrace : WordTrace (prefixWord ++ tailWord_8334976) baseStart_8334976 baseEnd_8334976 := by
    simpa [prefixWord, tailWord_8334976, baseEnd_8334976] using wordTrace_append hprefix tailTrace_8334976
  have hstable : (prefixWord ++ tailWord_8334976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8334976).length < 2 ^ (prefixWord ++ tailWord_8334976).sum := by decide
  have hdescent : baseEnd_8334976 < baseStart_8334976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8334976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335039 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_8335039 : Nat := 118140960795 + 8335039 * 2 ^ 59
def prefixEnd_8335039 : Nat := 4983230072969 + 3 ^ 40 * 8335039 * 2
def baseEnd_8335039 : Nat := 4279881280970519855280359

theorem tailTrace_8335039 : CollatzResearch.WordTrace tailWord_8335039 prefixEnd_8335039 4279881280970519855280359 := by
  unfold tailWord_8335039
  simp only [CollatzResearch.WordTrace]
  refine ⟨304003847250584689174784171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202669231500389792783189447 304003847250584689174784171)
  ·
    refine ⟨456005770875877033762176257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304003847250584689174784171 456005770875877033762176257)
    ·
      refine ⟨342004328156907775321632193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456005770875877033762176257 342004328156907775321632193)
      ·
        refine ⟨256503246117680831491224145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342004328156907775321632193 256503246117680831491224145)
        ·
          refine ⟨192377434588260623618418109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256503246117680831491224145 192377434588260623618418109)
          ·
            refine ⟨72141537970597733856906791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192377434588260623618418109 72141537970597733856906791)
            ·
              refine ⟨108212306955896600785360187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72141537970597733856906791 108212306955896600785360187)
              ·
                refine ⟨162318460433844901178040281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108212306955896600785360187 162318460433844901178040281)
                ·
                  refine ⟨121738845325383675883530211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162318460433844901178040281 121738845325383675883530211)
                  ·
                    refine ⟨182608267988075513825295317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121738845325383675883530211 182608267988075513825295317)
                    ·
                      refine ⟨4279881280970519855280359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182608267988075513825295317 4279881280970519855280359)
                      ·
                        rfl

theorem cell23_8335039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_8335039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335039 prefixEnd_8335039 := by exact prefixLift 8335039
  have htrace : WordTrace (prefixWord ++ tailWord_8335039) baseStart_8335039 baseEnd_8335039 := by
    simpa [prefixWord, tailWord_8335039, baseEnd_8335039] using wordTrace_append hprefix tailTrace_8335039
  have hstable : (prefixWord ++ tailWord_8335039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335039).length < 2 ^ (prefixWord ++ tailWord_8335039).sum := by decide
  have hdescent : baseEnd_8335039 < baseStart_8335039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335059 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 6]
def baseStart_8335059 : Nat := 118140960795 + 8335059 * 2 ^ 59
def prefixEnd_8335059 : Nat := 4983230072969 + 3 ^ 40 * 8335059 * 2
def baseEnd_8335059 : Nat := 1426630516861203259010089

theorem tailTrace_8335059 : CollatzResearch.WordTrace tailWord_8335059 prefixEnd_8335059 1426630516861203259010089 := by
  unfold tailWord_8335059
  simp only [CollatzResearch.WordTrace]
  refine ⟨304004576710512232590512231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202669717807008155060341487 304004576710512232590512231)
  ·
    refine ⟨456006865065768348885768347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304004576710512232590512231 456006865065768348885768347)
    ·
      refine ⟨684010297598652523328652521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456006865065768348885768347 684010297598652523328652521)
      ·
        refine ⟨513007723198989392496489391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684010297598652523328652521 513007723198989392496489391)
        ·
          refine ⟨769511584798484088744734087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513007723198989392496489391 769511584798484088744734087)
          ·
            refine ⟨1154267377197726133117101131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769511584798484088744734087 1154267377197726133117101131)
            ·
              refine ⟨1731401065796589199675651697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154267377197726133117101131 1731401065796589199675651697)
              ·
                refine ⟨1298550799347441899756738773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731401065796589199675651697 1298550799347441899756738773)
                ·
                  refine ⟨30434784359705669525548565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1298550799347441899756738773 30434784359705669525548565)
                  ·
                    refine ⟨1426630516861203259010089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30434784359705669525548565 1426630516861203259010089)
                    ·
                      rfl

theorem cell23_8335059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_8335059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335059 prefixEnd_8335059 := by exact prefixLift 8335059
  have htrace : WordTrace (prefixWord ++ tailWord_8335059) baseStart_8335059 baseEnd_8335059 := by
    simpa [prefixWord, tailWord_8335059, baseEnd_8335059] using wordTrace_append hprefix tailTrace_8335059
  have hstable : (prefixWord ++ tailWord_8335059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335059).length < 2 ^ (prefixWord ++ tailWord_8335059).sum := by decide
  have hdescent : baseEnd_8335059 < baseStart_8335059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335096 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_8335096 : Nat := 118140960795 + 8335096 * 2 ^ 59
def prefixEnd_8335096 : Nat := 4983230072969 + 3 ^ 40 * 8335096 * 2
def baseEnd_8335096 : Nat := 4279910549367826132267597

theorem tailTrace_8335096 : CollatzResearch.WordTrace tailWord_8335096 prefixEnd_8335096 4279910549367826132267597 := by
  unfold tailWord_8335096
  simp only [CollatzResearch.WordTrace]
  refine ⟨152002963105689093954804571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202670617474252125273072761 152002963105689093954804571)
  ·
    refine ⟨228004444658533640932206857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152002963105689093954804571 228004444658533640932206857)
    ·
      refine ⟨171003333493900230699155143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228004444658533640932206857 171003333493900230699155143)
      ·
        refine ⟨256505000240850346048732715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171003333493900230699155143 256505000240850346048732715)
        ·
          refine ⟨384757500361275519073099073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256505000240850346048732715 384757500361275519073099073)
          ·
            refine ⟨288568125270956639304824305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384757500361275519073099073 288568125270956639304824305)
            ·
              refine ⟨216426093953217479478618229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288568125270956639304824305 216426093953217479478618229)
              ·
                refine ⟨20289946308114138701120459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216426093953217479478618229 20289946308114138701120459)
                ·
                  refine ⟨30434919462171208051680689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20289946308114138701120459 30434919462171208051680689)
                  ·
                    refine ⟨22826189596628406038760517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30434919462171208051680689 22826189596628406038760517)
                    ·
                      refine ⟨4279910549367826132267597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22826189596628406038760517 4279910549367826132267597)
                      ·
                        rfl

theorem cell23_8335096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_8335096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335096 prefixEnd_8335096 := by exact prefixLift 8335096
  have htrace : WordTrace (prefixWord ++ tailWord_8335096) baseStart_8335096 baseEnd_8335096 := by
    simpa [prefixWord, tailWord_8335096, baseEnd_8335096] using wordTrace_append hprefix tailTrace_8335096
  have hstable : (prefixWord ++ tailWord_8335096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335096).length < 2 ^ (prefixWord ++ tailWord_8335096).sum := by decide
  have hdescent : baseEnd_8335096 < baseStart_8335096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335100 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_8335100 : Nat := 118140960795 + 8335100 * 2 ^ 59
def prefixEnd_8335100 : Nat := 4983230072969 + 3 ^ 40 * 8335100 * 2
def baseEnd_8335100 : Nat := 4279912603290444116617579

theorem tailTrace_8335100 : CollatzResearch.WordTrace tailWord_8335100 prefixEnd_8335100 4279912603290444116617579 := by
  unfold tailWord_8335100
  simp only [CollatzResearch.WordTrace]
  refine ⟨152003036051681848296377377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202670714735575797728503169 152003036051681848296377377)
  ·
    refine ⟨114002277038761386222283033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152003036051681848296377377 114002277038761386222283033)
    ·
      refine ⟨85501707779071039666712275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114002277038761386222283033 85501707779071039666712275)
      ·
        refine ⟨128252561668606559500068413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85501707779071039666712275 128252561668606559500068413)
        ·
          refine ⟨48094710625727459812525655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128252561668606559500068413 48094710625727459812525655)
          ·
            refine ⟨72142065938591189718788483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48094710625727459812525655 72142065938591189718788483)
            ·
              refine ⟨108213098907886784578182725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72142065938591189718788483 108213098907886784578182725)
              ·
                refine ⟨20289956045228772108409261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108213098907886784578182725 20289956045228772108409261)
                ·
                  refine ⟨7608733516960789540653473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20289956045228772108409261 7608733516960789540653473)
                  ·
                    refine ⟨5706550137720592155490105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608733516960789540653473 5706550137720592155490105)
                    ·
                      refine ⟨4279912603290444116617579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706550137720592155490105 4279912603290444116617579)
                      ·
                        rfl

theorem cell23_8335100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_8335100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335100 prefixEnd_8335100 := by exact prefixLift 8335100
  have htrace : WordTrace (prefixWord ++ tailWord_8335100) baseStart_8335100 baseEnd_8335100 := by
    simpa [prefixWord, tailWord_8335100, baseEnd_8335100] using wordTrace_append hprefix tailTrace_8335100
  have hstable : (prefixWord ++ tailWord_8335100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335100).length < 2 ^ (prefixWord ++ tailWord_8335100).sum := by decide
  have hdescent : baseEnd_8335100 < baseStart_8335100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335103 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_8335103 : Nat := 118140960795 + 8335103 * 2 ^ 59
def prefixEnd_8335103 : Nat := 4983230072969 + 3 ^ 40 * 8335103 * 2
def baseEnd_8335103 : Nat := 4279914143732407604880065

theorem tailTrace_8335103 : CollatzResearch.WordTrace tailWord_8335103 prefixEnd_8335103 4279914143732407604880065 := by
  unfold tailWord_8335103
  simp only [CollatzResearch.WordTrace]
  refine ⟨304006181522352828105113963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202670787681568552070075975 304006181522352828105113963)
  ·
    refine ⟨456009272283529242157670945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304006181522352828105113963 456009272283529242157670945)
    ·
      refine ⟨342006954212646931618253209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456009272283529242157670945 342006954212646931618253209)
      ·
        refine ⟨256505215659485198713689907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342006954212646931618253209 256505215659485198713689907)
        ·
          refine ⟨384757823489227798070534861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256505215659485198713689907 384757823489227798070534861)
          ·
            refine ⟨144284183808460424276450573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384757823489227798070534861 144284183808460424276450573)
            ·
              refine ⟨54106568928172659103668965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144284183808460424276450573 54106568928172659103668965)
              ·
                refine ⟨10144981674032373581937931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54106568928172659103668965 10144981674032373581937931)
                ·
                  refine ⟨15217472511048560372906897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10144981674032373581937931 15217472511048560372906897)
                  ·
                    refine ⟨11413104383286420279680173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15217472511048560372906897 11413104383286420279680173)
                    ·
                      refine ⟨4279914143732407604880065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413104383286420279680173 4279914143732407604880065)
                      ·
                        rfl

theorem cell23_8335103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_8335103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335103 prefixEnd_8335103 := by exact prefixLift 8335103
  have htrace : WordTrace (prefixWord ++ tailWord_8335103) baseStart_8335103 baseEnd_8335103 := by
    simpa [prefixWord, tailWord_8335103, baseEnd_8335103] using wordTrace_append hprefix tailTrace_8335103
  have hstable : (prefixWord ++ tailWord_8335103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335103).length < 2 ^ (prefixWord ++ tailWord_8335103).sum := by decide
  have hdescent : baseEnd_8335103 < baseStart_8335103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335111 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_8335111 : Nat := 118140960795 + 8335111 * 2 ^ 59
def prefixEnd_8335111 : Nat := 4983230072969 + 3 ^ 40 * 8335111 * 2
def baseEnd_8335111 : Nat := 4279918251577643573580029

theorem tailTrace_8335111 : CollatzResearch.WordTrace tailWord_8335111 prefixEnd_8335111 4279918251577643573580029 := by
  unfold tailWord_8335111
  simp only [CollatzResearch.WordTrace]
  refine ⟨304006473306323845471405187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202670982204215896980936791 304006473306323845471405187)
  ·
    refine ⟨456009709959485768207107781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304006473306323845471405187 456009709959485768207107781)
    ·
      refine ⟨85501820617403581538832709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456009709959485768207107781 85501820617403581538832709)
      ·
        refine ⟨16031591365763171538531133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85501820617403581538832709 16031591365763171538531133)
        ·
          refine ⟨6011846762161189326949175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16031591365763171538531133 6011846762161189326949175)
          ·
            refine ⟨9017770143241783990423763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011846762161189326949175 9017770143241783990423763)
            ·
              refine ⟨13526655214862675985635645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017770143241783990423763 13526655214862675985635645)
              ·
                refine ⟨5072495705573503494613367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13526655214862675985635645 5072495705573503494613367)
                ·
                  refine ⟨7608743558360255241920051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072495705573503494613367 7608743558360255241920051)
                  ·
                    refine ⟨11413115337540382862880077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7608743558360255241920051 11413115337540382862880077)
                    ·
                      refine ⟨4279918251577643573580029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413115337540382862880077 4279918251577643573580029)
                      ·
                        rfl

theorem cell23_8335111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_8335111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335111 prefixEnd_8335111 := by exact prefixLift 8335111
  have htrace : WordTrace (prefixWord ++ tailWord_8335111) baseStart_8335111 baseEnd_8335111 := by
    simpa [prefixWord, tailWord_8335111, baseEnd_8335111] using wordTrace_append hprefix tailTrace_8335111
  have hstable : (prefixWord ++ tailWord_8335111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335111).length < 2 ^ (prefixWord ++ tailWord_8335111).sum := by decide
  have hdescent : baseEnd_8335111 < baseStart_8335111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335136 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_8335136 : Nat := 118140960795 + 8335136 * 2 ^ 59
def prefixEnd_8335136 : Nat := 4983230072969 + 3 ^ 40 * 8335136 * 2
def baseEnd_8335136 : Nat := 1426643696198001991922471

theorem tailTrace_8335136 : CollatzResearch.WordTrace tailWord_8335136 prefixEnd_8335136 1426643696198001991922471 := by
  unfold tailWord_8335136
  simp only [CollatzResearch.WordTrace]
  refine ⟨152003692565616637370532631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202671590087488849827376841 152003692565616637370532631)
  ·
    refine ⟨228005538848424956055798947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152003692565616637370532631 228005538848424956055798947)
    ·
      refine ⟨342008308272637434083698421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228005538848424956055798947 342008308272637434083698421)
      ·
        refine ⟨32063278900559759445346727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342008308272637434083698421 32063278900559759445346727)
        ·
          refine ⟨48094918350839639168020091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32063278900559759445346727 48094918350839639168020091)
          ·
            refine ⟨72142377526259458752030137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48094918350839639168020091 72142377526259458752030137)
            ·
              refine ⟨54106783144694594064022603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72142377526259458752030137 54106783144694594064022603)
              ·
                refine ⟨81160174717041891096033905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54106783144694594064022603 81160174717041891096033905)
                ·
                  refine ⟨60870131037781418322025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81160174717041891096033905 60870131037781418322025429)
                  ·
                    refine ⟨1426643696198001991922471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60870131037781418322025429 1426643696198001991922471)
                    ·
                      rfl

theorem cell23_8335136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_8335136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335136 prefixEnd_8335136 := by exact prefixLift 8335136
  have htrace : WordTrace (prefixWord ++ tailWord_8335136) baseStart_8335136 baseEnd_8335136 := by
    simpa [prefixWord, tailWord_8335136, baseEnd_8335136] using wordTrace_append hprefix tailTrace_8335136
  have hstable : (prefixWord ++ tailWord_8335136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335136).length < 2 ^ (prefixWord ++ tailWord_8335136).sum := by decide
  have hdescent : baseEnd_8335136 < baseStart_8335136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335160 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_8335160 : Nat := 118140960795 + 8335160 * 2 ^ 59
def prefixEnd_8335160 : Nat := 4983230072969 + 3 ^ 40 * 8335160 * 2
def baseEnd_8335160 : Nat := 4279943412129713881867303

theorem tailTrace_8335160 : CollatzResearch.WordTrace tailWord_8335160 prefixEnd_8335160 4279943412129713881867303 := by
  unfold tailWord_8335160
  simp only [CollatzResearch.WordTrace]
  refine ⟨152004130241573163419969467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202672173655430884559959289 152004130241573163419969467)
  ·
    refine ⟨228006195362359745129954201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152004130241573163419969467 228006195362359745129954201)
    ·
      refine ⟨171004646521769808847465651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228006195362359745129954201 171004646521769808847465651)
      ·
        refine ⟨256506969782654713271198477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171004646521769808847465651 256506969782654713271198477)
        ·
          refine ⟨96190113668495517476699429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256506969782654713271198477 96190113668495517476699429)
          ·
            refine ⟨18035646312842909526881143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96190113668495517476699429 18035646312842909526881143)
            ·
              refine ⟨27053469469264364290321715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18035646312842909526881143 27053469469264364290321715)
              ·
                refine ⟨40580204203896546435482573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27053469469264364290321715 40580204203896546435482573)
                ·
                  refine ⟨15217576576461204913305965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40580204203896546435482573 15217576576461204913305965)
                  ·
                    refine ⟨5706591216172951842489737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15217576576461204913305965 5706591216172951842489737)
                    ·
                      refine ⟨4279943412129713881867303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706591216172951842489737 4279943412129713881867303)
                      ·
                        rfl

theorem cell23_8335160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_8335160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335160 prefixEnd_8335160 := by exact prefixLift 8335160
  have htrace : WordTrace (prefixWord ++ tailWord_8335160) baseStart_8335160 baseEnd_8335160 := by
    simpa [prefixWord, tailWord_8335160, baseEnd_8335160] using wordTrace_append hprefix tailTrace_8335160
  have hstable : (prefixWord ++ tailWord_8335160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335160).length < 2 ^ (prefixWord ++ tailWord_8335160).sum := by decide
  have hdescent : baseEnd_8335160 < baseStart_8335160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335177 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 1, 3, 2]
def baseStart_8335177 : Nat := 118140960795 + 8335177 * 2 ^ 59
def prefixEnd_8335177 : Nat := 4983230072969 + 3 ^ 40 * 8335177 * 2
def baseEnd_8335177 : Nat := 4279952141300840315354725

theorem tailTrace_8335177 : CollatzResearch.WordTrace tailWord_8335177 prefixEnd_8335177 4279952141300840315354725 := by
  unfold tailWord_8335177
  simp only [CollatzResearch.WordTrace]
  refine ⟨304008880524084738743307785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202672587016056492495538523 304008880524084738743307785)
  ·
    refine ⟨228006660393063554057480839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304008880524084738743307785 228006660393063554057480839)
    ·
      refine ⟨342009990589595331086221259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228006660393063554057480839 342009990589595331086221259)
      ·
        refine ⟨513014985884392996629331889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342009990589595331086221259 513014985884392996629331889)
        ·
          refine ⟨384761239413294747471998917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513014985884392996629331889 384761239413294747471998917)
          ·
            refine ⟨72142732389992765150999797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384761239413294747471998917 72142732389992765150999797)
            ·
              refine ⟨6763381161561821732906231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72142732389992765150999797 6763381161561821732906231)
              ·
                refine ⟨10145071742342732599359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763381161561821732906231 10145071742342732599359347)
                ·
                  refine ⟨15217607613514098899039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10145071742342732599359347 15217607613514098899039021)
                  ·
                    refine ⟨5706602855067787087139633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15217607613514098899039021 5706602855067787087139633)
                    ·
                      refine ⟨4279952141300840315354725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706602855067787087139633 4279952141300840315354725)
                      ·
                        rfl

theorem cell23_8335177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 3, 2].length) (baseStart_8335177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335177 prefixEnd_8335177 := by exact prefixLift 8335177
  have htrace : WordTrace (prefixWord ++ tailWord_8335177) baseStart_8335177 baseEnd_8335177 := by
    simpa [prefixWord, tailWord_8335177, baseEnd_8335177] using wordTrace_append hprefix tailTrace_8335177
  have hstable : (prefixWord ++ tailWord_8335177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335177).length < 2 ^ (prefixWord ++ tailWord_8335177).sum := by decide
  have hdescent : baseEnd_8335177 < baseStart_8335177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335207 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_8335207 : Nat := 118140960795 + 8335207 * 2 ^ 59
def prefixEnd_8335207 : Nat := 4983230072969 + 3 ^ 40 * 8335207 * 2
def baseEnd_8335207 : Nat := 4279967545720475197979587

theorem tailTrace_8335207 : CollatzResearch.WordTrace tailWord_8335207 prefixEnd_8335207 4279967545720475197979587 := by
  unfold tailWord_8335207
  simp only [CollatzResearch.WordTrace]
  refine ⟨304009974713976053866899875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202673316475984035911266583 304009974713976053866899875)
  ·
    refine ⟨456014962070964080800349813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304009974713976053866899875 456014962070964080800349813)
    ·
      refine ⟨42751402694152882575032795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456014962070964080800349813 42751402694152882575032795)
      ·
        refine ⟨64127104041229323862549193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42751402694152882575032795 64127104041229323862549193)
        ·
          refine ⟨48095328030921992896911895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64127104041229323862549193 48095328030921992896911895)
          ·
            refine ⟨72142992046382989345367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48095328030921992896911895 72142992046382989345367843)
            ·
              refine ⟨108214488069574484018051765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72142992046382989345367843 108214488069574484018051765)
              ·
                refine ⟨10145108256522607876692353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108214488069574484018051765 10145108256522607876692353)
                ·
                  refine ⟨7608831192391955907519265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10145108256522607876692353 7608831192391955907519265)
                  ·
                    refine ⟨5706623394293966930639449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608831192391955907519265 5706623394293966930639449)
                    ·
                      refine ⟨4279967545720475197979587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706623394293966930639449 4279967545720475197979587)
                      ·
                        rfl

theorem cell23_8335207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_8335207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335207 prefixEnd_8335207 := by exact prefixLift 8335207
  have htrace : WordTrace (prefixWord ++ tailWord_8335207) baseStart_8335207 baseEnd_8335207 := by
    simpa [prefixWord, tailWord_8335207, baseEnd_8335207] using wordTrace_append hprefix tailTrace_8335207
  have hstable : (prefixWord ++ tailWord_8335207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335207).length < 2 ^ (prefixWord ++ tailWord_8335207).sum := by decide
  have hdescent : baseEnd_8335207 < baseStart_8335207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335273 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_8335273 : Nat := 118140960795 + 8335273 * 2 ^ 59
def prefixEnd_8335273 : Nat := 4983230072969 + 3 ^ 40 * 8335273 * 2
def baseEnd_8335273 : Nat := 1426667145147890646584761

theorem tailTrace_8335273 : CollatzResearch.WordTrace tailWord_8335273 prefixEnd_8335273 1426667145147890646584761 := by
  unfold tailWord_8335273
  simp only [CollatzResearch.WordTrace]
  refine ⟨304012381931736947138802473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202674921287824631425868315 304012381931736947138802473)
  ·
    refine ⟨228009286448802710354101855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304012381931736947138802473 228009286448802710354101855)
    ·
      refine ⟨342013929673204065531152783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228009286448802710354101855 342013929673204065531152783)
      ·
        refine ⟨513020894509806098296729175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342013929673204065531152783 513020894509806098296729175)
        ·
          refine ⟨769531341764709147445093763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513020894509806098296729175 769531341764709147445093763)
          ·
            refine ⟨1154297012647063721167640645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769531341764709147445093763 1154297012647063721167640645)
            ·
              refine ⟨216430689871324447718932621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1154297012647063721167640645 216430689871324447718932621)
              ·
                refine ⟨81161508701746667894599733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216430689871324447718932621 81161508701746667894599733)
                ·
                  refine ⟨7608891440788750115118725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81161508701746667894599733 7608891440788750115118725)
                  ·
                    refine ⟨1426667145147890646584761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608891440788750115118725 1426667145147890646584761)
                    ·
                      rfl

theorem cell23_8335273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_8335273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335273 prefixEnd_8335273 := by exact prefixLift 8335273
  have htrace : WordTrace (prefixWord ++ tailWord_8335273) baseStart_8335273 baseEnd_8335273 := by
    simpa [prefixWord, tailWord_8335273, baseEnd_8335273] using wordTrace_append hprefix tailTrace_8335273
  have hstable : (prefixWord ++ tailWord_8335273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335273).length < 2 ^ (prefixWord ++ tailWord_8335273).sum := by decide
  have hdescent : baseEnd_8335273 < baseStart_8335273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335283 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3]
def baseStart_8335283 : Nat := 118140960795 + 8335283 * 2 ^ 59
def prefixEnd_8335283 : Nat := 4983230072969 + 3 ^ 40 * 8335283 * 2
def baseEnd_8335283 : Nat := 4280006570250216900629237

theorem tailTrace_8335283 : CollatzResearch.WordTrace tailWord_8335283 prefixEnd_8335283 4280006570250216900629237 := by
  unfold tailWord_8335283
  simp only [CollatzResearch.WordTrace]
  refine ⟨304012746661700718846666503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202675164441133812564444335 304012746661700718846666503)
  ·
    refine ⟨456019119992551078269999755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304012746661700718846666503 456019119992551078269999755)
    ·
      refine ⟨684028679988826617404999633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456019119992551078269999755 684028679988826617404999633)
      ·
        refine ⟨513021509991619963053749725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684028679988826617404999633 513021509991619963053749725)
        ·
          refine ⟨192383066246857486145156147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513021509991619963053749725 192383066246857486145156147)
          ·
            refine ⟨288574599370286229217734221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192383066246857486145156147 288574599370286229217734221)
            ·
              refine ⟨108215474763857335956650333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288574599370286229217734221 108215474763857335956650333)
              ·
                refine ⟨40580803036446500983743875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108215474763857335956650333 40580803036446500983743875)
                ·
                  refine ⟨60871204554669751475615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40580803036446500983743875 60871204554669751475615813)
                  ·
                    refine ⟨11413350854000578401677965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60871204554669751475615813 11413350854000578401677965)
                    ·
                      refine ⟨4280006570250216900629237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413350854000578401677965 4280006570250216900629237)
                      ·
                        rfl

theorem cell23_8335283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_8335283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335283 prefixEnd_8335283 := by exact prefixLift 8335283
  have htrace : WordTrace (prefixWord ++ tailWord_8335283) baseStart_8335283 baseEnd_8335283 := by
    simpa [prefixWord, tailWord_8335283, baseEnd_8335283] using wordTrace_append hprefix tailTrace_8335283
  have hstable : (prefixWord ++ tailWord_8335283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335283).length < 2 ^ (prefixWord ++ tailWord_8335283).sum := by decide
  have hdescent : baseEnd_8335283 < baseStart_8335283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335303 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 6]
def baseStart_8335303 : Nat := 118140960795 + 8335303 * 2 ^ 59
def prefixEnd_8335303 : Nat := 4983230072969 + 3 ^ 40 * 8335303 * 2
def baseEnd_8335303 : Nat := 475557426651478535819905

theorem tailTrace_8335303 : CollatzResearch.WordTrace tailWord_8335303 prefixEnd_8335303 475557426651478535819905 := by
  unfold tailWord_8335303
  simp only [CollatzResearch.WordTrace]
  refine ⟨304013476121628262262394563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202675650747752174841596375 304013476121628262262394563)
  ·
    refine ⟨456020214182442393393591845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304013476121628262262394563 456020214182442393393591845)
    ·
      refine ⟨85503790159207948761298471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456020214182442393393591845 85503790159207948761298471)
      ·
        refine ⟨128255685238811923141947707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85503790159207948761298471 128255685238811923141947707)
        ·
          refine ⟨192383527858217884712921561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128255685238811923141947707 192383527858217884712921561)
          ·
            refine ⟨144287645893663413534691171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192383527858217884712921561 144287645893663413534691171)
            ·
              refine ⟨216431468840495120302036757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144287645893663413534691171 216431468840495120302036757)
              ·
                refine ⟨10145225101898208764157973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216431468840495120302036757 10145225101898208764157973)
                ·
                  refine ⟨475557426651478535819905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10145225101898208764157973 475557426651478535819905)
                  ·
                    rfl

theorem cell23_8335303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 6].length) (baseStart_8335303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335303 prefixEnd_8335303 := by exact prefixLift 8335303
  have htrace : WordTrace (prefixWord ++ tailWord_8335303) baseStart_8335303 baseEnd_8335303 := by
    simpa [prefixWord, tailWord_8335303, baseEnd_8335303] using wordTrace_append hprefix tailTrace_8335303
  have hstable : (prefixWord ++ tailWord_8335303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335303).length < 2 ^ (prefixWord ++ tailWord_8335303).sum := by decide
  have hdescent : baseEnd_8335303 < baseStart_8335303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335313 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_8335313 : Nat := 118140960795 + 8335313 * 2 ^ 59
def prefixEnd_8335313 : Nat := 4983230072969 + 3 ^ 40 * 8335313 * 2
def baseEnd_8335313 : Nat := 4280021974669851783254099

theorem tailTrace_8335313 : CollatzResearch.WordTrace tailWord_8335313 prefixEnd_8335313 4280021974669851783254099 := by
  unfold tailWord_8335313
  simp only [CollatzResearch.WordTrace]
  refine ⟨304013840851592033970258593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202675893901061355980172395 304013840851592033970258593)
  ·
    refine ⟨228010380638694025477693945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304013840851592033970258593 228010380638694025477693945)
    ·
      refine ⟨171007785479020519108270459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228010380638694025477693945 171007785479020519108270459)
      ·
        refine ⟨256511678218530778662405689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171007785479020519108270459 256511678218530778662405689)
        ·
          refine ⟨192383758663898083996804267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256511678218530778662405689 192383758663898083996804267)
          ·
            refine ⟨288575637995847125995206401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192383758663898083996804267 288575637995847125995206401)
            ·
              refine ⟨216431728496885344496404801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288575637995847125995206401 216431728496885344496404801)
              ·
                refine ⟨162323796372664008372303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216431728496885344496404801 162323796372664008372303601)
                ·
                  refine ⟨121742847279498006279227701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162323796372664008372303601 121742847279498006279227701)
                  ·
                    refine ⟨11413391932452938088677597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121742847279498006279227701 11413391932452938088677597)
                    ·
                      refine ⟨4280021974669851783254099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413391932452938088677597 4280021974669851783254099)
                      ·
                        rfl

theorem cell23_8335313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_8335313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335313 prefixEnd_8335313 := by exact prefixLift 8335313
  have htrace : WordTrace (prefixWord ++ tailWord_8335313) baseStart_8335313 baseEnd_8335313 := by
    simpa [prefixWord, tailWord_8335313, baseEnd_8335313] using wordTrace_append hprefix tailTrace_8335313
  have hstable : (prefixWord ++ tailWord_8335313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335313).length < 2 ^ (prefixWord ++ tailWord_8335313).sum := by decide
  have hdescent : baseEnd_8335313 < baseStart_8335313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335340 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_8335340 : Nat := 118140960795 + 8335340 * 2 ^ 59
def prefixEnd_8335340 : Nat := 4983230072969 + 3 ^ 40 * 8335340 * 2
def baseEnd_8335340 : Nat := 4280035838647523177616475

theorem tailTrace_8335340 : CollatzResearch.WordTrace tailWord_8335340 prefixEnd_8335340 4280035838647523177616475 := by
  unfold tailWord_8335340
  simp only [CollatzResearch.WordTrace]
  refine ⟨152007412811247108790745737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202676550414996145054327649 152007412811247108790745737)
  ·
    refine ⟨114005559608435331593059303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152007412811247108790745737 114005559608435331593059303)
    ·
      refine ⟨171008339412652997389588955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114005559608435331593059303 171008339412652997389588955)
      ·
        refine ⟨256512509118979496084383433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171008339412652997389588955 256512509118979496084383433)
        ·
          refine ⟨192384381839234622063287575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256512509118979496084383433 192384381839234622063287575)
          ·
            refine ⟨288576572758851933094931363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192384381839234622063287575 288576572758851933094931363)
            ·
              refine ⟨432864859138277899642397045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288576572758851933094931363 432864859138277899642397045)
              ·
                refine ⟨40581080544213553091474723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432864859138277899642397045 40581080544213553091474723)
                ·
                  refine ⟨60871620816320329637212085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40581080544213553091474723 60871620816320329637212085)
                  ·
                    refine ⟨5706714451530030903488633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60871620816320329637212085 5706714451530030903488633)
                    ·
                      refine ⟨4280035838647523177616475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706714451530030903488633 4280035838647523177616475)
                      ·
                        rfl

theorem cell23_8335340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_8335340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335340 prefixEnd_8335340 := by exact prefixLift 8335340
  have htrace : WordTrace (prefixWord ++ tailWord_8335340) baseStart_8335340 baseEnd_8335340 := by
    simpa [prefixWord, tailWord_8335340, baseEnd_8335340] using wordTrace_append hprefix tailTrace_8335340
  have hstable : (prefixWord ++ tailWord_8335340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335340).length < 2 ^ (prefixWord ++ tailWord_8335340).sum := by decide
  have hdescent : baseEnd_8335340 < baseStart_8335340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335357 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_8335357 : Nat := 118140960795 + 8335357 * 2 ^ 59
def prefixEnd_8335357 : Nat := 4983230072969 + 3 ^ 40 * 8335357 * 2
def baseEnd_8335357 : Nat := 4280044567818649611103897

theorem tailTrace_8335357 : CollatzResearch.WordTrace tailWord_8335357 prefixEnd_8335357 4280044567818649611103897 := by
  unfold tailWord_8335357
  simp only [CollatzResearch.WordTrace]
  refine ⟨304015445663432629484860325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202676963775621752989906883 304015445663432629484860325)
  ·
    refine ⟨57002896061893618028411311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304015445663432629484860325 57002896061893618028411311)
    ·
      refine ⟨85504344092840427042616967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57002896061893618028411311 85504344092840427042616967)
      ·
        refine ⟨128256516139260640563925451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85504344092840427042616967 128256516139260640563925451)
        ·
          refine ⟨192384774208890960845888177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128256516139260640563925451 192384774208890960845888177)
          ·
            refine ⟨144288580656668220634416133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192384774208890960845888177 144288580656668220634416133)
            ·
              refine ⟨27054108873125291368953025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144288580656668220634416133 27054108873125291368953025)
              ·
                refine ⟨20290581654843968526714769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27054108873125291368953025 20290581654843968526714769)
                ·
                  refine ⟨15217936241132976395036077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20290581654843968526714769 15217936241132976395036077)
                  ·
                    refine ⟨5706726090424866148138529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15217936241132976395036077 5706726090424866148138529)
                    ·
                      refine ⟨4280044567818649611103897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706726090424866148138529 4280044567818649611103897)
                      ·
                        rfl

theorem cell23_8335357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_8335357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335357 prefixEnd_8335357 := by exact prefixLift 8335357
  have htrace : WordTrace (prefixWord ++ tailWord_8335357) baseStart_8335357 baseEnd_8335357 := by
    simpa [prefixWord, tailWord_8335357, baseEnd_8335357] using wordTrace_append hprefix tailTrace_8335357
  have hstable : (prefixWord ++ tailWord_8335357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335357).length < 2 ^ (prefixWord ++ tailWord_8335357).sum := by decide
  have hdescent : baseEnd_8335357 < baseStart_8335357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335358 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_8335358 : Nat := 118140960795 + 8335358 * 2 ^ 59
def prefixEnd_8335358 : Nat := 4983230072969 + 3 ^ 40 * 8335358 * 2
def baseEnd_8335358 : Nat := 1426681693766434702397131

theorem tailTrace_8335358 : CollatzResearch.WordTrace tailWord_8335358 prefixEnd_8335358 1426681693766434702397131 := by
  unfold tailWord_8335358
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001935267053625831955841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202676988090952671103764485 38001935267053625831955841)
  ·
    refine ⟨28501451450290219373966881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38001935267053625831955841 28501451450290219373966881)
    ·
      refine ⟨21376088587717664530475161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28501451450290219373966881 21376088587717664530475161)
      ·
        refine ⟨16032066440788248397856371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21376088587717664530475161 16032066440788248397856371)
        ·
          refine ⟨24048099661182372596784557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032066440788248397856371 24048099661182372596784557)
          ·
            refine ⟨9018037372943389723794209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24048099661182372596784557 9018037372943389723794209)
            ·
              refine ⟨6763528029707542292845657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018037372943389723794209 6763528029707542292845657)
              ·
                refine ⟨5072646022280656719634243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763528029707542292845657 5072646022280656719634243)
                ·
                  refine ⟨7608969033420985079451365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072646022280656719634243 7608969033420985079451365)
                  ·
                    refine ⟨1426681693766434702397131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7608969033420985079451365 1426681693766434702397131)
                    ·
                      rfl

theorem cell23_8335358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_8335358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335358 prefixEnd_8335358 := by exact prefixLift 8335358
  have htrace : WordTrace (prefixWord ++ tailWord_8335358) baseStart_8335358 baseEnd_8335358 := by
    simpa [prefixWord, tailWord_8335358, baseEnd_8335358] using wordTrace_append hprefix tailTrace_8335358
  have hstable : (prefixWord ++ tailWord_8335358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335358).length < 2 ^ (prefixWord ++ tailWord_8335358).sum := by decide
  have hdescent : baseEnd_8335358 < baseStart_8335358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335421 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_8335421 : Nat := 118140960795 + 8335421 * 2 ^ 59
def prefixEnd_8335421 : Nat := 4983230072969 + 3 ^ 40 * 8335421 * 2
def baseEnd_8335421 : Nat := 4280077430580537360703603

theorem tailTrace_8335421 : CollatzResearch.WordTrace tailWord_8335421 prefixEnd_8335421 4280077430580537360703603 := by
  unfold tailWord_8335421
  simp only [CollatzResearch.WordTrace]
  refine ⟨304017779935200768415190117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202678519956800512276793411 304017779935200768415190117)
  ·
    refine ⟨57003333737850144077848147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304017779935200768415190117 57003333737850144077848147)
    ·
      refine ⟨85505000606775216116772221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003333737850144077848147 85505000606775216116772221)
      ·
        refine ⟨32064375227540706043789583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85505000606775216116772221 32064375227540706043789583)
        ·
          refine ⟨48096562841311059065684375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32064375227540706043789583 48096562841311059065684375)
          ·
            refine ⟨72144844261966588598526563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48096562841311059065684375 72144844261966588598526563)
            ·
              refine ⟨108217266392949882897789845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72144844261966588598526563 108217266392949882897789845)
              ·
                refine ⟨5072684362169525760833899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108217266392949882897789845 5072684362169525760833899)
                ·
                  refine ⟨7609026543254288641250849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072684362169525760833899 7609026543254288641250849)
                  ·
                    refine ⟨5706769907440716480938137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609026543254288641250849 5706769907440716480938137)
                    ·
                      refine ⟨4280077430580537360703603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706769907440716480938137 4280077430580537360703603)
                      ·
                        rfl

theorem cell23_8335421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_8335421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335421 prefixEnd_8335421 := by exact prefixLift 8335421
  have htrace : WordTrace (prefixWord ++ tailWord_8335421) baseStart_8335421 baseEnd_8335421 := by
    simpa [prefixWord, tailWord_8335421, baseEnd_8335421] using wordTrace_append hprefix tailTrace_8335421
  have hstable : (prefixWord ++ tailWord_8335421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335421).length < 2 ^ (prefixWord ++ tailWord_8335421).sum := by decide
  have hdescent : baseEnd_8335421 < baseStart_8335421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335423 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 9]
def baseStart_8335423 : Nat := 118140960795 + 8335423 * 2 ^ 59
def prefixEnd_8335423 : Nat := 4983230072969 + 3 ^ 40 * 8335423 * 2
def baseEnd_8335423 : Nat := 1426692819180615450959531

theorem tailTrace_8335423 : CollatzResearch.WordTrace tailWord_8335423 prefixEnd_8335423 1426692819180615450959531 := by
  unfold tailWord_8335423
  simp only [CollatzResearch.WordTrace]
  refine ⟨304017852881193522756762923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202678568587462348504508615 304017852881193522756762923)
  ·
    refine ⟨456026779321790284135144385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304017852881193522756762923 456026779321790284135144385)
    ·
      refine ⟨342020084491342713101358289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456026779321790284135144385 342020084491342713101358289)
      ·
        refine ⟨256515063368507034826018717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342020084491342713101358289 256515063368507034826018717)
        ·
          refine ⟨96193148763190138059757019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256515063368507034826018717 96193148763190138059757019)
          ·
            refine ⟨144289723144785207089635529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96193148763190138059757019 144289723144785207089635529)
            ·
              refine ⟨108217292358588905317226647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144289723144785207089635529 108217292358588905317226647)
              ·
                refine ⟨162325938537883357975839971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108217292358588905317226647 162325938537883357975839971)
                ·
                  refine ⟨243488907806825036963759957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162325938537883357975839971 243488907806825036963759957)
                  ·
                    refine ⟨1426692819180615450959531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243488907806825036963759957 1426692819180615450959531)
                    ·
                      rfl

theorem cell23_8335423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_8335423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335423 prefixEnd_8335423 := by exact prefixLift 8335423
  have htrace : WordTrace (prefixWord ++ tailWord_8335423) baseStart_8335423 baseEnd_8335423 := by
    simpa [prefixWord, tailWord_8335423, baseEnd_8335423] using wordTrace_append hprefix tailTrace_8335423
  have hstable : (prefixWord ++ tailWord_8335423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335423).length < 2 ^ (prefixWord ++ tailWord_8335423).sum := by decide
  have hdescent : baseEnd_8335423 < baseStart_8335423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335447 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_8335447 : Nat := 118140960795 + 8335447 * 2 ^ 59
def prefixEnd_8335447 : Nat := 4983230072969 + 3 ^ 40 * 8335447 * 2
def baseEnd_8335447 : Nat := 4280090781077554258978483

theorem tailTrace_8335447 : CollatzResearch.WordTrace tailWord_8335447 prefixEnd_8335447 4280090781077554258978483 := by
  unfold tailWord_8335447
  simp only [CollatzResearch.WordTrace]
  refine ⟨304018728233106574855636595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202679152155404383237091063 304018728233106574855636595)
  ·
    refine ⟨456028092349659862283454893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304018728233106574855636595 456028092349659862283454893)
    ·
      refine ⟨171010534631122448356295585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456028092349659862283454893 171010534631122448356295585)
      ·
        refine ⟨128257900973341836267221689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171010534631122448356295585 128257900973341836267221689)
        ·
          refine ⟨96193425730006377200416267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128257900973341836267221689 96193425730006377200416267)
          ·
            refine ⟨144290138595009565800624401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96193425730006377200416267 144290138595009565800624401)
            ·
              refine ⟨108217603946257174350468301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144290138595009565800624401 108217603946257174350468301)
              ·
                refine ⟨40581601479846440381425613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108217603946257174350468301 40581601479846440381425613)
                ·
                  refine ⟨15218100554942415143034605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40581601479846440381425613 15218100554942415143034605)
                  ·
                    refine ⟨5706787708103405678637977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15218100554942415143034605 5706787708103405678637977)
                    ·
                      refine ⟨4280090781077554258978483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706787708103405678637977 4280090781077554258978483)
                      ·
                        rfl

theorem cell23_8335447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_8335447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335447 prefixEnd_8335447 := by exact prefixLift 8335447
  have htrace : WordTrace (prefixWord ++ tailWord_8335447) baseStart_8335447 baseEnd_8335447 := by
    simpa [prefixWord, tailWord_8335447, baseEnd_8335447] using wordTrace_append hprefix tailTrace_8335447
  have hstable : (prefixWord ++ tailWord_8335447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335447).length < 2 ^ (prefixWord ++ tailWord_8335447).sum := by decide
  have hdescent : baseEnd_8335447 < baseStart_8335447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335480 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_8335480 : Nat := 118140960795 + 8335480 * 2 ^ 59
def prefixEnd_8335480 : Nat := 4983230072969 + 3 ^ 40 * 8335480 * 2
def baseEnd_8335480 : Nat := 4280107725939152629865831

theorem tailTrace_8335480 : CollatzResearch.WordTrace tailWord_8335480 prefixEnd_8335480 4280107725939152629865831 := by
  unfold tailWord_8335480
  simp only [CollatzResearch.WordTrace]
  refine ⟨152009965920993510745793947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202679954561324680994391929 152009965920993510745793947)
  ·
    refine ⟨228014948881490266118690921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152009965920993510745793947 228014948881490266118690921)
    ·
      refine ⟨171011211661117699589018191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228014948881490266118690921 171011211661117699589018191)
      ·
        refine ⟨256516817491676549383527287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171011211661117699589018191 256516817491676549383527287)
        ·
          refine ⟨384775226237514824075290931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256516817491676549383527287 384775226237514824075290931)
          ·
            refine ⟨577162839356272236112936397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384775226237514824075290931 577162839356272236112936397)
            ·
              refine ⟨216436064758602088542351149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577162839356272236112936397 216436064758602088542351149)
              ·
                refine ⟨81163524284475783203381681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216436064758602088542351149 81163524284475783203381681)
                ·
                  refine ⟨60872643213356837402536261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81163524284475783203381681 60872643213356837402536261)
                  ·
                    refine ⟨11413620602504407012975549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60872643213356837402536261 11413620602504407012975549)
                    ·
                      refine ⟨4280107725939152629865831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413620602504407012975549 4280107725939152629865831)
                      ·
                        rfl

theorem cell23_8335480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_8335480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335480 prefixEnd_8335480 := by exact prefixLift 8335480
  have htrace : WordTrace (prefixWord ++ tailWord_8335480) baseStart_8335480 baseEnd_8335480 := by
    simpa [prefixWord, tailWord_8335480, baseEnd_8335480] using wordTrace_append hprefix tailTrace_8335480
  have hstable : (prefixWord ++ tailWord_8335480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335480).length < 2 ^ (prefixWord ++ tailWord_8335480).sum := by decide
  have hdescent : baseEnd_8335480 < baseStart_8335480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335564 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_8335564 : Nat := 118140960795 + 8335564 * 2 ^ 59
def prefixEnd_8335564 : Nat := 4983230072969 + 3 ^ 40 * 8335564 * 2
def baseEnd_8335564 : Nat := 1426716952771376767071815

theorem tailTrace_8335564 : CollatzResearch.WordTrace tailWord_8335564 prefixEnd_8335564 1426716952771376767071815 := by
  unfold tailWord_8335564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152011497786841351918822873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202681997049121802558430497 152011497786841351918822873)
  ·
    refine ⟨114008623340131013939117155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152011497786841351918822873 114008623340131013939117155)
    ·
      refine ⟨171012935010196520908675733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114008623340131013939117155 171012935010196520908675733)
      ·
        refine ⟨8016231328602961917594175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171012935010196520908675733 8016231328602961917594175)
        ·
          refine ⟨12024346992904442876391263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016231328602961917594175 12024346992904442876391263)
          ·
            refine ⟨18036520489356664314586895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024346992904442876391263 18036520489356664314586895)
            ·
              refine ⟨27054780734034996471880343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036520489356664314586895 27054780734034996471880343)
              ·
                refine ⟨40582171101052494707820515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27054780734034996471880343 40582171101052494707820515)
                ·
                  refine ⟨60873256651578742061730773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40582171101052494707820515 60873256651578742061730773)
                  ·
                    refine ⟨1426716952771376767071815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60873256651578742061730773 1426716952771376767071815)
                    ·
                      rfl

theorem cell23_8335564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_8335564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335564 prefixEnd_8335564 := by exact prefixLift 8335564
  have htrace : WordTrace (prefixWord ++ tailWord_8335564) baseStart_8335564 baseEnd_8335564 := by
    simpa [prefixWord, tailWord_8335564, baseEnd_8335564] using wordTrace_append hprefix tailTrace_8335564
  have hstable : (prefixWord ++ tailWord_8335564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335564).length < 2 ^ (prefixWord ++ tailWord_8335564).sum := by decide
  have hdescent : baseEnd_8335564 < baseStart_8335564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335567 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 6, 2]
def baseStart_8335567 : Nat := 118140960795 + 8335567 * 2 ^ 59
def prefixEnd_8335567 : Nat := 4983230072969 + 3 ^ 40 * 8335567 * 2
def baseEnd_8335567 : Nat := 4280152398756093789477931

theorem tailTrace_8335567 : CollatzResearch.WordTrace tailWord_8335567 prefixEnd_8335567 4280152398756093789477931 := by
  unfold tailWord_8335567
  simp only [CollatzResearch.WordTrace]
  refine ⟨304023104992671835350004955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202682069995114556900003303 304023104992671835350004955)
  ·
    refine ⟨456034657489007753025007433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304023104992671835350004955 456034657489007753025007433)
    ·
      refine ⟨342025993116755814768755575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456034657489007753025007433 342025993116755814768755575)
      ·
        refine ⟨513038989675133722153133363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342025993116755814768755575 513038989675133722153133363)
        ·
          refine ⟨769558484512700583229700045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513038989675133722153133363 769558484512700583229700045)
          ·
            refine ⟨288584431692262718711137517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769558484512700583229700045 288584431692262718711137517)
            ·
              refine ⟨108219161884598519516676569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288584431692262718711137517 108219161884598519516676569)
              ·
                refine ⟨81164371413448889637507427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108219161884598519516676569 81164371413448889637507427)
                ·
                  refine ⟨121746557120173334456261141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81164371413448889637507427 121746557120173334456261141)
                  ·
                    refine ⟨5706869865008125052637241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121746557120173334456261141 5706869865008125052637241)
                    ·
                      refine ⟨4280152398756093789477931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706869865008125052637241 4280152398756093789477931)
                      ·
                        rfl

theorem cell23_8335567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6, 2].length) (baseStart_8335567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335567 prefixEnd_8335567 := by exact prefixLift 8335567
  have htrace : WordTrace (prefixWord ++ tailWord_8335567) baseStart_8335567 baseEnd_8335567 := by
    simpa [prefixWord, tailWord_8335567, baseEnd_8335567] using wordTrace_append hprefix tailTrace_8335567
  have hstable : (prefixWord ++ tailWord_8335567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335567).length < 2 ^ (prefixWord ++ tailWord_8335567).sum := by decide
  have hdescent : baseEnd_8335567 < baseStart_8335567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335594 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_8335594 : Nat := 118140960795 + 8335594 * 2 ^ 59
def prefixEnd_8335594 : Nat := 4983230072969 + 3 ^ 40 * 8335594 * 2
def baseEnd_8335594 : Nat := 1426722087577921727946769

theorem tailTrace_8335594 : CollatzResearch.WordTrace tailWord_8335594 prefixEnd_8335594 1426722087577921727946769 := by
  unfold tailWord_8335594
  simp only [CollatzResearch.WordTrace]
  refine ⟨76006022440893504740309459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202682726509049345974158557 76006022440893504740309459)
  ·
    refine ⟨114009033661340257110464189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76006022440893504740309459 114009033661340257110464189)
    ·
      refine ⟨42753387623002596416424071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114009033661340257110464189 42753387623002596416424071)
      ·
        refine ⟨64130081434503894624636107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42753387623002596416424071 64130081434503894624636107)
        ·
          refine ⟨96195122151755841936954161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64130081434503894624636107 96195122151755841936954161)
          ·
            refine ⟨72146341613816881452715621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96195122151755841936954161 72146341613816881452715621)
            ·
              refine ⟨13527439052590665272384179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72146341613816881452715621 13527439052590665272384179)
              ·
                refine ⟨20291158578885997908576269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527439052590665272384179 20291158578885997908576269)
                ·
                  refine ⟨7609184467082249215716101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20291158578885997908576269 7609184467082249215716101)
                  ·
                    refine ⟨1426722087577921727946769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609184467082249215716101 1426722087577921727946769)
                    ·
                      rfl

theorem cell23_8335594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_8335594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335594 prefixEnd_8335594 := by exact prefixLift 8335594
  have htrace : WordTrace (prefixWord ++ tailWord_8335594) baseStart_8335594 baseEnd_8335594 := by
    simpa [prefixWord, tailWord_8335594, baseEnd_8335594] using wordTrace_append hprefix tailTrace_8335594
  have hstable : (prefixWord ++ tailWord_8335594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335594).length < 2 ^ (prefixWord ++ tailWord_8335594).sum := by decide
  have hdescent : baseEnd_8335594 < baseStart_8335594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335617 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_8335617 : Nat := 118140960795 + 8335617 * 2 ^ 59
def prefixEnd_8335617 : Nat := 4983230072969 + 3 ^ 40 * 8335617 * 2
def baseEnd_8335617 : Nat := 4280178072788818593852701

theorem tailTrace_8335617 : CollatzResearch.WordTrace tailWord_8335617 prefixEnd_8335617 4280178072788818593852701 := by
  unfold tailWord_8335617
  simp only [CollatzResearch.WordTrace]
  refine ⟨304024928642490693889325105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202683285761660462592883403 304024928642490693889325105)
  ·
    refine ⟨228018696481868020416993829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304024928642490693889325105 228018696481868020416993829)
    ·
      refine ⟨42753505590350253828186343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228018696481868020416993829 42753505590350253828186343)
      ·
        refine ⟨64130258385525380742279515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42753505590350253828186343 64130258385525380742279515)
        ·
          refine ⟨96195387578288071113419273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64130258385525380742279515 96195387578288071113419273)
          ·
            refine ⟨72146540683716053335064455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96195387578288071113419273 72146540683716053335064455)
            ·
              refine ⟨108219811025574080002596683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72146540683716053335064455 108219811025574080002596683)
              ·
                refine ⟨162329716538361120003895025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108219811025574080002596683 162329716538361120003895025)
                ·
                  refine ⟨121747287403770840002921269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162329716538361120003895025 121747287403770840002921269)
                  ·
                    refine ⟨11413808194103516250273869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121747287403770840002921269 11413808194103516250273869)
                    ·
                      refine ⟨4280178072788818593852701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413808194103516250273869 4280178072788818593852701)
                      ·
                        rfl

theorem cell23_8335617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_8335617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335617 prefixEnd_8335617 := by exact prefixLift 8335617
  have htrace : WordTrace (prefixWord ++ tailWord_8335617) baseStart_8335617 baseEnd_8335617 := by
    simpa [prefixWord, tailWord_8335617, baseEnd_8335617] using wordTrace_append hprefix tailTrace_8335617
  have hstable : (prefixWord ++ tailWord_8335617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335617).length < 2 ^ (prefixWord ++ tailWord_8335617).sum := by decide
  have hdescent : baseEnd_8335617 < baseStart_8335617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335645 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_8335645 : Nat := 118140960795 + 8335645 * 2 ^ 59
def prefixEnd_8335645 : Nat := 4983230072969 + 3 ^ 40 * 8335645 * 2
def baseEnd_8335645 : Nat := 1426730816749048161434191

theorem tailTrace_8335645 : CollatzResearch.WordTrace tailWord_8335645 prefixEnd_8335645 1426730816749048161434191 := by
  unfold tailWord_8335645
  simp only [CollatzResearch.WordTrace]
  refine ⟨304025949886389254671344389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202683966590926169780896259 304025949886389254671344389)
  ·
    refine ⟨57004865603697985250877073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304025949886389254671344389 57004865603697985250877073)
    ·
      refine ⟨42753649202773488938157805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57004865603697985250877073 42753649202773488938157805)
      ·
        refine ⟨16032618451040058351809177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42753649202773488938157805 16032618451040058351809177)
        ·
          refine ⟨12024463838280043763856883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16032618451040058351809177 12024463838280043763856883)
          ·
            refine ⟨18036695757420065645785325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024463838280043763856883 18036695757420065645785325)
            ·
              refine ⟨6763760909032524617169497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18036695757420065645785325 6763760909032524617169497)
              ·
                refine ⟨5072820681774393462877123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763760909032524617169497 5072820681774393462877123)
                ·
                  refine ⟨7609231022661590194315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072820681774393462877123 7609231022661590194315685)
                  ·
                    refine ⟨1426730816749048161434191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609231022661590194315685 1426730816749048161434191)
                    ·
                      rfl

theorem cell23_8335645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_8335645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335645 prefixEnd_8335645 := by exact prefixLift 8335645
  have htrace : WordTrace (prefixWord ++ tailWord_8335645) baseStart_8335645 baseEnd_8335645 := by
    simpa [prefixWord, tailWord_8335645, baseEnd_8335645] using wordTrace_append hprefix tailTrace_8335645
  have hstable : (prefixWord ++ tailWord_8335645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335645).length < 2 ^ (prefixWord ++ tailWord_8335645).sum := by decide
  have hdescent : baseEnd_8335645 < baseStart_8335645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335658 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_8335658 : Nat := 118140960795 + 8335658 * 2 ^ 59
def prefixEnd_8335658 : Nat := 4983230072969 + 3 ^ 40 * 8335658 * 2
def baseEnd_8335658 : Nat := 475577680610628103715557

theorem tailTrace_8335658 : CollatzResearch.WordTrace tailWord_8335658 prefixEnd_8335658 475577680610628103715557 := by
  unfold tailWord_8335658
  simp only [CollatzResearch.WordTrace]
  refine ⟨76006606008835539472891907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202684282690228105261045085 76006606008835539472891907)
  ·
    refine ⟨114009909013253309209337861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76006606008835539472891907 114009909013253309209337861)
    ·
      refine ⟨21376857939984995476750849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114009909013253309209337861 21376857939984995476750849)
      ·
        refine ⟨16032643454988746607563137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21376857939984995476750849 16032643454988746607563137)
        ·
          refine ⟨12024482591241559955672353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16032643454988746607563137 12024482591241559955672353)
          ·
            refine ⟨9018361943431169966754265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12024482591241559955672353 9018361943431169966754265)
            ·
              refine ⟨6763771457573377475065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018361943431169966754265 6763771457573377475065699)
              ·
                refine ⟨10145657186360066212598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763771457573377475065699 10145657186360066212598549)
                ·
                  refine ⟨475577680610628103715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10145657186360066212598549 475577680610628103715557)
                  ·
                    rfl

theorem cell23_8335658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_8335658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335658 prefixEnd_8335658 := by exact prefixLift 8335658
  have htrace : WordTrace (prefixWord ++ tailWord_8335658) baseStart_8335658 baseEnd_8335658 := by
    simpa [prefixWord, tailWord_8335658, baseEnd_8335658] using wordTrace_append hprefix tailTrace_8335658
  have hstable : (prefixWord ++ tailWord_8335658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335658).length < 2 ^ (prefixWord ++ tailWord_8335658).sum := by decide
  have hdescent : baseEnd_8335658 < baseStart_8335658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335667 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 6]
def baseStart_8335667 : Nat := 118140960795 + 8335667 * 2 ^ 59
def prefixEnd_8335667 : Nat := 4983230072969 + 3 ^ 40 * 8335667 * 2
def baseEnd_8335667 : Nat := 1426734582273847799409157

theorem tailTrace_8335667 : CollatzResearch.WordTrace tailWord_8335667 prefixEnd_8335667 1426734582273847799409157 := by
  unfold tailWord_8335667
  simp only [CollatzResearch.WordTrace]
  refine ⟨304026752292309552428645255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202684501528206368285763503 304026752292309552428645255)
  ·
    refine ⟨456040128438464328642967883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304026752292309552428645255 456040128438464328642967883)
    ·
      refine ⟨684060192657696492964451825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456040128438464328642967883 684060192657696492964451825)
      ·
        refine ⟨513045144493272369723338869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684060192657696492964451825 513045144493272369723338869)
        ·
          refine ⟨48097982296244284661563019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 513045144493272369723338869 48097982296244284661563019)
          ·
            refine ⟨72146973444366426992344529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48097982296244284661563019 72146973444366426992344529)
            ·
              refine ⟨54110230083274820244258397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72146973444366426992344529 54110230083274820244258397)
              ·
                refine ⟨20291336281228057591596899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54110230083274820244258397 20291336281228057591596899)
                ·
                  refine ⟨30437004421842086387395349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20291336281228057591596899 30437004421842086387395349)
                  ·
                    refine ⟨1426734582273847799409157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30437004421842086387395349 1426734582273847799409157)
                    ·
                      rfl

theorem cell23_8335667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_8335667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335667 prefixEnd_8335667 := by exact prefixLift 8335667
  have htrace : WordTrace (prefixWord ++ tailWord_8335667) baseStart_8335667 baseEnd_8335667 := by
    simpa [prefixWord, tailWord_8335667, baseEnd_8335667] using wordTrace_append hprefix tailTrace_8335667
  have hstable : (prefixWord ++ tailWord_8335667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335667).length < 2 ^ (prefixWord ++ tailWord_8335667).sum := by decide
  have hdescent : baseEnd_8335667 < baseStart_8335667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335674 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_8335674 : Nat := 118140960795 + 8335674 * 2 ^ 59
def prefixEnd_8335674 : Nat := 4983230072969 + 3 ^ 40 * 8335674 * 2
def baseEnd_8335674 : Nat := 4280207341186124870839939

theorem tailTrace_8335674 : CollatzResearch.WordTrace tailWord_8335674 prefixEnd_8335674 4280207341186124870839939 := by
  unfold tailWord_8335674
  simp only [CollatzResearch.WordTrace]
  refine ⟨76006751900821048156037519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202684671735522795082766717 76006751900821048156037519)
  ·
    refine ⟨114010127851231572234056279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76006751900821048156037519 114010127851231572234056279)
    ·
      refine ⟨171015191776847358351084419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114010127851231572234056279 171015191776847358351084419)
      ·
        refine ⟨256522787665271037526626629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171015191776847358351084419 256522787665271037526626629)
        ·
          refine ⟨48098022687238319536242493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256522787665271037526626629 48098022687238319536242493)
          ·
            refine ⟨18036758507714369826090935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48098022687238319536242493 18036758507714369826090935)
            ·
              refine ⟨27055137761571554739136403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036758507714369826090935 27055137761571554739136403)
              ·
                refine ⟨40582706642357332108704605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27055137761571554739136403 40582706642357332108704605)
                ·
                  refine ⟨15218514990883999540764227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40582706642357332108704605 15218514990883999540764227)
                  ·
                    refine ⟨22827772486325999311146341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15218514990883999540764227 22827772486325999311146341)
                    ·
                      refine ⟨4280207341186124870839939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22827772486325999311146341 4280207341186124870839939)
                      ·
                        rfl

theorem cell23_8335674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_8335674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335674 prefixEnd_8335674 := by exact prefixLift 8335674
  have htrace : WordTrace (prefixWord ++ tailWord_8335674) baseStart_8335674 baseEnd_8335674 := by
    simpa [prefixWord, tailWord_8335674, baseEnd_8335674] using wordTrace_append hprefix tailTrace_8335674
  have hstable : (prefixWord ++ tailWord_8335674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335674).length < 2 ^ (prefixWord ++ tailWord_8335674).sum := by decide
  have hdescent : baseEnd_8335674 < baseStart_8335674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335678 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_8335678 : Nat := 118140960795 + 8335678 * 2 ^ 59
def prefixEnd_8335678 : Nat := 4983230072969 + 3 ^ 40 * 8335678 * 2
def baseEnd_8335678 : Nat := 4280209395108742855189921

theorem tailTrace_8335678 : CollatzResearch.WordTrace tailWord_8335678 prefixEnd_8335678 4280209395108742855189921 := by
  unfold tailWord_8335678
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003394186908712663411961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202684768996846467538197125 38003394186908712663411961)
  ·
    refine ⟨28502545640181534497558971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38003394186908712663411961 28502545640181534497558971)
    ·
      refine ⟨42753818460272301746338457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28502545640181534497558971 42753818460272301746338457)
      ·
        refine ⟨32065363845204226309753843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42753818460272301746338457 32065363845204226309753843)
        ·
          refine ⟨48098045767806339464630765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32065363845204226309753843 48098045767806339464630765)
          ·
            refine ⟨18036767162927377299236537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48098045767806339464630765 18036767162927377299236537)
            ·
              refine ⟨13527575372195532974427403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18036767162927377299236537 13527575372195532974427403)
              ·
                refine ⟨20291363058293299461641105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527575372195532974427403 20291363058293299461641105)
                ·
                  refine ⟨15218522293719974596230829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20291363058293299461641105 15218522293719974596230829)
                  ·
                    refine ⟨5706945860144990473586561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15218522293719974596230829 5706945860144990473586561)
                    ·
                      refine ⟨4280209395108742855189921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5706945860144990473586561 4280209395108742855189921)
                      ·
                        rfl

theorem cell23_8335678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_8335678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335678 prefixEnd_8335678 := by exact prefixLift 8335678
  have htrace : WordTrace (prefixWord ++ tailWord_8335678) baseStart_8335678 baseEnd_8335678 := by
    simpa [prefixWord, tailWord_8335678, baseEnd_8335678] using wordTrace_append hprefix tailTrace_8335678
  have hstable : (prefixWord ++ tailWord_8335678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335678).length < 2 ^ (prefixWord ++ tailWord_8335678).sum := by decide
  have hdescent : baseEnd_8335678 < baseStart_8335678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335714 : List Nat := [3, 3, 2, 1, 1, 2, 3, 8]
def baseStart_8335714 : Nat := 118140960795 + 8335714 * 2 ^ 59
def prefixEnd_8335714 : Nat := 4983230072969 + 3 ^ 40 * 8335714 * 2
def baseEnd_8335714 : Nat := 158526958533789063494065

theorem tailTrace_8335714 : CollatzResearch.WordTrace tailWord_8335714 prefixEnd_8335714 158526958533789063494065 := by
  unfold tailWord_8335714
  simp only [CollatzResearch.WordTrace]
  refine ⟨76007116630784819863901549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202685644348759519637070797 76007116630784819863901549)
  ·
    refine ⟨28502668736544307448963081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76007116630784819863901549 28502668736544307448963081)
    ·
      refine ⟨21377001552408230586722311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28502668736544307448963081 21377001552408230586722311)
      ·
        refine ⟨32065502328612345880083467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21377001552408230586722311 32065502328612345880083467)
        ·
          refine ⟨48098253492918518820125201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32065502328612345880083467 48098253492918518820125201)
          ·
            refine ⟨36073690119688889115093901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48098253492918518820125201 36073690119688889115093901)
            ·
              refine ⟨13527633794883333418160213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36073690119688889115093901 13527633794883333418160213)
              ·
                refine ⟨158526958533789063494065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13527633794883333418160213 158526958533789063494065)
                ·
                  rfl

theorem cell23_8335714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_8335714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335714 prefixEnd_8335714 := by exact prefixLift 8335714
  have htrace : WordTrace (prefixWord ++ tailWord_8335714) baseStart_8335714 baseEnd_8335714 := by
    simpa [prefixWord, tailWord_8335714, baseEnd_8335714] using wordTrace_append hprefix tailTrace_8335714
  have hstable : (prefixWord ++ tailWord_8335714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335714).length < 2 ^ (prefixWord ++ tailWord_8335714).sum := by decide
  have hdescent : baseEnd_8335714 < baseStart_8335714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335737 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_8335737 : Nat := 118140960795 + 8335737 * 2 ^ 59
def prefixEnd_8335737 : Nat := 4983230072969 + 3 ^ 40 * 8335737 * 2
def baseEnd_8335737 : Nat := 4280239690467358124352149

theorem tailTrace_8335737 : CollatzResearch.WordTrace tailWord_8335737 prefixEnd_8335737 4280239690467358124352149 := by
  unfold tailWord_8335737
  simp only [CollatzResearch.WordTrace]
  refine ⟨304029305402055954383693465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202686203601370636255795643 304029305402055954383693465)
  ·
    refine ⟨228021979051541965787770099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304029305402055954383693465 228021979051541965787770099)
    ·
      refine ⟨342032968577312948681655149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228021979051541965787770099 342032968577312948681655149)
      ·
        refine ⟨128262363216492355755620681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342032968577312948681655149 128262363216492355755620681)
        ·
          refine ⟨96196772412369266816715511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128262363216492355755620681 96196772412369266816715511)
          ·
            refine ⟨144295158618553900225073267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96196772412369266816715511 144295158618553900225073267)
            ·
              refine ⟨216442737927830850337609901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144295158618553900225073267 216442737927830850337609901)
              ·
                refine ⟨81166026722936568876603713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216442737927830850337609901 81166026722936568876603713)
                ·
                  refine ⟨60874520042202426657452785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81166026722936568876603713 60874520042202426657452785)
                  ·
                    refine ⟨45655890031651819993089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60874520042202426657452785 45655890031651819993089589)
                    ·
                      refine ⟨4280239690467358124352149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45655890031651819993089589 4280239690467358124352149)
                      ·
                        rfl

theorem cell23_8335737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_8335737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335737 prefixEnd_8335737 := by exact prefixLift 8335737
  have htrace : WordTrace (prefixWord ++ tailWord_8335737) baseStart_8335737 baseEnd_8335737 := by
    simpa [prefixWord, tailWord_8335737, baseEnd_8335737] using wordTrace_append hprefix tailTrace_8335737
  have hstable : (prefixWord ++ tailWord_8335737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335737).length < 2 ^ (prefixWord ++ tailWord_8335737).sum := by decide
  have hdescent : baseEnd_8335737 < baseStart_8335737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335745 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_8335745 : Nat := 118140960795 + 8335745 * 2 ^ 59
def prefixEnd_8335745 : Nat := 4983230072969 + 3 ^ 40 * 8335745 * 2
def baseEnd_8335745 : Nat := 4280243798312594093052113

theorem tailTrace_8335745 : CollatzResearch.WordTrace tailWord_8335745 prefixEnd_8335745 4280243798312594093052113 := by
  unfold tailWord_8335745
  simp only [CollatzResearch.WordTrace]
  refine ⟨304029597186026971749984689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202686398124017981166656459 304029597186026971749984689)
  ·
    refine ⟨228022197889520228812488517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304029597186026971749984689 228022197889520228812488517)
    ·
      refine ⟨42754162104285042902341597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228022197889520228812488517 42754162104285042902341597)
      ·
        refine ⟨16032810789106891088378099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42754162104285042902341597 16032810789106891088378099)
        ·
          refine ⟨24049216183660336632567149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032810789106891088378099 24049216183660336632567149)
          ·
            refine ⟨9018456068872626237212681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24049216183660336632567149 9018456068872626237212681)
            ·
              refine ⟨6763842051654469677909511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018456068872626237212681 6763842051654469677909511)
              ·
                refine ⟨10145763077481704516864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763842051654469677909511 10145763077481704516864267)
                ·
                  refine ⟨15218644616222556775296401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10145763077481704516864267 15218644616222556775296401)
                  ·
                    refine ⟨11413983462166917581472301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15218644616222556775296401 11413983462166917581472301)
                    ·
                      refine ⟨4280243798312594093052113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11413983462166917581472301 4280243798312594093052113)
                      ·
                        rfl

theorem cell23_8335745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_8335745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335745 prefixEnd_8335745 := by exact prefixLift 8335745
  have htrace : WordTrace (prefixWord ++ tailWord_8335745) baseStart_8335745 baseEnd_8335745 := by
    simpa [prefixWord, tailWord_8335745, baseEnd_8335745] using wordTrace_append hprefix tailTrace_8335745
  have hstable : (prefixWord ++ tailWord_8335745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335745).length < 2 ^ (prefixWord ++ tailWord_8335745).sum := by decide
  have hdescent : baseEnd_8335745 < baseStart_8335745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335758 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8335758 : Nat := 118140960795 + 8335758 * 2 ^ 59
def prefixEnd_8335758 : Nat := 4983230072969 + 3 ^ 40 * 8335758 * 2
def baseEnd_8335758 : Nat := 4280250473561102542189553

theorem tailTrace_8335758 : CollatzResearch.WordTrace tailWord_8335758 prefixEnd_8335758 4280250473561102542189553 := by
  unfold tailWord_8335758
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003758916872484371275991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202686714223319916646805285 38003758916872484371275991)
  ·
    refine ⟨57005638375308726556913987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38003758916872484371275991 57005638375308726556913987)
    ·
      refine ⟨85508457562963089835370981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57005638375308726556913987 85508457562963089835370981)
      ·
        refine ⟨16032835793055579344132059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85508457562963089835370981 16032835793055579344132059)
        ·
          refine ⟨24049253689583369016198089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032835793055579344132059 24049253689583369016198089)
          ·
            refine ⟨18036940267187526762148567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24049253689583369016198089 18036940267187526762148567)
            ·
              refine ⟨27055410400781290143222851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036940267187526762148567 27055410400781290143222851)
              ·
                refine ⟨40583115601171935214834277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27055410400781290143222851 40583115601171935214834277)
                ·
                  refine ⟨7609334175219737852781427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40583115601171935214834277 7609334175219737852781427)
                  ·
                    refine ⟨11414001262829606779172141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609334175219737852781427 11414001262829606779172141)
                    ·
                      refine ⟨4280250473561102542189553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414001262829606779172141 4280250473561102542189553)
                      ·
                        rfl

theorem cell23_8335758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8335758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335758 prefixEnd_8335758 := by exact prefixLift 8335758
  have htrace : WordTrace (prefixWord ++ tailWord_8335758) baseStart_8335758 baseEnd_8335758 := by
    simpa [prefixWord, tailWord_8335758, baseEnd_8335758] using wordTrace_append hprefix tailTrace_8335758
  have hstable : (prefixWord ++ tailWord_8335758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335758).length < 2 ^ (prefixWord ++ tailWord_8335758).sum := by decide
  have hdescent : baseEnd_8335758 < baseStart_8335758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335807 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_8335807 : Nat := 118140960795 + 8335807 * 2 ^ 59
def prefixEnd_8335807 : Nat := 4983230072969 + 3 ^ 40 * 8335807 * 2
def baseEnd_8335807 : Nat := 4280275634113172850476827

theorem tailTrace_8335807 : CollatzResearch.WordTrace tailWord_8335807 prefixEnd_8335807 4280275634113172850476827 := by
  unfold tailWord_8335807
  simp only [CollatzResearch.WordTrace]
  refine ⟨304031858511802356338741675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202687905674534904225827783 304031858511802356338741675)
  ·
    refine ⟨456047787767703534508112513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304031858511802356338741675 456047787767703534508112513)
    ·
      refine ⟨342035840825777650881084385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456047787767703534508112513 342035840825777650881084385)
      ·
        refine ⟨256526880619333238160813289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342035840825777650881084385 256526880619333238160813289)
        ·
          refine ⟨192395160464499928620609967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256526880619333238160813289 192395160464499928620609967)
          ·
            refine ⟨288592740696749892930914951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192395160464499928620609967 288592740696749892930914951)
            ·
              refine ⟨432889111045124839396372427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288592740696749892930914951 432889111045124839396372427)
              ·
                refine ⟨649333666567687259094558641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432889111045124839396372427 649333666567687259094558641)
                ·
                  refine ⟨487000249925765444320918981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649333666567687259094558641 487000249925765444320918981)
                  ·
                    refine ⟨91312546861081020810172309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487000249925765444320918981 91312546861081020810172309)
                    ·
                      refine ⟨4280275634113172850476827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91312546861081020810172309 4280275634113172850476827)
                      ·
                        rfl

theorem cell23_8335807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_8335807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335807 prefixEnd_8335807 := by exact prefixLift 8335807
  have htrace : WordTrace (prefixWord ++ tailWord_8335807) baseStart_8335807 baseEnd_8335807 := by
    simpa [prefixWord, tailWord_8335807, baseEnd_8335807] using wordTrace_append hprefix tailTrace_8335807
  have hstable : (prefixWord ++ tailWord_8335807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335807).length < 2 ^ (prefixWord ++ tailWord_8335807).sum := by decide
  have hdescent : baseEnd_8335807 < baseStart_8335807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335834 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_8335834 : Nat := 118140960795 + 8335834 * 2 ^ 59
def prefixEnd_8335834 : Nat := 4983230072969 + 3 ^ 40 * 8335834 * 2
def baseEnd_8335834 : Nat := 1426763166030281414946401

theorem tailTrace_8335834 : CollatzResearch.WordTrace tailWord_8335834 prefixEnd_8335834 1426763166030281414946401 := by
  unfold tailWord_8335834
  simp only [CollatzResearch.WordTrace]
  refine ⟨76008210820676134987493639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202688562188469693299983037 76008210820676134987493639)
  ·
    refine ⟨114012316231014202481240459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76008210820676134987493639 114012316231014202481240459)
    ·
      refine ⟨171018474346521303721860689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114012316231014202481240459 171018474346521303721860689)
      ·
        refine ⟨128263855759890977791395517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171018474346521303721860689 128263855759890977791395517)
        ·
          refine ⟨48098945909959116671773319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128263855759890977791395517 48098945909959116671773319)
          ·
            refine ⟨72148418864938675007659979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48098945909959116671773319 72148418864938675007659979)
            ·
              refine ⟨108222628297408012511489969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72148418864938675007659979 108222628297408012511489969)
              ·
                refine ⟨81166971223056009383617477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108222628297408012511489969 81166971223056009383617477)
                ·
                  refine ⟨15218807104323001759428277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81166971223056009383617477 15218807104323001759428277)
                  ·
                    refine ⟨1426763166030281414946401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15218807104323001759428277 1426763166030281414946401)
                    ·
                      rfl

theorem cell23_8335834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_8335834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335834 prefixEnd_8335834 := by exact prefixLift 8335834
  have htrace : WordTrace (prefixWord ++ tailWord_8335834) baseStart_8335834 baseEnd_8335834 := by
    simpa [prefixWord, tailWord_8335834, baseEnd_8335834] using wordTrace_append hprefix tailTrace_8335834
  have hstable : (prefixWord ++ tailWord_8335834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335834).length < 2 ^ (prefixWord ++ tailWord_8335834).sum := by decide
  have hdescent : baseEnd_8335834 < baseStart_8335834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335871 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 4, 2]
def baseStart_8335871 : Nat := 118140960795 + 8335871 * 2 ^ 59
def prefixEnd_8335871 : Nat := 4983230072969 + 3 ^ 40 * 8335871 * 2
def baseEnd_8335871 : Nat := 4280308496875060600076533

theorem tailTrace_8335871 : CollatzResearch.WordTrace tailWord_8335871 prefixEnd_8335871 4280308496875060600076533 := by
  unfold tailWord_8335871
  simp only [CollatzResearch.WordTrace]
  refine ⟨304034192783570495269071467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202689461855713663512714311 304034192783570495269071467)
  ·
    refine ⟨456051289175355742903607201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304034192783570495269071467 456051289175355742903607201)
    ·
      refine ⟨342038466881516807177705401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456051289175355742903607201 342038466881516807177705401)
      ·
        refine ⟨256528850161137605383279051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342038466881516807177705401 256528850161137605383279051)
        ·
          refine ⟨384793275241706408074918577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256528850161137605383279051 384793275241706408074918577)
          ·
            refine ⟨288594956431279806056188933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384793275241706408074918577 288594956431279806056188933)
            ·
              refine ⟨54111554330864963635535425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288594956431279806056188933 54111554330864963635535425)
              ·
                refine ⟨40583665748148722726651569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54111554330864963635535425 40583665748148722726651569)
                ·
                  refine ⟨30437749311111542044988677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40583665748148722726651569 30437749311111542044988677)
                  ·
                    refine ⟨5707077995833414133435377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30437749311111542044988677 5707077995833414133435377)
                    ·
                      refine ⟨4280308496875060600076533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707077995833414133435377 4280308496875060600076533)
                      ·
                        rfl

theorem cell23_8335871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_8335871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335871 prefixEnd_8335871 := by exact prefixLift 8335871
  have htrace : WordTrace (prefixWord ++ tailWord_8335871) baseStart_8335871 baseEnd_8335871 := by
    simpa [prefixWord, tailWord_8335871, baseEnd_8335871] using wordTrace_append hprefix tailTrace_8335871
  have hstable : (prefixWord ++ tailWord_8335871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335871).length < 2 ^ (prefixWord ++ tailWord_8335871).sum := by decide
  have hdescent : baseEnd_8335871 < baseStart_8335871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335971 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 6, 4]
def baseStart_8335971 : Nat := 118140960795 + 8335971 * 2 ^ 59
def prefixEnd_8335971 : Nat := 4983230072969 + 3 ^ 40 * 8335971 * 2
def baseEnd_8335971 : Nat := 1426786614980170069608691

theorem tailTrace_8335971 : CollatzResearch.WordTrace tailWord_8335971 prefixEnd_8335971 1426786614980170069608691 := by
  unfold tailWord_8335971
  simp only [CollatzResearch.WordTrace]
  refine ⟨304037840083208212347711767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202691893388805474898474511 304037840083208212347711767)
  ·
    refine ⟨456056760124812318521567651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304037840083208212347711767 456056760124812318521567651)
    ·
      refine ⟨684085140187218477782351477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456056760124812318521567651 684085140187218477782351477)
      ·
        refine ⟨64132981892551732292095451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 684085140187218477782351477 64132981892551732292095451)
        ·
          refine ⟨96199472838827598438143177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64132981892551732292095451 96199472838827598438143177)
          ·
            refine ⟨72149604629120698828607383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96199472838827598438143177 72149604629120698828607383)
            ·
              refine ⟨108224406943681048242911075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72149604629120698828607383 108224406943681048242911075)
              ·
                refine ⟨162336610415521572364366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108224406943681048242911075 162336610415521572364366613)
                ·
                  refine ⟨7609528613227573704579685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162336610415521572364366613 7609528613227573704579685)
                  ·
                    refine ⟨1426786614980170069608691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609528613227573704579685 1426786614980170069608691)
                    ·
                      rfl

theorem cell23_8335971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 4].length) (baseStart_8335971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335971 prefixEnd_8335971 := by exact prefixLift 8335971
  have htrace : WordTrace (prefixWord ++ tailWord_8335971) baseStart_8335971 baseEnd_8335971 := by
    simpa [prefixWord, tailWord_8335971, baseEnd_8335971] using wordTrace_append hprefix tailTrace_8335971
  have hstable : (prefixWord ++ tailWord_8335971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335971).length < 2 ^ (prefixWord ++ tailWord_8335971).sum := by decide
  have hdescent : baseEnd_8335971 < baseStart_8335971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335978 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_8335978 : Nat := 118140960795 + 8335978 * 2 ^ 59
def prefixEnd_8335978 : Nat := 4983230072969 + 3 ^ 40 * 8335978 * 2
def baseEnd_8335978 : Nat := 4280363439305091681438541

theorem tailTrace_8335978 : CollatzResearch.WordTrace tailWord_8335978 prefixEnd_8335978 4280363439305091681438541 := by
  unfold tailWord_8335978
  simp only [CollatzResearch.WordTrace]
  refine ⟨76009523848545713135804147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202692063596121901695477725 76009523848545713135804147)
  ·
    refine ⟨114014285772818569703706221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76009523848545713135804147 114014285772818569703706221)
    ·
      refine ⟨42755357164806963638889833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114014285772818569703706221 42755357164806963638889833)
      ·
        refine ⟨32066517873605222729167375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42755357164806963638889833 32066517873605222729167375)
        ·
          refine ⟨48099776810407834093751063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32066517873605222729167375 48099776810407834093751063)
          ·
            refine ⟨72149665215611751140626595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48099776810407834093751063 72149665215611751140626595)
            ·
              refine ⟨108224497823417626710939893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72149665215611751140626595 108224497823417626710939893)
              ·
                refine ⟨10146046670945402504150615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108224497823417626710939893 10146046670945402504150615)
                ·
                  refine ⟨15219070006418103756225923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146046670945402504150615 15219070006418103756225923)
                  ·
                    refine ⟨22828605009627155634338885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15219070006418103756225923 22828605009627155634338885)
                    ·
                      refine ⟨4280363439305091681438541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22828605009627155634338885 4280363439305091681438541)
                      ·
                        rfl

theorem cell23_8335978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_8335978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335978 prefixEnd_8335978 := by exact prefixLift 8335978
  have htrace : WordTrace (prefixWord ++ tailWord_8335978) baseStart_8335978 baseEnd_8335978 := by
    simpa [prefixWord, tailWord_8335978, baseEnd_8335978] using wordTrace_append hprefix tailTrace_8335978
  have hstable : (prefixWord ++ tailWord_8335978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335978).length < 2 ^ (prefixWord ++ tailWord_8335978).sum := by decide
  have hdescent : baseEnd_8335978 < baseStart_8335978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8335989 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8335989 : Nat := 118140960795 + 8335989 * 2 ^ 59
def prefixEnd_8335989 : Nat := 4983230072969 + 3 ^ 40 * 8335989 * 2
def baseEnd_8335989 : Nat := 4280369087592291138400991

theorem tailTrace_8335989 : CollatzResearch.WordTrace tailWord_8335989 prefixEnd_8335989 4280369087592291138400991 := by
  unfold tailWord_8335989
  simp only [CollatzResearch.WordTrace]
  refine ⟨304038496597143001421867021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202692331064762000947911347 304038496597143001421867021)
  ·
    refine ⟨114014436223928625533200133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304038496597143001421867021 114014436223928625533200133)
    ·
      refine ⟨21377706791986617287475025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114014436223928625533200133 21377706791986617287475025)
      ·
        refine ⟨16033280093989962965606269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21377706791986617287475025 16033280093989962965606269)
        ·
          refine ⟨6012480035246236112102351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16033280093989962965606269 6012480035246236112102351)
          ·
            refine ⟨9018720052869354168153527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012480035246236112102351 9018720052869354168153527)
            ·
              refine ⟨13528080079304031252230291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018720052869354168153527 13528080079304031252230291)
              ·
                refine ⟨20292120118956046878345437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13528080079304031252230291 20292120118956046878345437)
                ·
                  refine ⟨7609545044608517579379539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20292120118956046878345437 7609545044608517579379539)
                  ·
                    refine ⟨11414317566912776369069309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609545044608517579379539 11414317566912776369069309)
                    ·
                      refine ⟨4280369087592291138400991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414317566912776369069309 4280369087592291138400991)
                      ·
                        rfl

theorem cell23_8335989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8335989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8335989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8335989 prefixEnd_8335989 := by exact prefixLift 8335989
  have htrace : WordTrace (prefixWord ++ tailWord_8335989) baseStart_8335989 baseEnd_8335989 := by
    simpa [prefixWord, tailWord_8335989, baseEnd_8335989] using wordTrace_append hprefix tailTrace_8335989
  have hstable : (prefixWord ++ tailWord_8335989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8335989).length < 2 ^ (prefixWord ++ tailWord_8335989).sum := by decide
  have hdescent : baseEnd_8335989 < baseStart_8335989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8335989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336001 : List Nat := [1, 2, 4, 2, 1, 1, 4, 8]
def baseStart_8336001 : Nat := 118140960795 + 8336001 * 2 ^ 59
def prefixEnd_8336001 : Nat := 4983230072969 + 3 ^ 40 * 8336001 * 2
def baseEnd_8336001 : Nat := 158532416642968336720405

theorem tailTrace_8336001 : CollatzResearch.WordTrace tailWord_8336001 prefixEnd_8336001 158532416642968336720405 := by
  unfold tailWord_8336001
  simp only [CollatzResearch.WordTrace]
  refine ⟨304038934273099527471303857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202692622848733018314202571 304038934273099527471303857)
  ·
    refine ⟨228029200704824645603477893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304038934273099527471303857 228029200704824645603477893)
    ·
      refine ⟨42755475132154621050652105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228029200704824645603477893 42755475132154621050652105)
      ·
        refine ⟨32066606349115965787989079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42755475132154621050652105 32066606349115965787989079)
        ·
          refine ⟨48099909523673948681983619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32066606349115965787989079 48099909523673948681983619)
          ·
            refine ⟨72149864285510923022975429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48099909523673948681983619 72149864285510923022975429)
            ·
              refine ⟨13528099553533298066807893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72149864285510923022975429 13528099553533298066807893)
              ·
                refine ⟨158532416642968336720405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13528099553533298066807893 158532416642968336720405)
                ·
                  rfl

theorem cell23_8336001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 8].length) (baseStart_8336001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336001 prefixEnd_8336001 := by exact prefixLift 8336001
  have htrace : WordTrace (prefixWord ++ tailWord_8336001) baseStart_8336001 baseEnd_8336001 := by
    simpa [prefixWord, tailWord_8336001, baseEnd_8336001] using wordTrace_append hprefix tailTrace_8336001
  have hstable : (prefixWord ++ tailWord_8336001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336001).length < 2 ^ (prefixWord ++ tailWord_8336001).sum := by decide
  have hdescent : baseEnd_8336001 < baseStart_8336001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336005 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_8336005 : Nat := 118140960795 + 8336005 * 2 ^ 59
def prefixEnd_8336005 : Nat := 4983230072969 + 3 ^ 40 * 8336005 * 2
def baseEnd_8336005 : Nat := 1426792434427587691933639

theorem tailTrace_8336005 : CollatzResearch.WordTrace tailWord_8336005 prefixEnd_8336005 1426792434427587691933639 := by
  unfold tailWord_8336005
  simp only [CollatzResearch.WordTrace]
  refine ⟨304039080165085036154449469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202692720110056690769632979 304039080165085036154449469)
  ·
    refine ⟨114014655061906888557918551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304039080165085036154449469 114014655061906888557918551)
    ·
      refine ⟨171021982592860332836877827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114014655061906888557918551 171021982592860332836877827)
      ·
        refine ⟨256532973889290499255316741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171021982592860332836877827 256532973889290499255316741)
        ·
          refine ⟨48099932604241968610371889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256532973889290499255316741 48099932604241968610371889)
          ·
            refine ⟨36074949453181476457778917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48099932604241968610371889 36074949453181476457778917)
            ·
              refine ⟨6764053022471526835833547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36074949453181476457778917 6764053022471526835833547)
              ·
                refine ⟨10146079533707290253750321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764053022471526835833547 10146079533707290253750321)
                ·
                  refine ⟨7609559650280467690312741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10146079533707290253750321 7609559650280467690312741)
                  ·
                    refine ⟨1426792434427587691933639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609559650280467690312741 1426792434427587691933639)
                    ·
                      rfl

theorem cell23_8336005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_8336005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336005 prefixEnd_8336005 := by exact prefixLift 8336005
  have htrace : WordTrace (prefixWord ++ tailWord_8336005) baseStart_8336005 baseEnd_8336005 := by
    simpa [prefixWord, tailWord_8336005, baseEnd_8336005] using wordTrace_append hprefix tailTrace_8336005
  have hstable : (prefixWord ++ tailWord_8336005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336005).length < 2 ^ (prefixWord ++ tailWord_8336005).sum := by decide
  have hdescent : baseEnd_8336005 < baseStart_8336005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336028 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_8336028 : Nat := 118140960795 + 8336028 * 2 ^ 59
def prefixEnd_8336028 : Nat := 4983230072969 + 3 ^ 40 * 8336028 * 2
def baseEnd_8336028 : Nat := 4280389113337816485813311

theorem tailTrace_8336028 : CollatzResearch.WordTrace tailWord_8336028 prefixEnd_8336028 4280389113337816485813311 := by
  unfold tailWord_8336028
  simp only [CollatzResearch.WordTrace]
  refine ⟨152019959522000855541268369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202693279362667807388357825 152019959522000855541268369)
  ·
    refine ⟨114014969641500641655951277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152019959522000855541268369 114014969641500641655951277)
    ·
      refine ⟨42755613615562740620981729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114014969641500641655951277 42755613615562740620981729)
      ·
        refine ⟨32066710211672055465736297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42755613615562740620981729 32066710211672055465736297)
        ·
          refine ⟨24050032658754041599302223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32066710211672055465736297 24050032658754041599302223)
          ·
            refine ⟨36075048988131062398953335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24050032658754041599302223 36075048988131062398953335)
            ·
              refine ⟨54112573482196593598430003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36075048988131062398953335 54112573482196593598430003)
              ·
                refine ⟨81168860223294890397645005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54112573482196593598430003 81168860223294890397645005)
                ·
                  refine ⟨30438322583735583899116877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81168860223294890397645005 30438322583735583899116877)
                  ·
                    refine ⟨11414370968900843962168829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30438322583735583899116877 11414370968900843962168829)
                    ·
                      refine ⟨4280389113337816485813311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414370968900843962168829 4280389113337816485813311)
                      ·
                        rfl

theorem cell23_8336028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_8336028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336028 prefixEnd_8336028 := by exact prefixLift 8336028
  have htrace : WordTrace (prefixWord ++ tailWord_8336028) baseStart_8336028 baseEnd_8336028 := by
    simpa [prefixWord, tailWord_8336028, baseEnd_8336028] using wordTrace_append hprefix tailTrace_8336028
  have hstable : (prefixWord ++ tailWord_8336028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336028).length < 2 ^ (prefixWord ++ tailWord_8336028).sum := by decide
  have hdescent : baseEnd_8336028 < baseStart_8336028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336032 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3]
def baseStart_8336032 : Nat := 118140960795 + 8336032 * 2 ^ 59
def prefixEnd_8336032 : Nat := 4983230072969 + 3 ^ 40 * 8336032 * 2
def baseEnd_8336032 : Nat := 4280391167260434470163293

theorem tailTrace_8336032 : CollatzResearch.WordTrace tailWord_8336032 prefixEnd_8336032 4280391167260434470163293 := by
  unfold tailWord_8336032
  simp only [CollatzResearch.WordTrace]
  refine ⟨152020032467993609882841175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202693376623991479843788233 152020032467993609882841175)
  ·
    refine ⟨228030048701990414824261763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152020032467993609882841175 228030048701990414824261763)
    ·
      refine ⟨342045073052985622236392645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228030048701990414824261763 342045073052985622236392645)
      ·
        refine ⟨64133451197434804169323621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342045073052985622236392645 64133451197434804169323621)
        ·
          refine ⟨12025022099519025781748179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64133451197434804169323621 12025022099519025781748179)
          ·
            refine ⟨18037533149278538672622269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025022099519025781748179 18037533149278538672622269)
            ·
              refine ⟨6764074930979452002233351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18037533149278538672622269 6764074930979452002233351)
              ·
                refine ⟨10146112396469178003350027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764074930979452002233351 10146112396469178003350027)
                ·
                  refine ⟨15219168594703767005025041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146112396469178003350027 15219168594703767005025041)
                  ·
                    refine ⟨11414376446027825253768781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15219168594703767005025041 11414376446027825253768781)
                    ·
                      refine ⟨4280391167260434470163293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414376446027825253768781 4280391167260434470163293)
                      ·
                        rfl

theorem cell23_8336032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_8336032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336032 prefixEnd_8336032 := by exact prefixLift 8336032
  have htrace : WordTrace (prefixWord ++ tailWord_8336032) baseStart_8336032 baseEnd_8336032 := by
    simpa [prefixWord, tailWord_8336032, baseEnd_8336032] using wordTrace_append hprefix tailTrace_8336032
  have hstable : (prefixWord ++ tailWord_8336032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336032).length < 2 ^ (prefixWord ++ tailWord_8336032).sum := by decide
  have hdescent : baseEnd_8336032 < baseStart_8336032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336046 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8336046 : Nat := 118140960795 + 8336046 * 2 ^ 59
def prefixEnd_8336046 : Nat := 4983230072969 + 3 ^ 40 * 8336046 * 2
def baseEnd_8336046 : Nat := 4280398355989597415388229

theorem tailTrace_8336046 : CollatzResearch.WordTrace tailWord_8336046 prefixEnd_8336046 4280398355989597415388229 := by
  unfold tailWord_8336046
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005071944742062519586499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202693717038624333437794661 38005071944742062519586499)
  ·
    refine ⟨57007607917113093779379749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38005071944742062519586499 57007607917113093779379749)
    ·
      refine ⟨10688926484458705083633703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57007607917113093779379749 10688926484458705083633703)
      ·
        refine ⟨16033389726688057625450555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688926484458705083633703 16033389726688057625450555)
        ·
          refine ⟨24050084590032086438175833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16033389726688057625450555 24050084590032086438175833)
          ·
            refine ⟨18037563442524064828631875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24050084590032086438175833 18037563442524064828631875)
            ·
              refine ⟨27056345163786097242947813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18037563442524064828631875 27056345163786097242947813)
              ·
                refine ⟨5073064718209893233052715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27056345163786097242947813 5073064718209893233052715)
                ·
                  refine ⟨7609597077314839849579073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073064718209893233052715 7609597077314839849579073)
                  ·
                    refine ⟨5707197807986129887184305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609597077314839849579073 5707197807986129887184305)
                    ·
                      refine ⟨4280398355989597415388229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707197807986129887184305 4280398355989597415388229)
                      ·
                        rfl

theorem cell23_8336046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8336046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336046 prefixEnd_8336046 := by exact prefixLift 8336046
  have htrace : WordTrace (prefixWord ++ tailWord_8336046) baseStart_8336046 baseEnd_8336046 := by
    simpa [prefixWord, tailWord_8336046, baseEnd_8336046] using wordTrace_append hprefix tailTrace_8336046
  have hstable : (prefixWord ++ tailWord_8336046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336046).length < 2 ^ (prefixWord ++ tailWord_8336046).sum := by decide
  have hdescent : baseEnd_8336046 < baseStart_8336046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336051 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_8336051 : Nat := 118140960795 + 8336051 * 2 ^ 59
def prefixEnd_8336051 : Nat := 4983230072969 + 3 ^ 40 * 8336051 * 2
def baseEnd_8336051 : Nat := 4280400923392869895825705

theorem tailTrace_8336051 : CollatzResearch.WordTrace tailWord_8336051 prefixEnd_8336051 4280400923392869895825705 := by
  unfold tailWord_8336051
  simp only [CollatzResearch.WordTrace]
  refine ⟨304040757922918386010624007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202693838615278924007082671 304040757922918386010624007)
  ·
    refine ⟨456061136884377579015936011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304040757922918386010624007 456061136884377579015936011)
    ·
      refine ⟨684091705326566368523904017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456061136884377579015936011 684091705326566368523904017)
      ·
        refine ⟨513068778994924776392928013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684091705326566368523904017 513068778994924776392928013)
        ·
          refine ⟨192400792123096791147348005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513068778994924776392928013 192400792123096791147348005)
          ·
            refine ⟨36075148523080648340127751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192400792123096791147348005 36075148523080648340127751)
            ·
              refine ⟨54112722784620972510191627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36075148523080648340127751 54112722784620972510191627)
              ·
                refine ⟨81169084176931458765287441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54112722784620972510191627 81169084176931458765287441)
                ·
                  refine ⟨60876813132698594073965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81169084176931458765287441 60876813132698594073965581)
                  ·
                    refine ⟨22828804924761972777737093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60876813132698594073965581 22828804924761972777737093)
                    ·
                      refine ⟨4280400923392869895825705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22828804924761972777737093 4280400923392869895825705)
                      ·
                        rfl

theorem cell23_8336051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_8336051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336051 prefixEnd_8336051 := by exact prefixLift 8336051
  have htrace : WordTrace (prefixWord ++ tailWord_8336051) baseStart_8336051 baseEnd_8336051 := by
    simpa [prefixWord, tailWord_8336051, baseEnd_8336051] using wordTrace_append hprefix tailTrace_8336051
  have hstable : (prefixWord ++ tailWord_8336051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336051).length < 2 ^ (prefixWord ++ tailWord_8336051).sum := by decide
  have hdescent : baseEnd_8336051 < baseStart_8336051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336061 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_8336061 : Nat := 118140960795 + 8336061 * 2 ^ 59
def prefixEnd_8336061 : Nat := 4983230072969 + 3 ^ 40 * 8336061 * 2
def baseEnd_8336061 : Nat := 1426802019399804952233553

theorem tailTrace_8336061 : CollatzResearch.WordTrace tailWord_8336061 prefixEnd_8336061 1426802019399804952233553 := by
  unfold tailWord_8336061
  simp only [CollatzResearch.WordTrace]
  refine ⟨304041122652882157718488037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202694081768588105145658691 304041122652882157718488037)
  ·
    refine ⟨57007710497415404572216507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304041122652882157718488037 57007710497415404572216507)
    ·
      refine ⟨85511565746123106858324761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57007710497415404572216507 85511565746123106858324761)
      ·
        refine ⟨64133674309592330143743571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85511565746123106858324761 64133674309592330143743571)
        ·
          refine ⟨96200511464388495215615357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64133674309592330143743571 96200511464388495215615357)
          ·
            refine ⟨36075191799145685705855759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96200511464388495215615357 36075191799145685705855759)
            ·
              refine ⟨54112787698718528558783639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36075191799145685705855759 54112787698718528558783639)
              ·
                refine ⟨81169181548077792838175459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54112787698718528558783639 81169181548077792838175459)
                ·
                  refine ⟨121753772322116689257263189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81169181548077792838175459 121753772322116689257263189)
                  ·
                    refine ⟨1426802019399804952233553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121753772322116689257263189 1426802019399804952233553)
                    ·
                      rfl

theorem cell23_8336061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_8336061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336061 prefixEnd_8336061 := by exact prefixLift 8336061
  have htrace : WordTrace (prefixWord ++ tailWord_8336061) baseStart_8336061 baseEnd_8336061 := by
    simpa [prefixWord, tailWord_8336061, baseEnd_8336061] using wordTrace_append hprefix tailTrace_8336061
  have hstable : (prefixWord ++ tailWord_8336061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336061).length < 2 ^ (prefixWord ++ tailWord_8336061).sum := by decide
  have hdescent : baseEnd_8336061 < baseStart_8336061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336071 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_8336071 : Nat := 118140960795 + 8336071 * 2 ^ 59
def prefixEnd_8336071 : Nat := 4983230072969 + 3 ^ 40 * 8336071 * 2
def baseEnd_8336071 : Nat := 4280411193005959817575613

theorem tailTrace_8336071 : CollatzResearch.WordTrace tailWord_8336071 prefixEnd_8336071 4280411193005959817575613 := by
  unfold tailWord_8336071
  simp only [CollatzResearch.WordTrace]
  refine ⟨304041487382845929426352067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202694324921897286284234711 304041487382845929426352067)
  ·
    refine ⟨456062231074268894139528101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304041487382845929426352067 456062231074268894139528101)
    ·
      refine ⟨85511668326425417651161519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456062231074268894139528101 85511668326425417651161519)
      ·
        refine ⟨128267502489638126476742279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85511668326425417651161519 128267502489638126476742279)
        ·
          refine ⟨192401253734457189715113419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128267502489638126476742279 192401253734457189715113419)
          ·
            refine ⟨288601880601685784572670129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192401253734457189715113419 288601880601685784572670129)
            ·
              refine ⟨216451410451264338429502597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288601880601685784572670129 216451410451264338429502597)
              ·
                refine ⟨40584639459612063455531737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216451410451264338429502597 40584639459612063455531737)
                ·
                  refine ⟨30438479594709047591648803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40584639459612063455531737 30438479594709047591648803)
                  ·
                    refine ⟨45657719392063571387473205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30438479594709047591648803 45657719392063571387473205)
                    ·
                      refine ⟨4280411193005959817575613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45657719392063571387473205 4280411193005959817575613)
                      ·
                        rfl

theorem cell23_8336071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_8336071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336071 prefixEnd_8336071 := by exact prefixLift 8336071
  have htrace : WordTrace (prefixWord ++ tailWord_8336071) baseStart_8336071 baseEnd_8336071 := by
    simpa [prefixWord, tailWord_8336071, baseEnd_8336071] using wordTrace_append hprefix tailTrace_8336071
  have hstable : (prefixWord ++ tailWord_8336071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336071).length < 2 ^ (prefixWord ++ tailWord_8336071).sum := by decide
  have hdescent : baseEnd_8336071 < baseStart_8336071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336081 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_8336081 : Nat := 118140960795 + 8336081 * 2 ^ 59
def prefixEnd_8336081 : Nat := 4983230072969 + 3 ^ 40 * 8336081 * 2
def baseEnd_8336081 : Nat := 4280416327812504778450567

theorem tailTrace_8336081 : CollatzResearch.WordTrace tailWord_8336081 prefixEnd_8336081 4280416327812504778450567 := by
  unfold tailWord_8336081
  simp only [CollatzResearch.WordTrace]
  refine ⟨304041852112809701134216097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202694568075206467422810731 304041852112809701134216097)
  ·
    refine ⟨228031389084607275850662073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304041852112809701134216097 228031389084607275850662073)
    ·
      refine ⟨171023541813455456887996555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228031389084607275850662073 171023541813455456887996555)
      ·
        refine ⟨256535312720183185331994833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171023541813455456887996555 256535312720183185331994833)
        ·
          refine ⟨192401484540137388998996125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256535312720183185331994833 192401484540137388998996125)
          ·
            refine ⟨72150556702551520874623547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192401484540137388998996125 72150556702551520874623547)
            ·
              refine ⟨108225835053827281311935321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72150556702551520874623547 108225835053827281311935321)
              ·
                refine ⟨81169376290370460983951491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108225835053827281311935321 81169376290370460983951491)
                ·
                  refine ⟨121754064435555691475927237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81169376290370460983951491 121754064435555691475927237)
                  ·
                    refine ⟨22828887081666692151736357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121754064435555691475927237 22828887081666692151736357)
                    ·
                      refine ⟨4280416327812504778450567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22828887081666692151736357 4280416327812504778450567)
                      ·
                        rfl

theorem cell23_8336081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_8336081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336081 prefixEnd_8336081 := by exact prefixLift 8336081
  have htrace : WordTrace (prefixWord ++ tailWord_8336081) baseStart_8336081 baseEnd_8336081 := by
    simpa [prefixWord, tailWord_8336081, baseEnd_8336081] using wordTrace_append hprefix tailTrace_8336081
  have hstable : (prefixWord ++ tailWord_8336081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336081).length < 2 ^ (prefixWord ++ tailWord_8336081).sum := by decide
  have hdescent : baseEnd_8336081 < baseStart_8336081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336131 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_8336131 : Nat := 118140960795 + 8336131 * 2 ^ 59
def prefixEnd_8336131 : Nat := 4983230072969 + 3 ^ 40 * 8336131 * 2
def baseEnd_8336131 : Nat := 4280442001845229582825337

theorem tailTrace_8336131 : CollatzResearch.WordTrace tailWord_8336131 prefixEnd_8336131 4280442001845229582825337 := by
  unfold tailWord_8336131
  simp only [CollatzResearch.WordTrace]
  refine ⟨304043675762628559673536247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202695783841752373115690831 304043675762628559673536247)
  ·
    refine ⟨456065513643942839510304371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304043675762628559673536247 456065513643942839510304371)
    ·
      refine ⟨684098270465914259265456557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456065513643942839510304371 684098270465914259265456557)
      ·
        refine ⟨256536851424717847224546209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684098270465914259265456557 256536851424717847224546209)
        ·
          refine ⟨192402638568538385418409657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256536851424717847224546209 192402638568538385418409657)
          ·
            refine ⟨144301978926403789063807243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192402638568538385418409657 144301978926403789063807243)
            ·
              refine ⟨216452968389605683595710865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144301978926403789063807243 216452968389605683595710865)
              ·
                refine ⟨162339726292204262696783149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216452968389605683595710865 162339726292204262696783149)
                ·
                  refine ⟨60877397359576598511293681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162339726292204262696783149 60877397359576598511293681)
                  ·
                    refine ⟨45658048019682448883470261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60877397359576598511293681 45658048019682448883470261)
                    ·
                      refine ⟨4280442001845229582825337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45658048019682448883470261 4280442001845229582825337)
                      ·
                        rfl

theorem cell23_8336131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_8336131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336131 prefixEnd_8336131 := by exact prefixLift 8336131
  have htrace : WordTrace (prefixWord ++ tailWord_8336131) baseStart_8336131 baseEnd_8336131 := by
    simpa [prefixWord, tailWord_8336131, baseEnd_8336131] using wordTrace_append hprefix tailTrace_8336131
  have hstable : (prefixWord ++ tailWord_8336131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336131).length < 2 ^ (prefixWord ++ tailWord_8336131).sum := by decide
  have hdescent : baseEnd_8336131 < baseStart_8336131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336138 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_8336138 : Nat := 118140960795 + 8336138 * 2 ^ 59
def prefixEnd_8336138 : Nat := 4983230072969 + 3 ^ 40 * 8336138 * 2
def baseEnd_8336138 : Nat := 1426815198736603685145935

theorem tailTrace_8336138 : CollatzResearch.WordTrace tailWord_8336138 prefixEnd_8336138 1426815198736603685145935 := by
  unfold tailWord_8336138
  simp only [CollatzResearch.WordTrace]
  refine ⟨76010982768400799967260267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202695954049068799912694045 76010982768400799967260267)
  ·
    refine ⟨114016474152601199950890401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76010982768400799967260267 114016474152601199950890401)
    ·
      refine ⟨85512355614450899963167801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114016474152601199950890401 85512355614450899963167801)
      ·
        refine ⟨64134266710838174972375851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85512355614450899963167801 64134266710838174972375851)
        ·
          refine ⟨96201400066257262458563777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64134266710838174972375851 96201400066257262458563777)
          ·
            refine ⟨72151050049692946843922833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96201400066257262458563777 72151050049692946843922833)
            ·
              refine ⟨54113287537269710132942125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72151050049692946843922833 54113287537269710132942125)
              ·
                refine ⟨20292482826476141299853297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54113287537269710132942125 20292482826476141299853297)
                ·
                  refine ⟨15219362119857105974889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20292482826476141299853297 15219362119857105974889973)
                  ·
                    refine ⟨1426815198736603685145935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15219362119857105974889973 1426815198736603685145935)
                    ·
                      rfl

theorem cell23_8336138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_8336138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336138 prefixEnd_8336138 := by exact prefixLift 8336138
  have htrace : WordTrace (prefixWord ++ tailWord_8336138) baseStart_8336138 baseEnd_8336138 := by
    simpa [prefixWord, tailWord_8336138, baseEnd_8336138] using wordTrace_append hprefix tailTrace_8336138
  have hstable : (prefixWord ++ tailWord_8336138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336138).length < 2 ^ (prefixWord ++ tailWord_8336138).sum := by decide
  have hdescent : baseEnd_8336138 < baseStart_8336138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336170 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8336170 : Nat := 118140960795 + 8336170 * 2 ^ 59
def prefixEnd_8336170 : Nat := 4983230072969 + 3 ^ 40 * 8336170 * 2
def baseEnd_8336170 : Nat := 4280462027590754930237659

theorem tailTrace_8336170 : CollatzResearch.WordTrace tailWord_8336170 prefixEnd_8336170 4280462027590754930237659 := by
  unfold tailWord_8336170
  simp only [CollatzResearch.WordTrace]
  refine ⟨76011274552371817333551491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202696732139658179556137309 76011274552371817333551491)
  ·
    refine ⟨114016911828557726000327237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76011274552371817333551491 114016911828557726000327237)
    ·
      refine ⟨21378170967854573625061357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114016911828557726000327237 21378170967854573625061357)
      ·
        refine ⟨8016814112945465109398009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21378170967854573625061357 8016814112945465109398009)
        ·
          refine ⟨6012610584709098832048507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8016814112945465109398009 6012610584709098832048507)
          ·
            refine ⟨9018915877063648248072761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012610584709098832048507 9018915877063648248072761)
            ·
              refine ⟨6764186907797736186054571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018915877063648248072761 6764186907797736186054571)
              ·
                refine ⟨10146280361696604279081857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764186907797736186054571 10146280361696604279081857)
                ·
                  refine ⟨7609710271272453209311393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10146280361696604279081857 7609710271272453209311393)
                  ·
                    refine ⟨5707282703454339906983545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609710271272453209311393 5707282703454339906983545)
                    ·
                      refine ⟨4280462027590754930237659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707282703454339906983545 4280462027590754930237659)
                      ·
                        rfl

theorem cell23_8336170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8336170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336170 prefixEnd_8336170 := by exact prefixLift 8336170
  have htrace : WordTrace (prefixWord ++ tailWord_8336170) baseStart_8336170 baseEnd_8336170 := by
    simpa [prefixWord, tailWord_8336170, baseEnd_8336170] using wordTrace_append hprefix tailTrace_8336170
  have hstable : (prefixWord ++ tailWord_8336170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336170).length < 2 ^ (prefixWord ++ tailWord_8336170).sum := by decide
  have hdescent : baseEnd_8336170 < baseStart_8336170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336171 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_8336171 : Nat := 118140960795 + 8336171 * 2 ^ 59
def prefixEnd_8336171 : Nat := 4983230072969 + 3 ^ 40 * 8336171 * 2
def baseEnd_8336171 : Nat := 4280462541071409426325153

theorem tailTrace_8336171 : CollatzResearch.WordTrace tailWord_8336171 prefixEnd_8336171 4280462541071409426325153 := by
  unfold tailWord_8336171
  simp only [CollatzResearch.WordTrace]
  refine ⟨304045134682483646504992367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202696756454989097669994911 304045134682483646504992367)
  ·
    refine ⟨456067702023725469757488551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304045134682483646504992367 456067702023725469757488551)
    ·
      refine ⟨684101553035588204636232827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456067702023725469757488551 684101553035588204636232827)
      ·
        refine ⟨1026152329553382306954349241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684101553035588204636232827 1026152329553382306954349241)
        ·
          refine ⟨769614247165036730215761931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026152329553382306954349241 769614247165036730215761931)
          ·
            refine ⟨1154421370747555095323642897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769614247165036730215761931 1154421370747555095323642897)
            ·
              refine ⟨865816028060666321492732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154421370747555095323642897 865816028060666321492732173)
              ·
                refine ⟨324681010522749870559774565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865816028060666321492732173 324681010522749870559774565)
                ·
                  refine ⟨60877689473015600729957731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324681010522749870559774565 60877689473015600729957731)
                  ·
                    refine ⟨91316534209523401094936597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60877689473015600729957731 91316534209523401094936597)
                    ·
                      refine ⟨4280462541071409426325153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91316534209523401094936597 4280462541071409426325153)
                      ·
                        rfl

theorem cell23_8336171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_8336171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336171 prefixEnd_8336171 := by exact prefixLift 8336171
  have htrace : WordTrace (prefixWord ++ tailWord_8336171) baseStart_8336171 baseEnd_8336171 := by
    simpa [prefixWord, tailWord_8336171, baseEnd_8336171] using wordTrace_append hprefix tailTrace_8336171
  have hstable : (prefixWord ++ tailWord_8336171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336171).length < 2 ^ (prefixWord ++ tailWord_8336171).sum := by decide
  have hdescent : baseEnd_8336171 < baseStart_8336171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336195 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3]
def baseStart_8336195 : Nat := 118140960795 + 8336195 * 2 ^ 59
def prefixEnd_8336195 : Nat := 4983230072969 + 3 ^ 40 * 8336195 * 2
def baseEnd_8336195 : Nat := 4280474864607117332425043

theorem tailTrace_8336195 : CollatzResearch.WordTrace tailWord_8336195 prefixEnd_8336195 4280474864607117332425043 := by
  unfold tailWord_8336195
  simp only [CollatzResearch.WordTrace]
  refine ⟨304046010034396698603866039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202697340022931132402577359 304046010034396698603866039)
  ·
    refine ⟨456069015051595047905799059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304046010034396698603866039 456069015051595047905799059)
    ·
      refine ⟨684103522577392571858698589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456069015051595047905799059 684103522577392571858698589)
      ·
        refine ⟨256538820966522214447011971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684103522577392571858698589 256538820966522214447011971)
        ·
          refine ⟨384808231449783321670517957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256538820966522214447011971 384808231449783321670517957)
          ·
            refine ⟨72151543396834372813222117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384808231449783321670517957 72151543396834372813222117)
            ·
              refine ⟨13528414386906444902479147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72151543396834372813222117 13528414386906444902479147)
              ·
                refine ⟨20292621580359667353718721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13528414386906444902479147 20292621580359667353718721)
                ·
                  refine ⟨15219466185269750515289041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20292621580359667353718721 15219466185269750515289041)
                  ·
                    refine ⟨11414599638952312886466781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15219466185269750515289041 11414599638952312886466781)
                    ·
                      refine ⟨4280474864607117332425043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414599638952312886466781 4280474864607117332425043)
                      ·
                        rfl

theorem cell23_8336195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_8336195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336195 prefixEnd_8336195 := by exact prefixLift 8336195
  have htrace : WordTrace (prefixWord ++ tailWord_8336195) baseStart_8336195 baseEnd_8336195 := by
    simpa [prefixWord, tailWord_8336195, baseEnd_8336195] using wordTrace_append hprefix tailTrace_8336195
  have hstable : (prefixWord ++ tailWord_8336195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336195).length < 2 ^ (prefixWord ++ tailWord_8336195).sum := by decide
  have hdescent : baseEnd_8336195 < baseStart_8336195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336215 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 6]
def baseStart_8336215 : Nat := 118140960795 + 8336215 * 2 ^ 59
def prefixEnd_8336215 : Nat := 4983230072969 + 3 ^ 40 * 8336215 * 2
def baseEnd_8336215 : Nat := 475609459357800806019439

theorem tailTrace_8336215 : CollatzResearch.WordTrace tailWord_8336215 prefixEnd_8336215 475609459357800806019439 := by
  unfold tailWord_8336215
  simp only [CollatzResearch.WordTrace]
  refine ⟨304046739494324242019594099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202697826329549494679729399 304046739494324242019594099)
  ·
    refine ⟨456070109241486363029391149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304046739494324242019594099 456070109241486363029391149)
    ·
      refine ⟨171026290965557386136021681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456070109241486363029391149 171026290965557386136021681)
      ·
        refine ⟨128269718224168039602016261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171026290965557386136021681 128269718224168039602016261)
        ·
          refine ⟨24050572167031507425378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128269718224168039602016261 24050572167031507425378049)
          ·
            refine ⟨18037929125273630569033537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24050572167031507425378049 18037929125273630569033537)
            ·
              refine ⟨13528446843955222926775153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18037929125273630569033537 13528446843955222926775153)
              ·
                refine ⟨10146335132966417195081365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13528446843955222926775153 10146335132966417195081365)
                ·
                  refine ⟨475609459357800806019439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10146335132966417195081365 475609459357800806019439)
                  ·
                    rfl

theorem cell23_8336215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 6].length) (baseStart_8336215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336215 prefixEnd_8336215 := by exact prefixLift 8336215
  have htrace : WordTrace (prefixWord ++ tailWord_8336215) baseStart_8336215 baseEnd_8336215 := by
    simpa [prefixWord, tailWord_8336215, baseEnd_8336215] using wordTrace_append hprefix tailTrace_8336215
  have hstable : (prefixWord ++ tailWord_8336215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336215).length < 2 ^ (prefixWord ++ tailWord_8336215).sum := by decide
  have hdescent : baseEnd_8336215 < baseStart_8336215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336235 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 4, 3, 2]
def baseStart_8336235 : Nat := 118140960795 + 8336235 * 2 ^ 59
def prefixEnd_8336235 : Nat := 4983230072969 + 3 ^ 40 * 8336235 * 2
def baseEnd_8336235 : Nat := 4280495403833297175924859

theorem tailTrace_8336235 : CollatzResearch.WordTrace tailWord_8336235 prefixEnd_8336235 4280495403833297175924859 := by
  unfold tailWord_8336235
  simp only [CollatzResearch.WordTrace]
  refine ⟨304047468954251785435322159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202698312636167856956881439 304047468954251785435322159)
  ·
    refine ⟨456071203431377678152983239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304047468954251785435322159 456071203431377678152983239)
    ·
      refine ⟨684106805147066517229474859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456071203431377678152983239 684106805147066517229474859)
      ·
        refine ⟨1026160207720599775844212289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684106805147066517229474859 1026160207720599775844212289)
        ·
          refine ⟨769620155790449831883159217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026160207720599775844212289 769620155790449831883159217)
          ·
            refine ⟨577215116842837373912369413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769620155790449831883159217 577215116842837373912369413)
            ·
              refine ⟨108227834408032007608569265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577215116842837373912369413 108227834408032007608569265)
              ·
                refine ⟨81170875806024005706426949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108227834408032007608569265 81170875806024005706426949)
                ·
                  refine ⟨15219539213629501069955053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81170875806024005706426949 15219539213629501069955053)
                  ·
                    refine ⟨5707327205111062901233145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15219539213629501069955053 5707327205111062901233145)
                    ·
                      refine ⟨4280495403833297175924859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707327205111062901233145 4280495403833297175924859)
                      ·
                        rfl

theorem cell23_8336235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3, 2].length) (baseStart_8336235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336235 prefixEnd_8336235 := by exact prefixLift 8336235
  have htrace : WordTrace (prefixWord ++ tailWord_8336235) baseStart_8336235 baseEnd_8336235 := by
    simpa [prefixWord, tailWord_8336235, baseEnd_8336235] using wordTrace_append hprefix tailTrace_8336235
  have hstable : (prefixWord ++ tailWord_8336235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336235).length < 2 ^ (prefixWord ++ tailWord_8336235).sum := by decide
  have hdescent : baseEnd_8336235 < baseStart_8336235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336245 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8336245 : Nat := 118140960795 + 8336245 * 2 ^ 59
def prefixEnd_8336245 : Nat := 4983230072969 + 3 ^ 40 * 8336245 * 2
def baseEnd_8336245 : Nat := 1426833512879947378933271

theorem tailTrace_8336245 : CollatzResearch.WordTrace tailWord_8336245 prefixEnd_8336245 1426833512879947378933271 := by
  unfold tailWord_8336245
  simp only [CollatzResearch.WordTrace]
  refine ⟨304047833684215557143186189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202698555789477038095457459 304047833684215557143186189)
  ·
    refine ⟨114017937631580833928694821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304047833684215557143186189 114017937631580833928694821)
    ·
      refine ⟨21378363305921406361630279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114017937631580833928694821 21378363305921406361630279)
      ·
        refine ⟨32067544958882109542445419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21378363305921406361630279 32067544958882109542445419)
        ·
          refine ⟨48101317438323164313668129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32067544958882109542445419 48101317438323164313668129)
          ·
            refine ⟨36075988078742373235251097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48101317438323164313668129 36075988078742373235251097)
            ·
              refine ⟨27056991059056779926438323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36075988078742373235251097 27056991059056779926438323)
              ·
                refine ⟨40585486588585169889657485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27056991059056779926438323 40585486588585169889657485)
                ·
                  refine ⟨15219557470719438708621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40585486588585169889657485 15219557470719438708621557)
                  ·
                    refine ⟨1426833512879947378933271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15219557470719438708621557 1426833512879947378933271)
                    ·
                      rfl

theorem cell23_8336245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8336245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336245 prefixEnd_8336245 := by exact prefixLift 8336245
  have htrace : WordTrace (prefixWord ++ tailWord_8336245) baseStart_8336245 baseEnd_8336245 := by
    simpa [prefixWord, tailWord_8336245, baseEnd_8336245] using wordTrace_append hprefix tailTrace_8336245
  have hstable : (prefixWord ++ tailWord_8336245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336245).length < 2 ^ (prefixWord ++ tailWord_8336245).sum := by decide
  have hdescent : baseEnd_8336245 < baseStart_8336245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336259 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 1, 1, 3]
def baseStart_8336259 : Nat := 118140960795 + 8336259 * 2 ^ 59
def prefixEnd_8336259 : Nat := 4983230072969 + 3 ^ 40 * 8336259 * 2
def baseEnd_8336259 : Nat := 4280507727369005082024749

theorem tailTrace_8336259 : CollatzResearch.WordTrace tailWord_8336259 prefixEnd_8336259 4280507727369005082024749 := by
  unfold tailWord_8336259
  simp only [CollatzResearch.WordTrace]
  refine ⟨304048344306164837534195831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202698896204109891689463887 304048344306164837534195831)
  ·
    refine ⟨456072516459247256301293747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304048344306164837534195831 456072516459247256301293747)
    ·
      refine ⟨684108774688870884451940621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456072516459247256301293747 684108774688870884451940621)
      ·
        refine ⟨256540790508326581669477733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684108774688870884451940621 256540790508326581669477733)
        ·
          refine ⟨48101398220311234063027075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256540790508326581669477733 48101398220311234063027075)
          ·
            refine ⟨72152097330466851094540613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48101398220311234063027075 72152097330466851094540613)
            ·
              refine ⟨13528518249462534580226365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72152097330466851094540613 13528518249462534580226365)
              ·
                refine ⟨5073194343548450467584887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13528518249462534580226365 5073194343548450467584887)
                ·
                  refine ⟨7609791515322675701377331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073194343548450467584887 7609791515322675701377331)
                  ·
                    refine ⟨11414687272984013552065997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609791515322675701377331 11414687272984013552065997)
                    ·
                      refine ⟨4280507727369005082024749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414687272984013552065997 4280507727369005082024749)
                      ·
                        rfl

theorem cell23_8336259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_8336259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336259 prefixEnd_8336259 := by exact prefixLift 8336259
  have htrace : WordTrace (prefixWord ++ tailWord_8336259) baseStart_8336259 baseEnd_8336259 := by
    simpa [prefixWord, tailWord_8336259, baseEnd_8336259] using wordTrace_append hprefix tailTrace_8336259
  have hstable : (prefixWord ++ tailWord_8336259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336259).length < 2 ^ (prefixWord ++ tailWord_8336259).sum := by decide
  have hdescent : baseEnd_8336259 < baseStart_8336259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336275 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 2, 4]
def baseStart_8336275 : Nat := 118140960795 + 8336275 * 2 ^ 59
def prefixEnd_8336275 : Nat := 4983230072969 + 3 ^ 40 * 8336275 * 2
def baseEnd_8336275 : Nat := 1426838647686492339808225

theorem tailTrace_8336275 : CollatzResearch.WordTrace tailWord_8336275 prefixEnd_8336275 1426838647686492339808225 := by
  unfold tailWord_8336275
  simp only [CollatzResearch.WordTrace]
  refine ⟨304048927874106872266778279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202699285249404581511185519 304048927874106872266778279)
  ·
    refine ⟨456073391811160308400167419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304048927874106872266778279 456073391811160308400167419)
    ·
      refine ⟨684110087716740462600251129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456073391811160308400167419 684110087716740462600251129)
      ·
        refine ⟨513082565787555346950188347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684110087716740462600251129 513082565787555346950188347)
        ·
          refine ⟨769623848681333020425282521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513082565787555346950188347 769623848681333020425282521)
          ·
            refine ⟨577217886510999765318961891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769623848681333020425282521 577217886510999765318961891)
            ·
              refine ⟨865826829766499647978442837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577217886510999765318961891 865826829766499647978442837)
              ·
                refine ⟨10146408161326167749747377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 865826829766499647978442837 10146408161326167749747377)
                ·
                  refine ⟨7609806120994625812310533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10146408161326167749747377 7609806120994625812310533)
                  ·
                    refine ⟨1426838647686492339808225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609806120994625812310533 1426838647686492339808225)
                    ·
                      rfl

theorem cell23_8336275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 4].length) (baseStart_8336275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336275 prefixEnd_8336275 := by exact prefixLift 8336275
  have htrace : WordTrace (prefixWord ++ tailWord_8336275) baseStart_8336275 baseEnd_8336275 := by
    simpa [prefixWord, tailWord_8336275, baseEnd_8336275] using wordTrace_append hprefix tailTrace_8336275
  have hstable : (prefixWord ++ tailWord_8336275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336275).length < 2 ^ (prefixWord ++ tailWord_8336275).sum := by decide
  have hdescent : baseEnd_8336275 < baseStart_8336275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336285 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_8336285 : Nat := 118140960795 + 8336285 * 2 ^ 59
def prefixEnd_8336285 : Nat := 4983230072969 + 3 ^ 40 * 8336285 * 2
def baseEnd_8336285 : Nat := 4280521077866021980299629

theorem tailTrace_8336285 : CollatzResearch.WordTrace tailWord_8336285 prefixEnd_8336285 4280521077866021980299629 := by
  unfold tailWord_8336285
  simp only [CollatzResearch.WordTrace]
  refine ⟨304049292604070643974642309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202699528402713762649761539 304049292604070643974642309)
  ·
    refine ⟨57009242363263245745245433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304049292604070643974642309 57009242363263245745245433)
    ·
      refine ⟨42756931772447434308934075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57009242363263245745245433 42756931772447434308934075)
      ·
        refine ⟨64135397658671151463401113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42756931772447434308934075 64135397658671151463401113)
        ·
          refine ⟨48101548244003363597550835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64135397658671151463401113 48101548244003363597550835)
          ·
            refine ⟨72152322366005045396326253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48101548244003363597550835 72152322366005045396326253)
            ·
              refine ⟨27057120887251892023622345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72152322366005045396326253 27057120887251892023622345)
              ·
                refine ⟨20292840665438919017716759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27057120887251892023622345 20292840665438919017716759)
                ·
                  refine ⟨30439260998158378526575139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20292840665438919017716759 30439260998158378526575139)
                  ·
                    refine ⟨45658891497237567789862709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30439260998158378526575139 45658891497237567789862709)
                    ·
                      refine ⟨4280521077866021980299629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45658891497237567789862709 4280521077866021980299629)
                      ·
                        rfl

theorem cell23_8336285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_8336285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336285 prefixEnd_8336285 := by exact prefixLift 8336285
  have htrace : WordTrace (prefixWord ++ tailWord_8336285) baseStart_8336285 baseEnd_8336285 := by
    simpa [prefixWord, tailWord_8336285, baseEnd_8336285] using wordTrace_append hprefix tailTrace_8336285
  have hstable : (prefixWord ++ tailWord_8336285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336285).length < 2 ^ (prefixWord ++ tailWord_8336285).sum := by decide
  have hdescent : baseEnd_8336285 < baseStart_8336285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336305 : List Nat := [1, 2, 2, 4, 3, 1, 1, 9]
def baseStart_8336305 : Nat := 118140960795 + 8336305 * 2 ^ 59
def prefixEnd_8336305 : Nat := 4983230072969 + 3 ^ 40 * 8336305 * 2
def baseEnd_8336305 : Nat := 158538198054781922298131

theorem tailTrace_8336305 : CollatzResearch.WordTrace tailWord_8336305 prefixEnd_8336305 158538198054781922298131 := by
  unfold tailWord_8336305
  simp only [CollatzResearch.WordTrace]
  refine ⟨304050022063998187390370369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202700014709332124926913579 304050022063998187390370369)
  ·
    refine ⟨228037516547998640542777777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304050022063998187390370369 228037516547998640542777777)
    ·
      refine ⟨171028137410998980407083333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228037516547998640542777777 171028137410998980407083333)
      ·
        refine ⟨32067775764562308826328125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171028137410998980407083333 32067775764562308826328125)
        ·
          refine ⟨12025415911710865809873047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32067775764562308826328125 12025415911710865809873047)
          ·
            refine ⟨18038123867566298714809571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025415911710865809873047 18038123867566298714809571)
            ·
              refine ⟨27057185801349448072214357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18038123867566298714809571 27057185801349448072214357)
              ·
                refine ⟨158538198054781922298131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27057185801349448072214357 158538198054781922298131)
                ·
                  rfl

theorem cell23_8336305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 9].length) (baseStart_8336305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336305 prefixEnd_8336305 := by exact prefixLift 8336305
  have htrace : WordTrace (prefixWord ++ tailWord_8336305) baseStart_8336305 baseEnd_8336305 := by
    simpa [prefixWord, tailWord_8336305, baseEnd_8336305] using wordTrace_append hprefix tailTrace_8336305
  have hstable : (prefixWord ++ tailWord_8336305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336305).length < 2 ^ (prefixWord ++ tailWord_8336305).sum := by decide
  have hdescent : baseEnd_8336305 < baseStart_8336305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336325 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_8336325 : Nat := 118140960795 + 8336325 * 2 ^ 59
def prefixEnd_8336325 : Nat := 4983230072969 + 3 ^ 40 * 8336325 * 2
def baseEnd_8336325 : Nat := 4280541617092201823799445

theorem tailTrace_8336325 : CollatzResearch.WordTrace tailWord_8336325 prefixEnd_8336325 4280541617092201823799445 := by
  unfold tailWord_8336325
  simp only [CollatzResearch.WordTrace]
  refine ⟨304050751523925730806098429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202700501015950487204065619 304050751523925730806098429)
  ·
    refine ⟨114019031821472149052286911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304050751523925730806098429 114019031821472149052286911)
    ·
      refine ⟨171028547732208223578430367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114019031821472149052286911 171028547732208223578430367)
      ·
        refine ⟨256542821598312335367645551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171028547732208223578430367 256542821598312335367645551)
        ·
          refine ⟨384814232397468503051468327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256542821598312335367645551 384814232397468503051468327)
          ·
            refine ⟨577221348596202754577202491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384814232397468503051468327 577221348596202754577202491)
            ·
              refine ⟨865832022894304131865803737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577221348596202754577202491 865832022894304131865803737)
              ·
                refine ⟨649374017170728098899352803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865832022894304131865803737 649374017170728098899352803)
                ·
                  refine ⟨974061025756092148349029205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649374017170728098899352803 974061025756092148349029205)
                  ·
                    refine ⟨5707388822789602431732593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 974061025756092148349029205 5707388822789602431732593)
                    ·
                      refine ⟨4280541617092201823799445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707388822789602431732593 4280541617092201823799445)
                      ·
                        rfl

theorem cell23_8336325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_8336325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336325 prefixEnd_8336325 := by exact prefixLift 8336325
  have htrace : WordTrace (prefixWord ++ tailWord_8336325) baseStart_8336325 baseEnd_8336325 := by
    simpa [prefixWord, tailWord_8336325, baseEnd_8336325] using wordTrace_append hprefix tailTrace_8336325
  have hstable : (prefixWord ++ tailWord_8336325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336325).length < 2 ^ (prefixWord ++ tailWord_8336325).sum := by decide
  have hdescent : baseEnd_8336325 < baseStart_8336325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336332 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_8336332 : Nat := 118140960795 + 8336332 * 2 ^ 59
def prefixEnd_8336332 : Nat := 4983230072969 + 3 ^ 40 * 8336332 * 2
def baseEnd_8336332 : Nat := 4280545211456783296411913

theorem tailTrace_8336332 : CollatzResearch.WordTrace tailWord_8336332 prefixEnd_8336332 4280545211456783296411913 := by
  unfold tailWord_8336332
  simp only [CollatzResearch.WordTrace]
  refine ⟨152025503417450185500801625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202700671223266914001068833 152025503417450185500801625)
  ·
    refine ⟨114019127563087639125601219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152025503417450185500801625 114019127563087639125601219)
    ·
      refine ⟨171028691344631458688401829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114019127563087639125601219 171028691344631458688401829)
      ·
        refine ⟨32067879627118398504075343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171028691344631458688401829 32067879627118398504075343)
        ·
          refine ⟨48101819440677597756113015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32067879627118398504075343 48101819440677597756113015)
          ·
            refine ⟨72152729161016396634169523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48101819440677597756113015 72152729161016396634169523)
            ·
              refine ⟨108229093741524594951254285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72152729161016396634169523 108229093741524594951254285)
              ·
                refine ⟨40585910153071723106720357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108229093741524594951254285 40585910153071723106720357)
                ·
                  refine ⟨7609858153700948082510067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40585910153071723106720357 7609858153700948082510067)
                  ·
                    refine ⟨11414787230551422123765101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609858153700948082510067 11414787230551422123765101)
                    ·
                      refine ⟨4280545211456783296411913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11414787230551422123765101 4280545211456783296411913)
                      ·
                        rfl

theorem cell23_8336332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_8336332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336332 prefixEnd_8336332 := by exact prefixLift 8336332
  have htrace : WordTrace (prefixWord ++ tailWord_8336332) baseStart_8336332 baseEnd_8336332 := by
    simpa [prefixWord, tailWord_8336332, baseEnd_8336332] using wordTrace_append hprefix tailTrace_8336332
  have hstable : (prefixWord ++ tailWord_8336332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336332).length < 2 ^ (prefixWord ++ tailWord_8336332).sum := by decide
  have hdescent : baseEnd_8336332 < baseStart_8336332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336359 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_8336359 : Nat := 118140960795 + 8336359 * 2 ^ 59
def prefixEnd_8336359 : Nat := 4983230072969 + 3 ^ 40 * 8336359 * 2
def baseEnd_8336359 : Nat := 4280559075434454690774289

theorem tailTrace_8336359 : CollatzResearch.WordTrace tailWord_8336359 prefixEnd_8336359 4280559075434454690774289 := by
  unfold tailWord_8336359
  simp only [CollatzResearch.WordTrace]
  refine ⟨304051991605802554612836131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202701327737201703075224087 304051991605802554612836131)
  ·
    refine ⟨456077987408703831919254197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304051991605802554612836131 456077987408703831919254197)
    ·
      refine ⟨42757311319565984242430081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456077987408703831919254197 42757311319565984242430081)
      ·
        refine ⟨32067983489674488181822561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42757311319565984242430081 32067983489674488181822561)
        ·
          refine ⟨24050987617255866136366921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32067983489674488181822561 24050987617255866136366921)
          ·
            refine ⟨18038240712941899602275191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24050987617255866136366921 18038240712941899602275191)
            ·
              refine ⟨27057361069412849403412787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18038240712941899602275191 27057361069412849403412787)
              ·
                refine ⟨40586041604119274105119181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27057361069412849403412787 40586041604119274105119181)
                ·
                  refine ⟨15219765601544727789419693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40586041604119274105119181 15219765601544727789419693)
                  ·
                    refine ⟨5707412100579272921032385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15219765601544727789419693 5707412100579272921032385)
                    ·
                      refine ⟨4280559075434454690774289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707412100579272921032385 4280559075434454690774289)
                      ·
                        rfl

theorem cell23_8336359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_8336359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336359 prefixEnd_8336359 := by exact prefixLift 8336359
  have htrace : WordTrace (prefixWord ++ tailWord_8336359) baseStart_8336359 baseEnd_8336359 := by
    simpa [prefixWord, tailWord_8336359, baseEnd_8336359] using wordTrace_append hprefix tailTrace_8336359
  have hstable : (prefixWord ++ tailWord_8336359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336359).length < 2 ^ (prefixWord ++ tailWord_8336359).sum := by decide
  have hdescent : baseEnd_8336359 < baseStart_8336359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336412 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 7]
def baseStart_8336412 : Nat := 118140960795 + 8336412 * 2 ^ 59
def prefixEnd_8336412 : Nat := 4983230072969 + 3 ^ 40 * 8336412 * 2
def baseEnd_8336412 : Nat := 475620698878793664823505

theorem tailTrace_8336412 : CollatzResearch.WordTrace tailWord_8336412 prefixEnd_8336412 475620698878793664823505 := by
  unfold tailWord_8336412
  simp only [CollatzResearch.WordTrace]
  refine ⟨152026962337305272332257745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202702616449740363109676993 152026962337305272332257745)
  ·
    refine ⟨114020221752978954249193309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152026962337305272332257745 114020221752978954249193309)
    ·
      refine ⟨42757583157367107843447491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114020221752978954249193309 42757583157367107843447491)
      ·
        refine ⟨64136374736050661765171237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42757583157367107843447491 64136374736050661765171237)
        ·
          refine ⟨12025570263009499080969607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64136374736050661765171237 12025570263009499080969607)
          ·
            refine ⟨18038355394514248621454411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025570263009499080969607 18038355394514248621454411)
            ·
              refine ⟨27057533091771372932181617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18038355394514248621454411 27057533091771372932181617)
              ·
                refine ⟨20293149818828529699136213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27057533091771372932181617 20293149818828529699136213)
                ·
                  refine ⟨475620698878793664823505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20293149818828529699136213 475620698878793664823505)
                  ·
                    rfl

theorem cell23_8336412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_8336412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336412 prefixEnd_8336412 := by exact prefixLift 8336412
  have htrace : WordTrace (prefixWord ++ tailWord_8336412) baseStart_8336412 baseEnd_8336412 := by
    simpa [prefixWord, tailWord_8336412, baseEnd_8336412] using wordTrace_append hprefix tailTrace_8336412
  have hstable : (prefixWord ++ tailWord_8336412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336412).length < 2 ^ (prefixWord ++ tailWord_8336412).sum := by decide
  have hdescent : baseEnd_8336412 < baseStart_8336412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336472 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_8336472 : Nat := 118140960795 + 8336472 * 2 ^ 59
def prefixEnd_8336472 : Nat := 4983230072969 + 3 ^ 40 * 8336472 * 2
def baseEnd_8336472 : Nat := 1426872366249470916220423

theorem tailTrace_8336472 : CollatzResearch.WordTrace tailWord_8336472 prefixEnd_8336472 1426872366249470916220423 := by
  unfold tailWord_8336472
  simp only [CollatzResearch.WordTrace]
  refine ⟨152028056527196587455849835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202704075369595449941133113 152028056527196587455849835)
  ·
    refine ⟨228042084790794881183774753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152028056527196587455849835 228042084790794881183774753)
    ·
      refine ⟨171031563593096160887831065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228042084790794881183774753 171031563593096160887831065)
      ·
        refine ⟨128273672694822120665873299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171031563593096160887831065 128273672694822120665873299)
        ·
          refine ⟨192410509042233180998809949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128273672694822120665873299 192410509042233180998809949)
          ·
            refine ⟨72153940890837442874553731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192410509042233180998809949 72153940890837442874553731)
            ·
              refine ⟨108230911336256164311830597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72153940890837442874553731 108230911336256164311830597)
              ·
                refine ⟨20293295875548030808468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108230911336256164311830597 20293295875548030808468237)
                ·
                  refine ⟨7609985953330511553175589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20293295875548030808468237 7609985953330511553175589)
                  ·
                    refine ⟨1426872366249470916220423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7609985953330511553175589 1426872366249470916220423)
                    ·
                      rfl

theorem cell23_8336472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_8336472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336472 prefixEnd_8336472 := by exact prefixLift 8336472
  have htrace : WordTrace (prefixWord ++ tailWord_8336472) baseStart_8336472 baseEnd_8336472 := by
    simpa [prefixWord, tailWord_8336472, baseEnd_8336472] using wordTrace_append hprefix tailTrace_8336472
  have hstable : (prefixWord ++ tailWord_8336472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336472).length < 2 ^ (prefixWord ++ tailWord_8336472).sum := by decide
  have hdescent : baseEnd_8336472 < baseStart_8336472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336485 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 10]
def baseStart_8336485 : Nat := 118140960795 + 8336485 * 2 ^ 59
def prefixEnd_8336485 : Nat := 4983230072969 + 3 ^ 40 * 8336485 * 2
def baseEnd_8336485 : Nat := 475624863777435688644301

theorem tailTrace_8336485 : CollatzResearch.WordTrace tailWord_8336485 prefixEnd_8336485 475624863777435688644301 := by
  unfold tailWord_8336485
  simp only [CollatzResearch.WordTrace]
  refine ⟨304056587203346078131922909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202704391468897385421281939 304056587203346078131922909)
  ·
    refine ⟨114021220201254779299471091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304056587203346078131922909 114021220201254779299471091)
    ·
      refine ⟨171031830301882168949206637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114021220201254779299471091 171031830301882168949206637)
      ·
        refine ⟨64136936363205813355952489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171031830301882168949206637 64136936363205813355952489)
        ·
          refine ⟨48102702272404360016964367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64136936363205813355952489 48102702272404360016964367)
          ·
            refine ⟨72154053408606540025446551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48102702272404360016964367 72154053408606540025446551)
            ·
              refine ⟨108231080112909810038169827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72154053408606540025446551 108231080112909810038169827)
              ·
                refine ⟨162346620169364715057254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108231080112909810038169827 162346620169364715057254741)
                ·
                  refine ⟨475624863777435688644301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162346620169364715057254741 475624863777435688644301)
                  ·
                    rfl

theorem cell23_8336485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_8336485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336485 prefixEnd_8336485 := by exact prefixLift 8336485
  have htrace : WordTrace (prefixWord ++ tailWord_8336485) baseStart_8336485 baseEnd_8336485 := by
    simpa [prefixWord, tailWord_8336485, baseEnd_8336485] using wordTrace_append hprefix tailTrace_8336485
  have hstable : (prefixWord ++ tailWord_8336485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336485).length < 2 ^ (prefixWord ++ tailWord_8336485).sum := by decide
  have hdescent : baseEnd_8336485 < baseStart_8336485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336502 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_8336502 : Nat := 118140960795 + 8336502 * 2 ^ 59
def prefixEnd_8336502 : Nat := 4983230072969 + 3 ^ 40 * 8336502 * 2
def baseEnd_8336502 : Nat := 475625833685338625698459

theorem tailTrace_8336502 : CollatzResearch.WordTrace tailWord_8336502 prefixEnd_8336502 475625833685338625698459 := by
  unfold tailWord_8336502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003575452767780627205735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202704804829522993356861173 19003575452767780627205735)
  ·
    refine ⟨28505363179151670940808603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003575452767780627205735 28505363179151670940808603)
    ·
      refine ⟨42758044768727506411212905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28505363179151670940808603 42758044768727506411212905)
      ·
        refine ⟨32068533576545629808409679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42758044768727506411212905 32068533576545629808409679)
        ·
          refine ⟨48102800364818444712614519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32068533576545629808409679 48102800364818444712614519)
          ·
            refine ⟨72154200547227667068921779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48102800364818444712614519 72154200547227667068921779)
            ·
              refine ⟨108231300820841500603382669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72154200547227667068921779 108231300820841500603382669)
              ·
                refine ⟨40586737807815562726268501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108231300820841500603382669 40586737807815562726268501)
                ·
                  refine ⟨475625833685338625698459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40586737807815562726268501 475625833685338625698459)
                  ·
                    rfl

theorem cell23_8336502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_8336502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336502 prefixEnd_8336502 := by exact prefixLift 8336502
  have htrace : WordTrace (prefixWord ++ tailWord_8336502) baseStart_8336502 baseEnd_8336502 := by
    simpa [prefixWord, tailWord_8336502, baseEnd_8336502] using wordTrace_append hprefix tailTrace_8336502
  have hstable : (prefixWord ++ tailWord_8336502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336502).length < 2 ^ (prefixWord ++ tailWord_8336502).sum := by decide
  have hdescent : baseEnd_8336502 < baseStart_8336502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336557 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_8336557 : Nat := 118140960795 + 8336557 * 2 ^ 59
def prefixEnd_8336557 : Nat := 4983230072969 + 3 ^ 40 * 8336557 * 2
def baseEnd_8336557 : Nat := 1426886914868014972032793

theorem tailTrace_8336557 : CollatzResearch.WordTrace tailWord_8336557 prefixEnd_8336557 1426886914868014972032793 := by
  unfold tailWord_8336557
  simp only [CollatzResearch.WordTrace]
  refine ⟨304059213259085234428543925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202706142172723489619029283 304059213259085234428543925)
  ·
    refine ⟨28505551243039240727675993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304059213259085234428543925 28505551243039240727675993)
    ·
      refine ⟨21379163432279430545756995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28505551243039240727675993 21379163432279430545756995)
      ·
        refine ⟨32068745148419145818635493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21379163432279430545756995 32068745148419145818635493)
        ·
          refine ⟨6012889715328589840994155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32068745148419145818635493 6012889715328589840994155)
          ·
            refine ⟨9019334572992884761491233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012889715328589840994155 9019334572992884761491233)
            ·
              refine ⟨6764500929744663571118425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9019334572992884761491233 6764500929744663571118425)
              ·
                refine ⟨5073375697308497678338819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764500929744663571118425 5073375697308497678338819)
                ·
                  refine ⟨7610063545962746517508229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073375697308497678338819 7610063545962746517508229)
                  ·
                    refine ⟨1426886914868014972032793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7610063545962746517508229 1426886914868014972032793)
                    ·
                      rfl

theorem cell23_8336557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_8336557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336557 prefixEnd_8336557 := by exact prefixLift 8336557
  have htrace : WordTrace (prefixWord ++ tailWord_8336557) baseStart_8336557 baseEnd_8336557 := by
    simpa [prefixWord, tailWord_8336557, baseEnd_8336557] using wordTrace_append hprefix tailTrace_8336557
  have hstable : (prefixWord ++ tailWord_8336557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336557).length < 2 ^ (prefixWord ++ tailWord_8336557).sum := by decide
  have hdescent : baseEnd_8336557 < baseStart_8336557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336563 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 1, 1, 3]
def baseStart_8336563 : Nat := 118140960795 + 8336563 * 2 ^ 59
def prefixEnd_8336563 : Nat := 4983230072969 + 3 ^ 40 * 8336563 * 2
def baseEnd_8336563 : Nat := 4280663825487971892623351

theorem tailTrace_8336563 : CollatzResearch.WordTrace tailWord_8336563 prefixEnd_8336563 4280663825487971892623351 := by
  unfold tailWord_8336563
  simp only [CollatzResearch.WordTrace]
  refine ⟨304059432097063497453262343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202706288064708998302174895 304059432097063497453262343)
  ·
    refine ⟨456089148145595246179893515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304059432097063497453262343 456089148145595246179893515)
    ·
      refine ⟨684133722218392869269840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456089148145595246179893515 684133722218392869269840273)
      ·
        refine ⟨513100291663794651952380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684133722218392869269840273 513100291663794651952380205)
        ·
          refine ⟨192412609373922994482142577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513100291663794651952380205 192412609373922994482142577)
          ·
            refine ⟨144309457030442245861606933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192412609373922994482142577 144309457030442245861606933)
            ·
              refine ⟨6764505798301980274762825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144309457030442245861606933 6764505798301980274762825)
              ·
                refine ⟨5073379348726485206072119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764505798301980274762825 5073379348726485206072119)
                ·
                  refine ⟨7610069023089727809108179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073379348726485206072119 7610069023089727809108179)
                  ·
                    refine ⟨11415103534634591713662269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610069023089727809108179 11415103534634591713662269)
                    ·
                      refine ⟨4280663825487971892623351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11415103534634591713662269 4280663825487971892623351)
                      ·
                        rfl

theorem cell23_8336563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 1, 3].length) (baseStart_8336563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336563 prefixEnd_8336563 := by exact prefixLift 8336563
  have htrace : WordTrace (prefixWord ++ tailWord_8336563) baseStart_8336563 baseEnd_8336563 := by
    simpa [prefixWord, tailWord_8336563, baseEnd_8336563] using wordTrace_append hprefix tailTrace_8336563
  have hstable : (prefixWord ++ tailWord_8336563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336563).length < 2 ^ (prefixWord ++ tailWord_8336563).sum := by decide
  have hdescent : baseEnd_8336563 < baseStart_8336563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336586 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_8336586 : Nat := 118140960795 + 8336586 * 2 ^ 59
def prefixEnd_8336586 : Nat := 4983230072969 + 3 ^ 40 * 8336586 * 2
def baseEnd_8336586 : Nat := 4280675635543025302635745

theorem tailTrace_8336586 : CollatzResearch.WordTrace tailWord_8336586 prefixEnd_8336586 4280675635543025302635745 := by
  unfold tailWord_8336586
  simp only [CollatzResearch.WordTrace]
  refine ⟨76015067743995043095337403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202706847317320114920899741 76015067743995043095337403)
  ·
    refine ⟨114022601615992564643006105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76015067743995043095337403 114022601615992564643006105)
    ·
      refine ⟨85516951211994423482254579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114022601615992564643006105 85516951211994423482254579)
      ·
        refine ⟨128275426817991635223381869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85516951211994423482254579 128275426817991635223381869)
        ·
          refine ⟨48103285056746863208768201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128275426817991635223381869 48103285056746863208768201)
          ·
            refine ⟨36077463792560147406576151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48103285056746863208768201 36077463792560147406576151)
            ·
              refine ⟨54116195688840221109864227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36077463792560147406576151 54116195688840221109864227)
              ·
                refine ⟨81174293533260331664796341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54116195688840221109864227 81174293533260331664796341)
                ·
                  refine ⟨7610090018743156093574657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81174293533260331664796341 7610090018743156093574657)
                  ·
                    refine ⟨5707567514057367070180993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7610090018743156093574657 5707567514057367070180993)
                    ·
                      refine ⟨4280675635543025302635745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707567514057367070180993 4280675635543025302635745)
                      ·
                        rfl

theorem cell23_8336586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_8336586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336586 prefixEnd_8336586 := by exact prefixLift 8336586
  have htrace : WordTrace (prefixWord ++ tailWord_8336586) baseStart_8336586 baseEnd_8336586 := by
    simpa [prefixWord, tailWord_8336586, baseEnd_8336586] using wordTrace_append hprefix tailTrace_8336586
  have hstable : (prefixWord ++ tailWord_8336586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336586).length < 2 ^ (prefixWord ++ tailWord_8336586).sum := by decide
  have hdescent : baseEnd_8336586 < baseStart_8336586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336590 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_8336590 : Nat := 118140960795 + 8336590 * 2 ^ 59
def prefixEnd_8336590 : Nat := 4983230072969 + 3 ^ 40 * 8336590 * 2
def baseEnd_8336590 : Nat := 4280677689465643286985727

theorem tailTrace_8336590 : CollatzResearch.WordTrace tailWord_8336590 prefixEnd_8336590 4280677689465643286985727 := by
  unfold tailWord_8336590
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007552108495710133061903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202706944578643787376330149 38007552108495710133061903)
  ·
    refine ⟨57011328162743565199592855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38007552108495710133061903 57011328162743565199592855)
    ·
      refine ⟨85516992244115347799389283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57011328162743565199592855 85516992244115347799389283)
      ·
        refine ⟨128275488366173021699083925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85516992244115347799389283 128275488366173021699083925)
        ·
          refine ⟨6012913517164360392144559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128275488366173021699083925 6012913517164360392144559)
          ·
            refine ⟨9019370275746540588216839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012913517164360392144559 9019370275746540588216839)
            ·
              refine ⟨13529055413619810882325259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019370275746540588216839 13529055413619810882325259)
              ·
                refine ⟨20293583120429716323487889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529055413619810882325259 20293583120429716323487889)
                ·
                  refine ⟨15220187340322287242615917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20293583120429716323487889 15220187340322287242615917)
                  ·
                    refine ⟨5707570252620857715980969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15220187340322287242615917 5707570252620857715980969)
                    ·
                      refine ⟨4280677689465643286985727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707570252620857715980969 4280677689465643286985727)
                      ·
                        rfl

theorem cell23_8336590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_8336590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336590 prefixEnd_8336590 := by exact prefixLift 8336590
  have htrace : WordTrace (prefixWord ++ tailWord_8336590) baseStart_8336590 baseEnd_8336590 := by
    simpa [prefixWord, tailWord_8336590, baseEnd_8336590] using wordTrace_append hprefix tailTrace_8336590
  have hstable : (prefixWord ++ tailWord_8336590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336590).length < 2 ^ (prefixWord ++ tailWord_8336590).sum := by decide
  have hdescent : baseEnd_8336590 < baseStart_8336590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336613 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_8336613 : Nat := 118140960795 + 8336613 * 2 ^ 59
def prefixEnd_8336613 : Nat := 4983230072969 + 3 ^ 40 * 8336613 * 2
def baseEnd_8336613 : Nat := 1426896499840232232332707

theorem tailTrace_8336613 : CollatzResearch.WordTrace tailWord_8336613 prefixEnd_8336613 1426896499840232232332707 := by
  unfold tailWord_8336613
  simp only [CollatzResearch.WordTrace]
  refine ⟨304061255746882355992582493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202707503831254903995054995 304061255746882355992582493)
  ·
    refine ⟨114022970905080883497218435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304061255746882355992582493 114022970905080883497218435)
    ·
      refine ⟨171034456357621325245827653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114022970905080883497218435 171034456357621325245827653)
      ·
        refine ⟨32068960567053998483592685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171034456357621325245827653 32068960567053998483592685)
        ·
          refine ⟨12025860212645249431347257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32068960567053998483592685 12025860212645249431347257)
          ·
            refine ⟨9019395159483937073510443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12025860212645249431347257 9019395159483937073510443)
            ·
              refine ⟨13529092739225905610265665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019395159483937073510443 13529092739225905610265665)
              ·
                refine ⟨10146819554419429207699249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13529092739225905610265665 10146819554419429207699249)
                ·
                  refine ⟨7610114665814571905774437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10146819554419429207699249 7610114665814571905774437)
                  ·
                    refine ⟨1426896499840232232332707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7610114665814571905774437 1426896499840232232332707)
                    ·
                      rfl

theorem cell23_8336613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_8336613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336613 prefixEnd_8336613 := by exact prefixLift 8336613
  have htrace : WordTrace (prefixWord ++ tailWord_8336613) baseStart_8336613 baseEnd_8336613 := by
    simpa [prefixWord, tailWord_8336613, baseEnd_8336613] using wordTrace_append hprefix tailTrace_8336613
  have hstable : (prefixWord ++ tailWord_8336613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336613).length < 2 ^ (prefixWord ++ tailWord_8336613).sum := by decide
  have hdescent : baseEnd_8336613 < baseStart_8336613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336622 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_8336622 : Nat := 118140960795 + 8336622 * 2 ^ 59
def prefixEnd_8336622 : Nat := 4983230072969 + 3 ^ 40 * 8336622 * 2
def baseEnd_8336622 : Nat := 1426898040282195720595193

theorem tailTrace_8336622 : CollatzResearch.WordTrace tailWord_8336622 prefixEnd_8336622 1426898040282195720595193 := by
  unfold tailWord_8336622
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007698000481218816207515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202707722669233167019773413 38007698000481218816207515)
  ·
    refine ⟨57011547000721828224311273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38007698000481218816207515 57011547000721828224311273)
    ·
      refine ⟨42758660250541371168233455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57011547000721828224311273 42758660250541371168233455)
      ·
        refine ⟨64137990375812056752350183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42758660250541371168233455 64137990375812056752350183)
        ·
          refine ⟨96206985563718085128525275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64137990375812056752350183 96206985563718085128525275)
          ·
            refine ⟨144310478345577127692787913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96206985563718085128525275 144310478345577127692787913)
            ·
              refine ⟨108232858759182845769590935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144310478345577127692787913 108232858759182845769590935)
              ·
                refine ⟨162349288138774268654386403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108232858759182845769590935 162349288138774268654386403)
                ·
                  refine ⟨243523932208161402981579605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162349288138774268654386403 243523932208161402981579605)
                  ·
                    refine ⟨1426898040282195720595193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243523932208161402981579605 1426898040282195720595193)
                    ·
                      rfl

theorem cell23_8336622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_8336622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336622 prefixEnd_8336622 := by exact prefixLift 8336622
  have htrace : WordTrace (prefixWord ++ tailWord_8336622) baseStart_8336622 baseEnd_8336622 := by
    simpa [prefixWord, tailWord_8336622, baseEnd_8336622] using wordTrace_append hprefix tailTrace_8336622
  have hstable : (prefixWord ++ tailWord_8336622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336622).length < 2 ^ (prefixWord ++ tailWord_8336622).sum := by decide
  have hdescent : baseEnd_8336622 < baseStart_8336622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336697 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 1, 3, 2]
def baseStart_8336697 : Nat := 118140960795 + 8336697 * 2 ^ 59
def prefixEnd_8336697 : Nat := 4983230072969 + 3 ^ 40 * 8336697 * 2
def baseEnd_8336697 : Nat := 4280732631895674368347735

theorem tailTrace_8336697 : CollatzResearch.WordTrace tailWord_8336697 prefixEnd_8336697 4280732631895674368347735 := by
  unfold tailWord_8336697
  simp only [CollatzResearch.WordTrace]
  refine ⟨304064319478578038338640345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202709546319052025559093563 304064319478578038338640345)
  ·
    refine ⟨228048239608933528753980259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304064319478578038338640345 228048239608933528753980259)
    ·
      refine ⟨342072359413400293130970389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228048239608933528753980259 342072359413400293130970389)
      ·
        refine ⟨16034641847503138740514237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342072359413400293130970389 16034641847503138740514237)
        ·
          refine ⟨6012990692813677027692839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16034641847503138740514237 6012990692813677027692839)
          ·
            refine ⟨9019486039220515541539259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012990692813677027692839 9019486039220515541539259)
            ·
              refine ⟨13529229058830773312308889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019486039220515541539259 13529229058830773312308889)
              ·
                refine ⟨10146921794123079984231667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13529229058830773312308889 10146921794123079984231667)
                ·
                  refine ⟨15220382691184619976347501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146921794123079984231667 15220382691184619976347501)
                  ·
                    refine ⟨5707643509194232491130313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15220382691184619976347501 5707643509194232491130313)
                    ·
                      refine ⟨4280732631895674368347735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707643509194232491130313 4280732631895674368347735)
                      ·
                        rfl

theorem cell23_8336697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_8336697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336697 prefixEnd_8336697 := by exact prefixLift 8336697
  have htrace : WordTrace (prefixWord ++ tailWord_8336697) baseStart_8336697 baseEnd_8336697 := by
    simpa [prefixWord, tailWord_8336697, baseEnd_8336697] using wordTrace_append hprefix tailTrace_8336697
  have hstable : (prefixWord ++ tailWord_8336697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336697).length < 2 ^ (prefixWord ++ tailWord_8336697).sum := by decide
  have hdescent : baseEnd_8336697 < baseStart_8336697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336729 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_8336729 : Nat := 118140960795 + 8336729 * 2 ^ 59
def prefixEnd_8336729 : Nat := 4983230072969 + 3 ^ 40 * 8336729 * 2
def baseEnd_8336729 : Nat := 1426916354425539414382529

theorem tailTrace_8336729 : CollatzResearch.WordTrace tailWord_8336729 prefixEnd_8336729 1426916354425539414382529 := by
  unfold tailWord_8336729
  simp only [CollatzResearch.WordTrace]
  refine ⟨304065486614462107803805241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202710324409641405202536827 304065486614462107803805241)
  ·
    refine ⟨228049114960846580852853931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304065486614462107803805241 228049114960846580852853931)
    ·
      refine ⟨342073672441269871279280897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228049114960846580852853931 342073672441269871279280897)
      ·
        refine ⟨256555254330952403459460673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342073672441269871279280897 256555254330952403459460673)
        ·
          refine ⟨192416440748214302594595505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256555254330952403459460673 192416440748214302594595505)
          ·
            refine ⟨144312330561160726945946629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192416440748214302594595505 144312330561160726945946629)
            ·
              refine ⟨27058561980217636302364993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144312330561160726945946629 27058561980217636302364993)
              ·
                refine ⟨20293921485163227226773745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27058561980217636302364993 20293921485163227226773745)
                ·
                  refine ⟨15220441113872420420080309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20293921485163227226773745 15220441113872420420080309)
                  ·
                    refine ⟨1426916354425539414382529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15220441113872420420080309 1426916354425539414382529)
                    ·
                      rfl

theorem cell23_8336729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_8336729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336729 prefixEnd_8336729 := by exact prefixLift 8336729
  have htrace : WordTrace (prefixWord ++ tailWord_8336729) baseStart_8336729 baseEnd_8336729 := by
    simpa [prefixWord, tailWord_8336729, baseEnd_8336729] using wordTrace_append hprefix tailTrace_8336729
  have hstable : (prefixWord ++ tailWord_8336729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336729).length < 2 ^ (prefixWord ++ tailWord_8336729).sum := by decide
  have hdescent : baseEnd_8336729 < baseStart_8336729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336736 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2]
def baseStart_8336736 : Nat := 118140960795 + 8336736 * 2 ^ 59
def prefixEnd_8336736 : Nat := 4983230072969 + 3 ^ 40 * 8336736 * 2
def baseEnd_8336736 : Nat := 4280752657641199715760055

theorem tailTrace_8336736 : CollatzResearch.WordTrace tailWord_8336736 prefixEnd_8336736 4280752657641199715760055 := by
  unfold tailWord_8336736
  simp only [CollatzResearch.WordTrace]
  refine ⟨152032870962718373999655031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202710494616957831999540041 152032870962718373999655031)
  ·
    refine ⟨228049306444077560999482547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152032870962718373999655031 228049306444077560999482547)
    ·
      refine ⟨342073959666116341499223821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228049306444077560999482547 342073959666116341499223821)
      ·
        refine ⟨128277734874793628062208933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342073959666116341499223821 128277734874793628062208933)
        ·
          refine ⟨24052075289023805261664175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128277734874793628062208933 24052075289023805261664175)
          ·
            refine ⟨36078112933535707892496263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24052075289023805261664175 36078112933535707892496263)
            ·
              refine ⟨54117169400303561838744395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36078112933535707892496263 54117169400303561838744395)
              ·
                refine ⟨81175754100455342758116593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54117169400303561838744395 81175754100455342758116593)
                ·
                  refine ⟨60881815575341507068587445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81175754100455342758116593 60881815575341507068587445)
                  ·
                    refine ⟨5707670210188266287680073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60881815575341507068587445 5707670210188266287680073)
                    ·
                      refine ⟨4280752657641199715760055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707670210188266287680073 4280752657641199715760055)
                      ·
                        rfl

theorem cell23_8336736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_8336736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336736 prefixEnd_8336736 := by exact prefixLift 8336736
  have htrace : WordTrace (prefixWord ++ tailWord_8336736) baseStart_8336736 baseEnd_8336736 := by
    simpa [prefixWord, tailWord_8336736, baseEnd_8336736] using wordTrace_append hprefix tailTrace_8336736
  have hstable : (prefixWord ++ tailWord_8336736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336736).length < 2 ^ (prefixWord ++ tailWord_8336736).sum := by decide
  have hdescent : baseEnd_8336736 < baseStart_8336736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336739 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_8336739 : Nat := 118140960795 + 8336739 * 2 ^ 59
def prefixEnd_8336739 : Nat := 4983230072969 + 3 ^ 40 * 8336739 * 2
def baseEnd_8336739 : Nat := 4280754198083163204022541

theorem tailTrace_8336739 : CollatzResearch.WordTrace tailWord_8336739 prefixEnd_8336739 4280754198083163204022541 := by
  unfold tailWord_8336739
  simp only [CollatzResearch.WordTrace]
  refine ⟨304065851344425879511669271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202710567562950586341112847 304065851344425879511669271)
  ·
    refine ⟨456098777016638819267503907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304065851344425879511669271 456098777016638819267503907)
    ·
      refine ⟨684148165524958228901255861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456098777016638819267503907 684148165524958228901255861)
      ·
        refine ⟨64138890517964833959492737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 684148165524958228901255861 64138890517964833959492737)
        ·
          refine ⟨48104167888473625469619553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64138890517964833959492737 48104167888473625469619553)
          ·
            refine ⟨36078125916355219102214665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48104167888473625469619553 36078125916355219102214665)
            ·
              refine ⟨27058594437266414326660999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36078125916355219102214665 27058594437266414326660999)
              ·
                refine ⟨40587891655899621489991499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27058594437266414326660999 40587891655899621489991499)
                ·
                  refine ⟨60881837483849432234987249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40587891655899621489991499 60881837483849432234987249)
                  ·
                    refine ⟨45661378112887074176240437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60881837483849432234987249 45661378112887074176240437)
                    ·
                      refine ⟨4280754198083163204022541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45661378112887074176240437 4280754198083163204022541)
                      ·
                        rfl

theorem cell23_8336739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_8336739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336739 prefixEnd_8336739 := by exact prefixLift 8336739
  have htrace : WordTrace (prefixWord ++ tailWord_8336739) baseStart_8336739 baseEnd_8336739 := by
    simpa [prefixWord, tailWord_8336739, baseEnd_8336739] using wordTrace_append hprefix tailTrace_8336739
  have hstable : (prefixWord ++ tailWord_8336739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336739).length < 2 ^ (prefixWord ++ tailWord_8336739).sum := by decide
  have hdescent : baseEnd_8336739 < baseStart_8336739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336793 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 1, 4]
def baseStart_8336793 : Nat := 118140960795 + 8336793 * 2 ^ 59
def prefixEnd_8336793 : Nat := 4983230072969 + 3 ^ 40 * 8336793 * 2
def baseEnd_8336793 : Nat := 1426927308679501997582431

theorem tailTrace_8336793 : CollatzResearch.WordTrace tailWord_8336793 prefixEnd_8336793 1426927308679501997582431 := by
  unfold tailWord_8336793
  simp only [CollatzResearch.WordTrace]
  refine ⟨304067820886230246734135033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202711880590820164489423355 304067820886230246734135033)
  ·
    refine ⟨228050865664672685050601275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304067820886230246734135033 228050865664672685050601275)
    ·
      refine ⟨342076298497009027575901913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228050865664672685050601275 342076298497009027575901913)
      ·
        refine ⟨256557223872756770681926435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342076298497009027575901913 256557223872756770681926435)
        ·
          refine ⟨384835835809135156022889653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256557223872756770681926435 384835835809135156022889653)
          ·
            refine ⟨36078359607106420877145905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384835835809135156022889653 36078359607106420877145905)
            ·
              refine ⟨27058769705329815657859429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36078359607106420877145905 27058769705329815657859429)
              ·
                refine ⟨5073519319749340435848643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27058769705329815657859429 5073519319749340435848643)
                ·
                  refine ⟨7610278979624010653772965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073519319749340435848643 7610278979624010653772965)
                  ·
                    refine ⟨1426927308679501997582431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7610278979624010653772965 1426927308679501997582431)
                    ·
                      rfl

theorem cell23_8336793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_8336793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336793 prefixEnd_8336793 := by exact prefixLift 8336793
  have htrace : WordTrace (prefixWord ++ tailWord_8336793) baseStart_8336793 baseEnd_8336793 := by
    simpa [prefixWord, tailWord_8336793, baseEnd_8336793] using wordTrace_append hprefix tailTrace_8336793
  have hstable : (prefixWord ++ tailWord_8336793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336793).length < 2 ^ (prefixWord ++ tailWord_8336793).sum := by decide
  have hdescent : baseEnd_8336793 < baseStart_8336793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_8336816 : Nat := 118140960795 + 8336816 * 2 ^ 59
def prefixEnd_8336816 : Nat := 4983230072969 + 3 ^ 40 * 8336816 * 2
def baseEnd_8336816 : Nat := 4280793736093559402759687

theorem tailTrace_8336816 : CollatzResearch.WordTrace tailWord_8336816 prefixEnd_8336816 4280793736093559402759687 := by
  unfold tailWord_8336816
  simp only [CollatzResearch.WordTrace]
  refine ⟨152034329882573460831111151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202712439843431281108148201 152034329882573460831111151)
  ·
    refine ⟨228051494823860191246666727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152034329882573460831111151 228051494823860191246666727)
    ·
      refine ⟨342077242235790286870000091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228051494823860191246666727 342077242235790286870000091)
      ·
        refine ⟨513115863353685430305000137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342077242235790286870000091 513115863353685430305000137)
        ·
          refine ⟨384836897515264072728750103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513115863353685430305000137 384836897515264072728750103)
          ·
            refine ⟨577255346272896109093125155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384836897515264072728750103 577255346272896109093125155)
            ·
              refine ⟨865883019409344163639687733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577255346272896109093125155 865883019409344163639687733)
              ·
                refine ⟨81176533069626015341220725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 865883019409344163639687733 81176533069626015341220725)
                ·
                  refine ⟨7610299975277438938239443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81176533069626015341220725 7610299975277438938239443)
                  ·
                    refine ⟨11415449962916158407359165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610299975277438938239443 11415449962916158407359165)
                    ·
                      refine ⟨4280793736093559402759687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11415449962916158407359165 4280793736093559402759687)
                      ·
                        rfl

theorem cell23_8336816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_8336816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336816 prefixEnd_8336816 := by exact prefixLift 8336816
  have htrace : WordTrace (prefixWord ++ tailWord_8336816) baseStart_8336816 baseEnd_8336816 := by
    simpa [prefixWord, tailWord_8336816, baseEnd_8336816] using wordTrace_append hprefix tailTrace_8336816
  have hstable : (prefixWord ++ tailWord_8336816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336816).length < 2 ^ (prefixWord ++ tailWord_8336816).sum := by decide
  have hdescent : baseEnd_8336816 < baseStart_8336816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336819 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 3, 5]
def baseStart_8336819 : Nat := 118140960795 + 8336819 * 2 ^ 59
def prefixEnd_8336819 : Nat := 4983230072969 + 3 ^ 40 * 8336819 * 2
def baseEnd_8336819 : Nat := 1426931758845174297007391

theorem tailTrace_8336819 : CollatzResearch.WordTrace tailWord_8336819 prefixEnd_8336819 1426931758845174297007391 := by
  unfold tailWord_8336819
  simp only [CollatzResearch.WordTrace]
  refine ⟨304068769184136053174581511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202712512789424035449721007 304068769184136053174581511)
  ·
    refine ⟨456103153776204079761872267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304068769184136053174581511 456103153776204079761872267)
    ·
      refine ⟨684154730664306119642808401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456103153776204079761872267 684154730664306119642808401)
      ·
        refine ⟨513116047998229589732106301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684154730664306119642808401 513116047998229589732106301)
        ·
          refine ⟨192418517999336096149539863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513116047998229589732106301 192418517999336096149539863)
          ·
            refine ⟨288627776999004144224309795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192418517999336096149539863 288627776999004144224309795)
            ·
              refine ⟨432941665498506216336464693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288627776999004144224309795 432941665498506216336464693)
              ·
                refine ⟨40588281140484957781543565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432941665498506216336464693 40588281140484957781543565)
                ·
                  refine ⟨15220605427681859168078837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40588281140484957781543565 15220605427681859168078837)
                  ·
                    refine ⟨1426931758845174297007391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15220605427681859168078837 1426931758845174297007391)
                    ·
                      rfl

theorem cell23_8336819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].length) (baseStart_8336819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336819 prefixEnd_8336819 := by exact prefixLift 8336819
  have htrace : WordTrace (prefixWord ++ tailWord_8336819) baseStart_8336819 baseEnd_8336819 := by
    simpa [prefixWord, tailWord_8336819, baseEnd_8336819] using wordTrace_append hprefix tailTrace_8336819
  have hstable : (prefixWord ++ tailWord_8336819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336819).length < 2 ^ (prefixWord ++ tailWord_8336819).sum := by decide
  have hdescent : baseEnd_8336819 < baseStart_8336819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336834 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_8336834 : Nat := 118140960795 + 8336834 * 2 ^ 59
def prefixEnd_8336834 : Nat := 4983230072969 + 3 ^ 40 * 8336834 * 2
def baseEnd_8336834 : Nat := 4280802978745340332334605

theorem tailTrace_8336834 : CollatzResearch.WordTrace tailWord_8336834 prefixEnd_8336834 4280802978745340332334605 := by
  unfold tailWord_8336834
  simp only [CollatzResearch.WordTrace]
  refine ⟨76017329069770427684094389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202712877519387807157585037 76017329069770427684094389)
  ·
    refine ⟨7126624600290977595383849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76017329069770427684094389 7126624600290977595383849)
    ·
      refine ⟨5344968450218233196537887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7126624600290977595383849 5344968450218233196537887)
      ·
        refine ⟨8017452675327349794806831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344968450218233196537887 8017452675327349794806831)
        ·
          refine ⟨12026179012991024692210247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017452675327349794806831 12026179012991024692210247)
          ·
            refine ⟨18039268519486537038315371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12026179012991024692210247 18039268519486537038315371)
            ·
              refine ⟨27058902779229805557473057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18039268519486537038315371 27058902779229805557473057)
              ·
                refine ⟨20294177084422354168104793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27058902779229805557473057 20294177084422354168104793)
                ·
                  refine ⟨15220632813316765626078595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20294177084422354168104793 15220632813316765626078595)
                  ·
                    refine ⟨22830949219975148439117893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15220632813316765626078595 22830949219975148439117893)
                    ·
                      refine ⟨4280802978745340332334605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22830949219975148439117893 4280802978745340332334605)
                      ·
                        rfl

theorem cell23_8336834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_8336834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336834 prefixEnd_8336834 := by exact prefixLift 8336834
  have htrace : WordTrace (prefixWord ++ tailWord_8336834) baseStart_8336834 baseEnd_8336834 := by
    simpa [prefixWord, tailWord_8336834, baseEnd_8336834] using wordTrace_append hprefix tailTrace_8336834
  have hstable : (prefixWord ++ tailWord_8336834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336834).length < 2 ^ (prefixWord ++ tailWord_8336834).sum := by decide
  have hdescent : baseEnd_8336834 < baseStart_8336834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336877 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_8336877 : Nat := 118140960795 + 8336877 * 2 ^ 59
def prefixEnd_8336877 : Nat := 4983230072969 + 3 ^ 40 * 8336877 * 2
def baseEnd_8336877 : Nat := 4280825058413483664096907

theorem tailTrace_8336877 : CollatzResearch.WordTrace tailWord_8336877 prefixEnd_8336877 4280825058413483664096907 := by
  unfold tailWord_8336877
  simp only [CollatzResearch.WordTrace]
  refine ⟨304070884617925929080192885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202713923078617286053461923 304070884617925929080192885)
  ·
    refine ⟨28506645432930555851268083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304070884617925929080192885 28506645432930555851268083)
    ·
      refine ⟨42759968149395833776902125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28506645432930555851268083 42759968149395833776902125)
      ·
        refine ⟨16034988056023437666338297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42759968149395833776902125 16034988056023437666338297)
        ·
          refine ⟨12026241042017578249753723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16034988056023437666338297 12026241042017578249753723)
          ·
            refine ⟨18039361563026367374630585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12026241042017578249753723 18039361563026367374630585)
            ·
              refine ⟨13529521172269775530972939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18039361563026367374630585 13529521172269775530972939)
              ·
                refine ⟨20294281758404663296459409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529521172269775530972939 20294281758404663296459409)
                ·
                  refine ⟨15220711318803497472344557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20294281758404663296459409 15220711318803497472344557)
                  ·
                    refine ⟨5707766744551311552129209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15220711318803497472344557 5707766744551311552129209)
                    ·
                      refine ⟨4280825058413483664096907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707766744551311552129209 4280825058413483664096907)
                      ·
                        rfl

theorem cell23_8336877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_8336877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336877 prefixEnd_8336877 := by exact prefixLift 8336877
  have htrace : WordTrace (prefixWord ++ tailWord_8336877) baseStart_8336877 baseEnd_8336877 := by
    simpa [prefixWord, tailWord_8336877, baseEnd_8336877] using wordTrace_append hprefix tailTrace_8336877
  have hstable : (prefixWord ++ tailWord_8336877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336877).length < 2 ^ (prefixWord ++ tailWord_8336877).sum := by decide
  have hdescent : baseEnd_8336877 < baseStart_8336877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336879 : List Nat := [1, 1, 2, 1, 4, 1, 4, 9]
def baseStart_8336879 : Nat := 118140960795 + 8336879 * 2 ^ 59
def prefixEnd_8336879 : Nat := 4983230072969 + 3 ^ 40 * 8336879 * 2
def baseEnd_8336879 : Nat := 158549114273140468750811

theorem tailTrace_8336879 : CollatzResearch.WordTrace tailWord_8336879 prefixEnd_8336879 158549114273140468750811 := by
  unfold tailWord_8336879
  simp only [CollatzResearch.WordTrace]
  refine ⟨304070957563918683421765691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202713971709279122281177127 304070957563918683421765691)
  ·
    refine ⟨456106436345878025132648537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304070957563918683421765691 456106436345878025132648537)
    ·
      refine ⟨342079827259408518849486403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456106436345878025132648537 342079827259408518849486403)
      ·
        refine ⟨513119740889112778274229605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342079827259408518849486403 513119740889112778274229605)
        ·
          refine ⟨96209951416708645926418051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513119740889112778274229605 96209951416708645926418051)
          ·
            refine ⟨144314927125062968889627077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96209951416708645926418051 144314927125062968889627077)
            ·
              refine ⟨27059048835949306666805077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144314927125062968889627077 27059048835949306666805077)
              ·
                refine ⟨158549114273140468750811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27059048835949306666805077 158549114273140468750811)
                ·
                  rfl

theorem cell23_8336879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 9].length) (baseStart_8336879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336879 prefixEnd_8336879 := by exact prefixLift 8336879
  have htrace : WordTrace (prefixWord ++ tailWord_8336879) baseStart_8336879 baseEnd_8336879 := by
    simpa [prefixWord, tailWord_8336879, baseEnd_8336879] using wordTrace_append hprefix tailTrace_8336879
  have hstable : (prefixWord ++ tailWord_8336879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336879).length < 2 ^ (prefixWord ++ tailWord_8336879).sum := by decide
  have hdescent : baseEnd_8336879 < baseStart_8336879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336893 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_8336893 : Nat := 118140960795 + 8336893 * 2 ^ 59
def prefixEnd_8336893 : Nat := 4983230072969 + 3 ^ 40 * 8336893 * 2
def baseEnd_8336893 : Nat := 4280833274103955601496833

theorem tailTrace_8336893 : CollatzResearch.WordTrace tailWord_8336893 prefixEnd_8336893 4280833274103955601496833 := by
  unfold tailWord_8336893
  simp only [CollatzResearch.WordTrace]
  refine ⟨304071468185867963812775333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202714312123911975875183555 304071468185867963812775333)
  ·
    refine ⟨57013400284850243214895375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304071468185867963812775333 57013400284850243214895375)
    ·
      refine ⟨85520100427275364822343063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57013400284850243214895375 85520100427275364822343063)
      ·
        refine ⟨128280150640913047233514595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85520100427275364822343063 128280150640913047233514595)
        ·
          refine ⟨192420225961369570850271893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128280150640913047233514595 192420225961369570850271893)
          ·
            refine ⟨9019698091939198633606495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192420225961369570850271893 9019698091939198633606495)
            ·
              refine ⟨13529547137908797950409743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019698091939198633606495 13529547137908797950409743)
              ·
                refine ⟨20294320706863196925614615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529547137908797950409743 20294320706863196925614615)
                ·
                  refine ⟨30441481060294795388421923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20294320706863196925614615 30441481060294795388421923)
                  ·
                    refine ⟨45662221590442193082632885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30441481060294795388421923 45662221590442193082632885)
                    ·
                      refine ⟨4280833274103955601496833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45662221590442193082632885 4280833274103955601496833)
                      ·
                        rfl

theorem cell23_8336893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_8336893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336893 prefixEnd_8336893 := by exact prefixLift 8336893
  have htrace : WordTrace (prefixWord ++ tailWord_8336893) baseStart_8336893 baseEnd_8336893 := by
    simpa [prefixWord, tailWord_8336893, baseEnd_8336893] using wordTrace_append hprefix tailTrace_8336893
  have hstable : (prefixWord ++ tailWord_8336893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336893).length < 2 ^ (prefixWord ++ tailWord_8336893).sum := by decide
  have hdescent : baseEnd_8336893 < baseStart_8336893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336899 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_8336899 : Nat := 118140960795 + 8336899 * 2 ^ 59
def prefixEnd_8336899 : Nat := 4983230072969 + 3 ^ 40 * 8336899 * 2
def baseEnd_8336899 : Nat := 4280836354987882578021805

theorem tailTrace_8336899 : CollatzResearch.WordTrace tailWord_8336899 prefixEnd_8336899 4280836354987882578021805 := by
  unfold tailWord_8336899
  simp only [CollatzResearch.WordTrace]
  refine ⟨304071687023846226837493751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202714458015897484558329167 304071687023846226837493751)
  ·
    refine ⟨456107530535769340256240627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304071687023846226837493751 456107530535769340256240627)
    ·
      refine ⟨684161295803654010384360941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456107530535769340256240627 684161295803654010384360941)
      ·
        refine ⟨256560485926370253894135353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684161295803654010384360941 256560485926370253894135353)
        ·
          refine ⟨192420364444777690420601515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256560485926370253894135353 192420364444777690420601515)
          ·
            refine ⟨288630546667166535630902273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192420364444777690420601515 288630546667166535630902273)
            ·
              refine ⟨216472910000374901723176705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288630546667166535630902273 216472910000374901723176705)
              ·
                refine ⟨162354682500281176292382529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216472910000374901723176705 162354682500281176292382529)
                ·
                  refine ⟨121766011875210882219286897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162354682500281176292382529 121766011875210882219286897)
                  ·
                    refine ⟨91324508906408161664465173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121766011875210882219286897 91324508906408161664465173)
                    ·
                      refine ⟨4280836354987882578021805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91324508906408161664465173 4280836354987882578021805)
                      ·
                        rfl

theorem cell23_8336899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_8336899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336899 prefixEnd_8336899 := by exact prefixLift 8336899
  have htrace : WordTrace (prefixWord ++ tailWord_8336899) baseStart_8336899 baseEnd_8336899 := by
    simpa [prefixWord, tailWord_8336899, baseEnd_8336899] using wordTrace_append hprefix tailTrace_8336899
  have hstable : (prefixWord ++ tailWord_8336899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336899).length < 2 ^ (prefixWord ++ tailWord_8336899).sum := by decide
  have hdescent : baseEnd_8336899 < baseStart_8336899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8336976 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_8336976 : Nat := 118140960795 + 8336976 * 2 ^ 59
def prefixEnd_8336976 : Nat := 4983230072969 + 3 ^ 40 * 8336976 * 2
def baseEnd_8336976 : Nat := 4280875892998278776758951

theorem tailTrace_8336976 : CollatzResearch.WordTrace tailWord_8336976 prefixEnd_8336976 4280875892998278776758951 := by
  unfold tailWord_8336976
  simp only [CollatzResearch.WordTrace]
  refine ⟨152037247722283634494023391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202716330296378179325364521 152037247722283634494023391)
  ·
    refine ⟨228055871583425451741035087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152037247722283634494023391 228055871583425451741035087)
    ·
      refine ⟨342083807375138177611552631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228055871583425451741035087 342083807375138177611552631)
      ·
        refine ⟨513125711062707266417328947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342083807375138177611552631 513125711062707266417328947)
        ·
          refine ⟨769688566594060899625993421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513125711062707266417328947 769688566594060899625993421)
          ·
            refine ⟨288633212472772837359747533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769688566594060899625993421 288633212472772837359747533)
            ·
              refine ⟨108237454677289814009905325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288633212472772837359747533 108237454677289814009905325)
              ·
                refine ⟨40589045503983680253714497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108237454677289814009905325 40589045503983680253714497)
                ·
                  refine ⟨30441784127987760190285873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40589045503983680253714497 30441784127987760190285873)
                  ·
                    refine ⟨22831338095990820142714405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30441784127987760190285873 22831338095990820142714405)
                    ·
                      refine ⟨4280875892998278776758951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22831338095990820142714405 4280875892998278776758951)
                      ·
                        rfl

theorem cell23_8336976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_8336976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8336976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8336976 prefixEnd_8336976 := by exact prefixLift 8336976
  have htrace : WordTrace (prefixWord ++ tailWord_8336976) baseStart_8336976 baseEnd_8336976 := by
    simpa [prefixWord, tailWord_8336976, baseEnd_8336976] using wordTrace_append hprefix tailTrace_8336976
  have hstable : (prefixWord ++ tailWord_8336976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8336976).length < 2 ^ (prefixWord ++ tailWord_8336976).sum := by decide
  have hdescent : baseEnd_8336976 < baseStart_8336976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8336976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337137 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_8337137 : Nat := 118140960795 + 8337137 * 2 ^ 59
def prefixEnd_8337137 : Nat := 4983230072969 + 3 ^ 40 * 8337137 * 2
def baseEnd_8337137 : Nat := 4280958563383652646845711

theorem tailTrace_8337137 : CollatzResearch.WordTrace tailWord_8337137 prefixEnd_8337137 4280958563383652646845711 := by
  unfold tailWord_8337137
  simp only [CollatzResearch.WordTrace]
  refine ⟨304080367596983993484657665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202720245064655995656438443 304080367596983993484657665)
  ·
    refine ⟨228060275697737995113493249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304080367596983993484657665 228060275697737995113493249)
    ·
      refine ⟨171045206773303496335119937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228060275697737995113493249 171045206773303496335119937)
      ·
        refine ⟨128283905079977622251339953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171045206773303496335119937 128283905079977622251339953)
        ·
          refine ⟨96212928809983216688504965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128283905079977622251339953 96212928809983216688504965)
          ·
            refine ⟨18039924151871853129094681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96212928809983216688504965 18039924151871853129094681)
            ·
              refine ⟨13529943113903889846821011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18039924151871853129094681 13529943113903889846821011)
              ·
                refine ⟨20294914670855834770231517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529943113903889846821011 20294914670855834770231517)
                ·
                  refine ⟨7610593001570938038836819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20294914670855834770231517 7610593001570938038836819)
                  ·
                    refine ⟨11415889502356407058255229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610593001570938038836819 11415889502356407058255229)
                    ·
                      refine ⟨4280958563383652646845711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11415889502356407058255229 4280958563383652646845711)
                      ·
                        rfl

theorem cell23_8337137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_8337137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337137 prefixEnd_8337137 := by exact prefixLift 8337137
  have htrace : WordTrace (prefixWord ++ tailWord_8337137) baseStart_8337137 baseEnd_8337137 := by
    simpa [prefixWord, tailWord_8337137, baseEnd_8337137] using wordTrace_append hprefix tailTrace_8337137
  have hstable : (prefixWord ++ tailWord_8337137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337137).length < 2 ^ (prefixWord ++ tailWord_8337137).sum := by decide
  have hdescent : baseEnd_8337137 < baseStart_8337137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337143 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_8337143 : Nat := 118140960795 + 8337143 * 2 ^ 59
def prefixEnd_8337143 : Nat := 4983230072969 + 3 ^ 40 * 8337143 * 2
def baseEnd_8337143 : Nat := 4280961644267579623370683

theorem tailTrace_8337143 : CollatzResearch.WordTrace tailWord_8337143 prefixEnd_8337143 4280961644267579623370683 := by
  unfold tailWord_8337143
  simp only [CollatzResearch.WordTrace]
  refine ⟨304080586434962256509376083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202720390956641504339584055 304080586434962256509376083)
  ·
    refine ⟨456120879652443384764064125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304080586434962256509376083 456120879652443384764064125)
    ·
      refine ⟨171045329869666269286524047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456120879652443384764064125 171045329869666269286524047)
      ·
        refine ⟨256567994804499403929786071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171045329869666269286524047 256567994804499403929786071)
        ·
          refine ⟨384851992206749105894679107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256567994804499403929786071 384851992206749105894679107)
          ·
            refine ⟨577277988310123658842018661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384851992206749105894679107 577277988310123658842018661)
            ·
              refine ⟨108239622808148186032878499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577277988310123658842018661 108239622808148186032878499)
              ·
                refine ⟨162359434212222279049317749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108239622808148186032878499 162359434212222279049317749)
                ·
                  refine ⟨15221196957395838660873539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162359434212222279049317749 15221196957395838660873539)
                  ·
                    refine ⟨22831795436093757991310309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15221196957395838660873539 22831795436093757991310309)
                    ·
                      refine ⟨4280961644267579623370683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22831795436093757991310309 4280961644267579623370683)
                      ·
                        rfl

theorem cell23_8337143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_8337143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337143 prefixEnd_8337143 := by exact prefixLift 8337143
  have htrace : WordTrace (prefixWord ++ tailWord_8337143) baseStart_8337143 baseEnd_8337143 := by
    simpa [prefixWord, tailWord_8337143, baseEnd_8337143] using wordTrace_append hprefix tailTrace_8337143
  have hstable : (prefixWord ++ tailWord_8337143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337143).length < 2 ^ (prefixWord ++ tailWord_8337143).sum := by decide
  have hdescent : baseEnd_8337143 < baseStart_8337143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337160 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_8337160 : Nat := 118140960795 + 8337160 * 2 ^ 59
def prefixEnd_8337160 : Nat := 4983230072969 + 3 ^ 40 * 8337160 * 2
def baseEnd_8337160 : Nat := 4280970373438706056858105

theorem tailTrace_8337160 : CollatzResearch.WordTrace tailWord_8337160 prefixEnd_8337160 4280970373438706056858105 := by
  unfold tailWord_8337160
  simp only [CollatzResearch.WordTrace]
  refine ⟨152040603237950334206372467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202720804317267112275163289 152040603237950334206372467)
  ·
    refine ⟨228060904856925501309558701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152040603237950334206372467 228060904856925501309558701)
    ·
      refine ⟨85522839321347062991084513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228060904856925501309558701 85522839321347062991084513)
      ·
        refine ⟨64142129491010297243313385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85522839321347062991084513 64142129491010297243313385)
        ·
          refine ⟨48106597118257722932485039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64142129491010297243313385 48106597118257722932485039)
          ·
            refine ⟨72159895677386584398727559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48106597118257722932485039 72159895677386584398727559)
            ·
              refine ⟨108239843516079876598091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72159895677386584398727559 108239843516079876598091339)
              ·
                refine ⟨162359765274119814897137009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108239843516079876598091339 162359765274119814897137009)
                ·
                  refine ⟨121769823955589861172852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162359765274119814897137009 121769823955589861172852757)
                  ·
                    refine ⟨5707960497918274742477473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121769823955589861172852757 5707960497918274742477473)
                    ·
                      refine ⟨4280970373438706056858105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5707960497918274742477473 4280970373438706056858105)
                      ·
                        rfl

theorem cell23_8337160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_8337160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337160 prefixEnd_8337160 := by exact prefixLift 8337160
  have htrace : WordTrace (prefixWord ++ tailWord_8337160) baseStart_8337160 baseEnd_8337160 := by
    simpa [prefixWord, tailWord_8337160, baseEnd_8337160] using wordTrace_append hprefix tailTrace_8337160
  have hstable : (prefixWord ++ tailWord_8337160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337160).length < 2 ^ (prefixWord ++ tailWord_8337160).sum := by decide
  have hdescent : baseEnd_8337160 < baseStart_8337160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337180 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_8337180 : Nat := 118140960795 + 8337180 * 2 ^ 59
def prefixEnd_8337180 : Nat := 4983230072969 + 3 ^ 40 * 8337180 * 2
def baseEnd_8337180 : Nat := 4280980643051795978608013

theorem tailTrace_8337180 : CollatzResearch.WordTrace tailWord_8337180 prefixEnd_8337180 4280980643051795978608013 := by
  unfold tailWord_8337180
  simp only [CollatzResearch.WordTrace]
  refine ⟨152040967967914105914236497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202721290623885474552315329 152040967967914105914236497)
  ·
    refine ⟨114030725975935579435677373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152040967967914105914236497 114030725975935579435677373)
    ·
      refine ⟨42761522240975842288379015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114030725975935579435677373 42761522240975842288379015)
      ·
        refine ⟨64142283361463763432568523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42761522240975842288379015 64142283361463763432568523)
        ·
          refine ⟨96213425042195645148852785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64142283361463763432568523 96213425042195645148852785)
          ·
            refine ⟨72160068781646733861639589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96213425042195645148852785 72160068781646733861639589)
            ·
              refine ⟨13530012896558762599057423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72160068781646733861639589 13530012896558762599057423)
              ·
                refine ⟨20295019344838143898586135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13530012896558762599057423 20295019344838143898586135)
                ·
                  refine ⟨30442529017257215847879203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20295019344838143898586135 30442529017257215847879203)
                  ·
                    refine ⟨45663793525885823771818805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30442529017257215847879203 45663793525885823771818805)
                    ·
                      refine ⟨4280980643051795978608013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45663793525885823771818805 4280980643051795978608013)
                      ·
                        rfl

theorem cell23_8337180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_8337180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337180 prefixEnd_8337180 := by exact prefixLift 8337180
  have htrace : WordTrace (prefixWord ++ tailWord_8337180) baseStart_8337180 baseEnd_8337180 := by
    simpa [prefixWord, tailWord_8337180, baseEnd_8337180] using wordTrace_append hprefix tailTrace_8337180
  have hstable : (prefixWord ++ tailWord_8337180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337180).length < 2 ^ (prefixWord ++ tailWord_8337180).sum := by decide
  have hdescent : baseEnd_8337180 < baseStart_8337180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337193 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_8337193 : Nat := 118140960795 + 8337193 * 2 ^ 59
def prefixEnd_8337193 : Nat := 4983230072969 + 3 ^ 40 * 8337193 * 2
def baseEnd_8337193 : Nat := 4280987318300304427745453

theorem tailTrace_8337193 : CollatzResearch.WordTrace tailWord_8337193 prefixEnd_8337193 4280987318300304427745453 := by
  unfold tailWord_8337193
  simp only [CollatzResearch.WordTrace]
  refine ⟨304082410084781115048696233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202721606723187410032464155 304082410084781115048696233)
  ·
    refine ⟨228061807563585836286522175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304082410084781115048696233 228061807563585836286522175)
    ·
      refine ⟨342092711345378754429783263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228061807563585836286522175 342092711345378754429783263)
      ·
        refine ⟨513139067018068131644674895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342092711345378754429783263 513139067018068131644674895)
        ·
          refine ⟨769708600527102197467012343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513139067018068131644674895 769708600527102197467012343)
          ·
            refine ⟨1154562900790653296200518515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769708600527102197467012343 1154562900790653296200518515)
            ·
              refine ⟨1731844351185979944300777773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154562900790653296200518515 1731844351185979944300777773)
              ·
                refine ⟨649441631694742479112791665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1731844351185979944300777773 649441631694742479112791665)
                ·
                  refine ⟨487081223771056859334593749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649441631694742479112791665 487081223771056859334593749)
                  ·
                    refine ⟨11415966182134145140654541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 487081223771056859334593749 11415966182134145140654541)
                    ·
                      refine ⟨4280987318300304427745453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11415966182134145140654541 4280987318300304427745453)
                      ·
                        rfl

theorem cell23_8337193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_8337193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337193 prefixEnd_8337193 := by exact prefixLift 8337193
  have htrace : WordTrace (prefixWord ++ tailWord_8337193) baseStart_8337193 baseEnd_8337193 := by
    simpa [prefixWord, tailWord_8337193, baseEnd_8337193] using wordTrace_append hprefix tailTrace_8337193
  have hstable : (prefixWord ++ tailWord_8337193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337193).length < 2 ^ (prefixWord ++ tailWord_8337193).sum := by decide
  have hdescent : baseEnd_8337193 < baseStart_8337193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337204 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_8337204 : Nat := 118140960795 + 8337204 * 2 ^ 59
def prefixEnd_8337204 : Nat := 4983230072969 + 3 ^ 40 * 8337204 * 2
def baseEnd_8337204 : Nat := 1426997655529167961569301

theorem tailTrace_8337204 : CollatzResearch.WordTrace tailWord_8337204 prefixEnd_8337204 1426997655529167961569301 := by
  unfold tailWord_8337204
  simp only [CollatzResearch.WordTrace]
  refine ⟨152041405643870631963673333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202721874191827509284897777 152041405643870631963673333)
  ·
    refine ⟨14253881779112871746594375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152041405643870631963673333 14253881779112871746594375)
    ·
      refine ⟨21380822668669307619891563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253881779112871746594375 21380822668669307619891563)
      ·
        refine ⟨32071234003003961429837345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21380822668669307619891563 32071234003003961429837345)
        ·
          refine ⟨24053425502252971072378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32071234003003961429837345 24053425502252971072378009)
          ·
            refine ⟨18040069126689728304283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24053425502252971072378009 18040069126689728304283507)
            ·
              refine ⟨27060103690034592456425261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18040069126689728304283507 27060103690034592456425261)
              ·
                refine ⟨10147538883762972171159473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27060103690034592456425261 10147538883762972171159473)
                ·
                  refine ⟨7610654162822229128369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10147538883762972171159473 7610654162822229128369605)
                  ·
                    refine ⟨1426997655529167961569301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7610654162822229128369605 1426997655529167961569301)
                    ·
                      rfl

theorem cell23_8337204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_8337204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337204 prefixEnd_8337204 := by exact prefixLift 8337204
  have htrace : WordTrace (prefixWord ++ tailWord_8337204) baseStart_8337204 baseEnd_8337204 := by
    simpa [prefixWord, tailWord_8337204, baseEnd_8337204] using wordTrace_append hprefix tailTrace_8337204
  have hstable : (prefixWord ++ tailWord_8337204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337204).length < 2 ^ (prefixWord ++ tailWord_8337204).sum := by decide
  have hdescent : baseEnd_8337204 < baseStart_8337204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337214 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_8337214 : Nat := 118140960795 + 8337214 * 2 ^ 59
def prefixEnd_8337214 : Nat := 4983230072969 + 3 ^ 40 * 8337214 * 2
def baseEnd_8337214 : Nat := 4280998101394048845582857

theorem tailTrace_8337214 : CollatzResearch.WordTrace tailWord_8337214 prefixEnd_8337214 4280998101394048845582857 := by
  unfold tailWord_8337214
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010397002213129454401337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202722117345136690423473797 38010397002213129454401337)
  ·
    refine ⟨28507797751659847090801003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38010397002213129454401337 28507797751659847090801003)
    ·
      refine ⟨42761696627489770636201505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28507797751659847090801003 42761696627489770636201505)
      ·
        refine ⟨32071272470617327977151129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42761696627489770636201505 32071272470617327977151129)
        ·
          refine ⟨24053454352962995982863347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32071272470617327977151129 24053454352962995982863347)
          ·
            refine ⟨36080181529444493974295021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24053454352962995982863347 36080181529444493974295021)
            ·
              refine ⟨13530068073541685240360633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36080181529444493974295021 13530068073541685240360633)
              ·
                refine ⟨10147551055156263930270475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13530068073541685240360633 10147551055156263930270475)
                ·
                  refine ⟨15221326582734395895405713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10147551055156263930270475 15221326582734395895405713)
                  ·
                    refine ⟨11415994937050796921554285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15221326582734395895405713 11415994937050796921554285)
                    ·
                      refine ⟨4280998101394048845582857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11415994937050796921554285 4280998101394048845582857)
                      ·
                        rfl

theorem cell23_8337214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_8337214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337214 prefixEnd_8337214 := by exact prefixLift 8337214
  have htrace : WordTrace (prefixWord ++ tailWord_8337214) baseStart_8337214 baseEnd_8337214 := by
    simpa [prefixWord, tailWord_8337214, baseEnd_8337214] using wordTrace_append hprefix tailTrace_8337214
  have hstable : (prefixWord ++ tailWord_8337214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337214).length < 2 ^ (prefixWord ++ tailWord_8337214).sum := by decide
  have hdescent : baseEnd_8337214 < baseStart_8337214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337223 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_8337223 : Nat := 118140960795 + 8337223 * 2 ^ 59
def prefixEnd_8337223 : Nat := 4983230072969 + 3 ^ 40 * 8337223 * 2
def baseEnd_8337223 : Nat := 4281002722719939310370315

theorem tailTrace_8337223 : CollatzResearch.WordTrace tailWord_8337223 prefixEnd_8337223 4281002722719939310370315 := by
  unfold tailWord_8337223
  simp only [CollatzResearch.WordTrace]
  refine ⟨304083504274672430172288323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202722336183114953448192215 304083504274672430172288323)
  ·
    refine ⟨456125256412008645258432485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304083504274672430172288323 456125256412008645258432485)
    ·
      refine ⟨85523485577251620985956091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456125256412008645258432485 85523485577251620985956091)
      ·
        refine ⟨128285228365877431478934137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85523485577251620985956091 128285228365877431478934137)
        ·
          refine ⟨96213921274408073609200603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128285228365877431478934137 96213921274408073609200603)
          ·
            refine ⟨144320881911612110413800905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96213921274408073609200603 144320881911612110413800905)
            ·
              refine ⟨108240661433709082810350679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144320881911612110413800905 108240661433709082810350679)
              ·
                refine ⟨162360992150563624215526019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108240661433709082810350679 162360992150563624215526019)
                ·
                  refine ⟨243541488225845436323289029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162360992150563624215526019 243541488225845436323289029)
                  ·
                    refine ⟨45664029042346019310616693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243541488225845436323289029 45664029042346019310616693)
                    ·
                      refine ⟨4281002722719939310370315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45664029042346019310616693 4281002722719939310370315)
                      ·
                        rfl

theorem cell23_8337223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_8337223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337223 prefixEnd_8337223 := by exact prefixLift 8337223
  have htrace : WordTrace (prefixWord ++ tailWord_8337223) baseStart_8337223 baseEnd_8337223 := by
    simpa [prefixWord, tailWord_8337223, baseEnd_8337223] using wordTrace_append hprefix tailTrace_8337223
  have hstable : (prefixWord ++ tailWord_8337223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337223).length < 2 ^ (prefixWord ++ tailWord_8337223).sum := by decide
  have hdescent : baseEnd_8337223 < baseStart_8337223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337260 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_8337260 : Nat := 118140960795 + 8337260 * 2 ^ 59
def prefixEnd_8337260 : Nat := 4983230072969 + 3 ^ 40 * 8337260 * 2
def baseEnd_8337260 : Nat := 1427007240501385221869215

theorem tailTrace_8337260 : CollatzResearch.WordTrace tailWord_8337260 prefixEnd_8337260 1427007240501385221869215 := by
  unfold tailWord_8337260
  simp only [CollatzResearch.WordTrace]
  refine ⟨152042426887769192745692617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202723235850358923660923489 152042426887769192745692617)
  ·
    refine ⟨114031820165826894559269463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152042426887769192745692617 114031820165826894559269463)
    ·
      refine ⟨171047730248740341838904195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114031820165826894559269463 171047730248740341838904195)
      ·
        refine ⟨256571595373110512758356293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171047730248740341838904195 256571595373110512758356293)
        ·
          refine ⟨48107174132458221142191805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256571595373110512758356293 48107174132458221142191805)
          ·
            refine ⟨18040190299671832928321927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48107174132458221142191805 18040190299671832928321927)
            ·
              refine ⟨27060285449507749392482891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18040190299671832928321927 27060285449507749392482891)
              ·
                refine ⟨40590428174261624088724337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27060285449507749392482891 40590428174261624088724337)
                ·
                  refine ⟨30442821130696218066543253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40590428174261624088724337 30442821130696218066543253)
                  ·
                    refine ⟨1427007240501385221869215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30442821130696218066543253 1427007240501385221869215)
                    ·
                      rfl

theorem cell23_8337260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_8337260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337260 prefixEnd_8337260 := by exact prefixLift 8337260
  have htrace : WordTrace (prefixWord ++ tailWord_8337260) baseStart_8337260 baseEnd_8337260 := by
    simpa [prefixWord, tailWord_8337260, baseEnd_8337260] using wordTrace_append hprefix tailTrace_8337260
  have hstable : (prefixWord ++ tailWord_8337260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337260).length < 2 ^ (prefixWord ++ tailWord_8337260).sum := by decide
  have hdescent : baseEnd_8337260 < baseStart_8337260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337267 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 6, 2, 2]
def baseStart_8337267 : Nat := 118140960795 + 8337267 * 2 ^ 59
def prefixEnd_8337267 : Nat := 4983230072969 + 3 ^ 40 * 8337267 * 2
def baseEnd_8337267 : Nat := 4281025315868737138220113

theorem tailTrace_8337267 : CollatzResearch.WordTrace tailWord_8337267 prefixEnd_8337267 4281025315868737138220113 := by
  unfold tailWord_8337267
  simp only [CollatzResearch.WordTrace]
  refine ⟨304085109086513025686890055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202723406057675350457926703 304085109086513025686890055)
  ·
    refine ⟨456127663629769538530335083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304085109086513025686890055 456127663629769538530335083)
    ·
      refine ⟨684191495444654307795502625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456127663629769538530335083 684191495444654307795502625)
      ·
        refine ⟨513143621583490730846626969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684191495444654307795502625 513143621583490730846626969)
        ·
          refine ⟨384857716187618048134970227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513143621583490730846626969 384857716187618048134970227)
          ·
            refine ⟨577286574281427072202455341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384857716187618048134970227 577286574281427072202455341)
            ·
              refine ⟨216482465355535152075920753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577286574281427072202455341 216482465355535152075920753)
              ·
                refine ⟨162361849016651364056940565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216482465355535152075920753 162361849016651364056940565)
                ·
                  refine ⟨7610711672655532690169089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162361849016651364056940565 7610711672655532690169089)
                  ·
                    refine ⟨5708033754491649517626817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7610711672655532690169089 5708033754491649517626817)
                    ·
                      refine ⟨4281025315868737138220113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708033754491649517626817 4281025315868737138220113)
                      ·
                        rfl

theorem cell23_8337267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2, 2].length) (baseStart_8337267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337267 prefixEnd_8337267 := by exact prefixLift 8337267
  have htrace : WordTrace (prefixWord ++ tailWord_8337267) baseStart_8337267 baseEnd_8337267 := by
    simpa [prefixWord, tailWord_8337267, baseEnd_8337267] using wordTrace_append hprefix tailTrace_8337267
  have hstable : (prefixWord ++ tailWord_8337267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337267).length < 2 ^ (prefixWord ++ tailWord_8337267).sum := by decide
  have hdescent : baseEnd_8337267 < baseStart_8337267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337288 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_8337288 : Nat := 118140960795 + 8337288 * 2 ^ 59
def prefixEnd_8337288 : Nat := 4983230072969 + 3 ^ 40 * 8337288 * 2
def baseEnd_8337288 : Nat := 4281036098962481556057517

theorem tailTrace_8337288 : CollatzResearch.WordTrace tailWord_8337288 prefixEnd_8337288 4281036098962481556057517 := by
  unfold tailWord_8337288
  simp only [CollatzResearch.WordTrace]
  refine ⟨152042937509718473136702259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202723916679624630848936345 152042937509718473136702259)
  ·
    refine ⟨228064406264577709705053389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152042937509718473136702259 228064406264577709705053389)
    ·
      refine ⟨85524152349216641139395021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228064406264577709705053389 85524152349216641139395021)
      ·
        refine ⟨32071557130956240427273133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85524152349216641139395021 32071557130956240427273133)
        ·
          refine ⟨12026833924108590160227425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32071557130956240427273133 12026833924108590160227425)
          ·
            refine ⟨9020125443081442620170569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026833924108590160227425 9020125443081442620170569)
            ·
              refine ⟨6765094082311081965127927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020125443081442620170569 6765094082311081965127927)
              ·
                refine ⟨10147641123466622947691891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765094082311081965127927 10147641123466622947691891)
                ·
                  refine ⟨15221461685199934421537837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10147641123466622947691891 15221461685199934421537837)
                  ·
                    refine ⟨5708048131949975408076689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15221461685199934421537837 5708048131949975408076689)
                    ·
                      refine ⟨4281036098962481556057517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708048131949975408076689 4281036098962481556057517)
                      ·
                        rfl

theorem cell23_8337288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_8337288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337288 prefixEnd_8337288 := by exact prefixLift 8337288
  have htrace : WordTrace (prefixWord ++ tailWord_8337288) baseStart_8337288 baseEnd_8337288 := by
    simpa [prefixWord, tailWord_8337288, baseEnd_8337288] using wordTrace_append hprefix tailTrace_8337288
  have hstable : (prefixWord ++ tailWord_8337288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337288).length < 2 ^ (prefixWord ++ tailWord_8337288).sum := by decide
  have hdescent : baseEnd_8337288 < baseStart_8337288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337417 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 5, 2]
def baseStart_8337417 : Nat := 118140960795 + 8337417 * 2 ^ 59
def prefixEnd_8337417 : Nat := 4983230072969 + 3 ^ 40 * 8337417 * 2
def baseEnd_8337417 : Nat := 4281102337966911551344423

theorem tailTrace_8337417 : CollatzResearch.WordTrace tailWord_8337417 prefixEnd_8337417 4281102337966911551344423 := by
  unfold tailWord_8337417
  simp only [CollatzResearch.WordTrace]
  refine ⟨304090580035969601304850505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202727053357313067536567003 304090580035969601304850505)
  ·
    refine ⟨228067935026977200978637879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304090580035969601304850505 228067935026977200978637879)
    ·
      refine ⟨342101902540465801467956819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228067935026977200978637879 342101902540465801467956819)
      ·
        refine ⟨513152853810698702201935229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342101902540465801467956819 513152853810698702201935229)
        ·
          refine ⟨192432320179012013325725711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513152853810698702201935229 192432320179012013325725711)
          ·
            refine ⟨288648480268518019988588567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192432320179012013325725711 288648480268518019988588567)
            ·
              refine ⟨432972720402777029982882851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288648480268518019988588567 432972720402777029982882851)
              ·
                refine ⟨649459080604165544974324277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432972720402777029982882851 649459080604165544974324277)
                ·
                  refine ⟨60886788806640519841342901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649459080604165544974324277 60886788806640519841342901)
                  ·
                    refine ⟨5708136450622548735125897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60886788806640519841342901 5708136450622548735125897)
                    ·
                      refine ⟨4281102337966911551344423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708136450622548735125897 4281102337966911551344423)
                      ·
                        rfl

theorem cell23_8337417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5, 2].length) (baseStart_8337417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337417 prefixEnd_8337417 := by exact prefixLift 8337417
  have htrace : WordTrace (prefixWord ++ tailWord_8337417) baseStart_8337417 baseEnd_8337417 := by
    simpa [prefixWord, tailWord_8337417, baseEnd_8337417] using wordTrace_append hprefix tailTrace_8337417
  have hstable : (prefixWord ++ tailWord_8337417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337417).length < 2 ^ (prefixWord ++ tailWord_8337417).sum := by decide
  have hdescent : baseEnd_8337417 < baseStart_8337417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337441 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_8337441 : Nat := 118140960795 + 8337441 * 2 ^ 59
def prefixEnd_8337441 : Nat := 4983230072969 + 3 ^ 40 * 8337441 * 2
def baseEnd_8337441 : Nat := 4281114661502619457444313

theorem tailTrace_8337441 : CollatzResearch.WordTrace tailWord_8337441 prefixEnd_8337441 4281114661502619457444313 := by
  unfold tailWord_8337441
  simp only [CollatzResearch.WordTrace]
  refine ⟨304091455387882653403724177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202727636925255102269149451 304091455387882653403724177)
  ·
    refine ⟨228068591540911990052793133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304091455387882653403724177 228068591540911990052793133)
    ·
      refine ⟨85525721827841996269797425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228068591540911990052793133 85525721827841996269797425)
      ·
        refine ⟨64144291370881497202348069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85525721827841996269797425 64144291370881497202348069)
        ·
          refine ⟨12027054632040280725440263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64144291370881497202348069 12027054632040280725440263)
          ·
            refine ⟨18040581948060421088160395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12027054632040280725440263 18040581948060421088160395)
            ·
              refine ⟨27060872922090631632240593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18040581948060421088160395 27060872922090631632240593)
              ·
                refine ⟨20295654691567973724180445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27060872922090631632240593 20295654691567973724180445)
                ·
                  refine ⟨7610870509337990146567667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20295654691567973724180445 7610870509337990146567667)
                  ·
                    refine ⟨11416305764006985219851501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610870509337990146567667 11416305764006985219851501)
                    ·
                      refine ⟨4281114661502619457444313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416305764006985219851501 4281114661502619457444313)
                      ·
                        rfl

theorem cell23_8337441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_8337441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337441 prefixEnd_8337441 := by exact prefixLift 8337441
  have htrace : WordTrace (prefixWord ++ tailWord_8337441) baseStart_8337441 baseEnd_8337441 := by
    simpa [prefixWord, tailWord_8337441, baseEnd_8337441] using wordTrace_append hprefix tailTrace_8337441
  have hstable : (prefixWord ++ tailWord_8337441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337441).length < 2 ^ (prefixWord ++ tailWord_8337441).sum := by decide
  have hdescent : baseEnd_8337441 < baseStart_8337441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337457 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_8337457 : Nat := 118140960795 + 8337457 * 2 ^ 59
def prefixEnd_8337457 : Nat := 4983230072969 + 3 ^ 40 * 8337457 * 2
def baseEnd_8337457 : Nat := 1427040959064363798281413

theorem tailTrace_8337457 : CollatzResearch.WordTrace tailWord_8337457 prefixEnd_8337457 1427040959064363798281413 := by
  unfold tailWord_8337457
  simp only [CollatzResearch.WordTrace]
  refine ⟨304092038955824688136306625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202728025970549792090871083 304092038955824688136306625)
  ·
    refine ⟨228069029216868516102229969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304092038955824688136306625 228069029216868516102229969)
    ·
      refine ⟨171051771912651387076672477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228069029216868516102229969 171051771912651387076672477)
      ·
        refine ⟨64144414467244270153752179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171051771912651387076672477 64144414467244270153752179)
        ·
          refine ⟨96216621700866405230628269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64144414467244270153752179 96216621700866405230628269)
          ·
            refine ⟨36081233137824901961485601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96216621700866405230628269 36081233137824901961485601)
            ·
              refine ⟨27060924853368676471114201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36081233137824901961485601 27060924853368676471114201)
              ·
                refine ⟨20295693640026507353335651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27060924853368676471114201 20295693640026507353335651)
                ·
                  refine ⟨30443540460039761030003477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20295693640026507353335651 30443540460039761030003477)
                  ·
                    refine ⟨1427040959064363798281413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30443540460039761030003477 1427040959064363798281413)
                    ·
                      rfl

theorem cell23_8337457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_8337457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337457 prefixEnd_8337457 := by exact prefixLift 8337457
  have htrace : WordTrace (prefixWord ++ tailWord_8337457) baseStart_8337457 baseEnd_8337457 := by
    simpa [prefixWord, tailWord_8337457, baseEnd_8337457] using wordTrace_append hprefix tailTrace_8337457
  have hstable : (prefixWord ++ tailWord_8337457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337457).length < 2 ^ (prefixWord ++ tailWord_8337457).sum := by decide
  have hdescent : baseEnd_8337457 < baseStart_8337457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337458 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_8337458 : Nat := 118140960795 + 8337458 * 2 ^ 59
def prefixEnd_8337458 : Nat := 4983230072969 + 3 ^ 40 * 8337458 * 2
def baseEnd_8337458 : Nat := 4281123390673745890931735

theorem tailTrace_8337458 : CollatzResearch.WordTrace tailWord_8337458 prefixEnd_8337458 4281123390673745890931735 := by
  unfold tailWord_8337458
  simp only [CollatzResearch.WordTrace]
  refine ⟨76023018857205266326773257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202728050285880710204728685 76023018857205266326773257)
  ·
    refine ⟨57017264142903949745079943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76023018857205266326773257 57017264142903949745079943)
    ·
      refine ⟨85525896214355924617619915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57017264142903949745079943 85525896214355924617619915)
      ·
        refine ⟨128288844321533886926429873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85525896214355924617619915 128288844321533886926429873)
        ·
          refine ⟨96216633241150415194822405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128288844321533886926429873 96216633241150415194822405)
          ·
            refine ⟨18040618732715702849029201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96216633241150415194822405 18040618732715702849029201)
            ·
              refine ⟨13530464049536777136771901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18040618732715702849029201 13530464049536777136771901)
              ·
                refine ⟨5073924018576291426289463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13530464049536777136771901 5073924018576291426289463)
                ·
                  refine ⟨7610886027864437139434195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073924018576291426289463 7610886027864437139434195)
                  ·
                    refine ⟨11416329041796655709151293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610886027864437139434195 11416329041796655709151293)
                    ·
                      refine ⟨4281123390673745890931735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416329041796655709151293 4281123390673745890931735)
                      ·
                        rfl

theorem cell23_8337458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_8337458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337458 prefixEnd_8337458 := by exact prefixLift 8337458
  have htrace : WordTrace (prefixWord ++ tailWord_8337458) baseStart_8337458 baseEnd_8337458 := by
    simpa [prefixWord, tailWord_8337458, baseEnd_8337458] using wordTrace_append hprefix tailTrace_8337458
  have hstable : (prefixWord ++ tailWord_8337458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337458).length < 2 ^ (prefixWord ++ tailWord_8337458).sum := by decide
  have hdescent : baseEnd_8337458 < baseStart_8337458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337481 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 3, 2, 2]
def baseStart_8337481 : Nat := 118140960795 + 8337481 * 2 ^ 59
def prefixEnd_8337481 : Nat := 4983230072969 + 3 ^ 40 * 8337481 * 2
def baseEnd_8337481 : Nat := 4281135200728799300944129

theorem tailTrace_8337481 : CollatzResearch.WordTrace tailWord_8337481 prefixEnd_8337481 4281135200728799300944129 := by
  unfold tailWord_8337481
  simp only [CollatzResearch.WordTrace]
  refine ⟨304092914307737740235180297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202728609538491826823453531 304092914307737740235180297)
  ·
    refine ⟨228069685730803305176385223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304092914307737740235180297 228069685730803305176385223)
    ·
      refine ⟨342104528596204957764577835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228069685730803305176385223 342104528596204957764577835)
      ·
        refine ⟨513156792894307436646866753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342104528596204957764577835 513156792894307436646866753)
        ·
          refine ⟨384867594670730577485150065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513156792894307436646866753 384867594670730577485150065)
          ·
            refine ⟨288650696003047933113862549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384867594670730577485150065 288650696003047933113862549)
            ·
              refine ⟨13530501375142871864712307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288650696003047933113862549 13530501375142871864712307)
              ·
                refine ⟨20295752062714307797068461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13530501375142871864712307 20295752062714307797068461)
                ·
                  refine ⟨7610907023517865423900673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20295752062714307797068461 7610907023517865423900673)
                  ·
                    refine ⟨5708180267638399067925505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7610907023517865423900673 5708180267638399067925505)
                    ·
                      refine ⟨4281135200728799300944129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708180267638399067925505 4281135200728799300944129)
                      ·
                        rfl

theorem cell23_8337481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2, 2].length) (baseStart_8337481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337481 prefixEnd_8337481 := by exact prefixLift 8337481
  have htrace : WordTrace (prefixWord ++ tailWord_8337481) baseStart_8337481 baseEnd_8337481 := by
    simpa [prefixWord, tailWord_8337481, baseEnd_8337481] using wordTrace_append hprefix tailTrace_8337481
  have hstable : (prefixWord ++ tailWord_8337481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337481).length < 2 ^ (prefixWord ++ tailWord_8337481).sum := by decide
  have hdescent : baseEnd_8337481 < baseStart_8337481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337504 : List Nat := [2, 1, 1, 3, 2, 5, 2, 7]
def baseStart_8337504 : Nat := 118140960795 + 8337504 * 2 ^ 59
def prefixEnd_8337504 : Nat := 4983230072969 + 3 ^ 40 * 8337504 * 2
def baseEnd_8337504 : Nat := 158561000399401952257649

theorem tailTrace_8337504 : CollatzResearch.WordTrace tailWord_8337504 prefixEnd_8337504 158561000399401952257649 := by
  unfold tailWord_8337504
  simp only [CollatzResearch.WordTrace]
  refine ⟨152046876593327207581633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202729168791102943442178377 152046876593327207581633783)
  ·
    refine ⟨228070314889990811372450675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152046876593327207581633783 228070314889990811372450675)
    ·
      refine ⟨342105472334986217058676013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228070314889990811372450675 342105472334986217058676013)
      ·
        refine ⟨128289552125619831397003505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342105472334986217058676013 128289552125619831397003505)
        ·
          refine ⟨96217164094214873547752629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128289552125619831397003505 96217164094214873547752629)
          ·
            refine ⟨9020359133832644395101809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96217164094214873547752629 9020359133832644395101809)
            ·
              refine ⟨6765269350374483296326357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020359133832644395101809 6765269350374483296326357)
              ·
                refine ⟨158561000399401952257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6765269350374483296326357 158561000399401952257649)
                ·
                  rfl

theorem cell23_8337504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 7].length) (baseStart_8337504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337504 prefixEnd_8337504 := by exact prefixLift 8337504
  have htrace : WordTrace (prefixWord ++ tailWord_8337504) baseStart_8337504 baseEnd_8337504 := by
    simpa [prefixWord, tailWord_8337504, baseEnd_8337504] using wordTrace_append hprefix tailTrace_8337504
  have hstable : (prefixWord ++ tailWord_8337504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337504).length < 2 ^ (prefixWord ++ tailWord_8337504).sum := by decide
  have hdescent : baseEnd_8337504 < baseStart_8337504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337557 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_8337557 : Nat := 118140960795 + 8337557 * 2 ^ 59
def prefixEnd_8337557 : Nat := 4983230072969 + 3 ^ 40 * 8337557 * 2
def baseEnd_8337557 : Nat := 4281174225258541003593779

theorem tailTrace_8337557 : CollatzResearch.WordTrace tailWord_8337557 prefixEnd_8337557 4281174225258541003593779 := by
  unfold tailWord_8337557
  simp only [CollatzResearch.WordTrace]
  refine ⟨304095686255462405214946925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202730457503641603476631283 304095686255462405214946925)
  ·
    refine ⟨114035882345798401955605097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304095686255462405214946925 114035882345798401955605097)
    ·
      refine ⟨85526911759348801466703823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114035882345798401955605097 85526911759348801466703823)
      ·
        refine ⟨128290367639023202200055735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85526911759348801466703823 128290367639023202200055735)
        ·
          refine ⟨192435551458534803300083603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128290367639023202200055735 192435551458534803300083603)
          ·
            refine ⟨288653327187802204950125405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192435551458534803300083603 288653327187802204950125405)
            ·
              refine ⟨108244997695425826856297027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288653327187802204950125405 108244997695425826856297027)
              ·
                refine ⟨162367496543138740284445541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108244997695425826856297027 162367496543138740284445541)
                ·
                  refine ⟨30443905601838513803333539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162367496543138740284445541 30443905601838513803333539)
                  ·
                    refine ⟨45665858402757770705000309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30443905601838513803333539 45665858402757770705000309)
                    ·
                      refine ⟨4281174225258541003593779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45665858402757770705000309 4281174225258541003593779)
                      ·
                        rfl

theorem cell23_8337557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_8337557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337557 prefixEnd_8337557 := by exact prefixLift 8337557
  have htrace : WordTrace (prefixWord ++ tailWord_8337557) baseStart_8337557 baseEnd_8337557 := by
    simpa [prefixWord, tailWord_8337557, baseEnd_8337557] using wordTrace_append hprefix tailTrace_8337557
  have hstable : (prefixWord ++ tailWord_8337557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337557).length < 2 ^ (prefixWord ++ tailWord_8337557).sum := by decide
  have hdescent : baseEnd_8337557 < baseStart_8337557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337582 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8337582 : Nat := 118140960795 + 8337582 * 2 ^ 59
def prefixEnd_8337582 : Nat := 4983230072969 + 3 ^ 40 * 8337582 * 2
def baseEnd_8337582 : Nat := 4281187062274903405781165

theorem tailTrace_8337582 : CollatzResearch.WordTrace tailWord_8337582 prefixEnd_8337582 4281187062274903405781165 := by
  unfold tailWord_8337582
  simp only [CollatzResearch.WordTrace]
  refine ⟨38012074760046479310575875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202731065386914556323071333 38012074760046479310575875)
  ·
    refine ⟨57018112140069718965863813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38012074760046479310575875 57018112140069718965863813)
    ·
      refine ⟨10690896026263072306099465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57018112140069718965863813 10690896026263072306099465)
      ·
        refine ⟨8018172019697304229574599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10690896026263072306099465 8018172019697304229574599)
        ·
          refine ⟨12027258029545956344361899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018172019697304229574599 12027258029545956344361899)
          ·
            refine ⟨18040887044318934516542849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12027258029545956344361899 18040887044318934516542849)
            ·
              refine ⟨13530665283239200887407137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18040887044318934516542849 13530665283239200887407137)
              ·
                refine ⟨10147998962429400665555353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13530665283239200887407137 10147998962429400665555353)
                ·
                  refine ⟨7610999221822050499166515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10147998962429400665555353 7610999221822050499166515)
                  ·
                    refine ⟨11416498832733075748749773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610999221822050499166515 11416498832733075748749773)
                    ·
                      refine ⟨4281187062274903405781165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416498832733075748749773 4281187062274903405781165)
                      ·
                        rfl

theorem cell23_8337582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8337582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337582 prefixEnd_8337582 := by exact prefixLift 8337582
  have htrace : WordTrace (prefixWord ++ tailWord_8337582) baseStart_8337582 baseEnd_8337582 := by
    simpa [prefixWord, tailWord_8337582, baseEnd_8337582] using wordTrace_append hprefix tailTrace_8337582
  have hstable : (prefixWord ++ tailWord_8337582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337582).length < 2 ^ (prefixWord ++ tailWord_8337582).sum := by decide
  have hdescent : baseEnd_8337582 < baseStart_8337582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_8337597 : Nat := 118140960795 + 8337597 * 2 ^ 59
def prefixEnd_8337597 : Nat := 4983230072969 + 3 ^ 40 * 8337597 * 2
def baseEnd_8337597 : Nat := 4281194764484720847093595

theorem tailTrace_8337597 : CollatzResearch.WordTrace tailWord_8337597 prefixEnd_8337597 4281194764484720847093595 := by
  unfold tailWord_8337597
  simp only [CollatzResearch.WordTrace]
  refine ⟨304097145175317492046403045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202731430116878328030935363 304097145175317492046403045)
  ·
    refine ⟨57018214720372029758700571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304097145175317492046403045 57018214720372029758700571)
    ·
      refine ⟨85527322080558044638050857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57018214720372029758700571 85527322080558044638050857)
      ·
        refine ⟨64145491560418533478538143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85527322080558044638050857 64145491560418533478538143)
        ·
          refine ⟨96218237340627800217807215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64145491560418533478538143 96218237340627800217807215)
          ·
            refine ⟨144327356010941700326710823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96218237340627800217807215 144327356010941700326710823)
            ·
              refine ⟨216491034016412550490066235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144327356010941700326710823 216491034016412550490066235)
              ·
                refine ⟨324736551024618825735099353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216491034016412550490066235 324736551024618825735099353)
                ·
                  refine ⟨243552413268464119301324515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324736551024618825735099353 243552413268464119301324515)
                  ·
                    refine ⟨365328619902696178951986773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243552413268464119301324515 365328619902696178951986773)
                    ·
                      refine ⟨4281194764484720847093595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365328619902696178951986773 4281194764484720847093595)
                      ·
                        rfl

theorem cell23_8337597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_8337597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337597 prefixEnd_8337597 := by exact prefixLift 8337597
  have htrace : WordTrace (prefixWord ++ tailWord_8337597) baseStart_8337597 baseEnd_8337597 := by
    simpa [prefixWord, tailWord_8337597, baseEnd_8337597] using wordTrace_append hprefix tailTrace_8337597
  have hstable : (prefixWord ++ tailWord_8337597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337597).length < 2 ^ (prefixWord ++ tailWord_8337597).sum := by decide
  have hdescent : baseEnd_8337597 < baseStart_8337597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337617 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_8337617 : Nat := 118140960795 + 8337617 * 2 ^ 59
def prefixEnd_8337617 : Nat := 4983230072969 + 3 ^ 40 * 8337617 * 2
def baseEnd_8337617 : Nat := 4281205034097810768843503

theorem tailTrace_8337617 : CollatzResearch.WordTrace tailWord_8337617 prefixEnd_8337617 4281205034097810768843503 := by
  unfold tailWord_8337617
  simp only [CollatzResearch.WordTrace]
  refine ⟨304097874635245035462131105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202731916423496690308087403 304097874635245035462131105)
  ·
    refine ⟨228073405976433776596598329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304097874635245035462131105 228073405976433776596598329)
    ·
      refine ⟨171055054482325332447448747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228073405976433776596598329 171055054482325332447448747)
      ·
        refine ⟨256582581723487998671173121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171055054482325332447448747 256582581723487998671173121)
        ·
          refine ⟨192436936292615999003379841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256582581723487998671173121 192436936292615999003379841)
          ·
            refine ⟨144327702219461999252534881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192436936292615999003379841 144327702219461999252534881)
            ·
              refine ⟨108245776664596499439401161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144327702219461999252534881 108245776664596499439401161)
              ·
                refine ⟨81184332498447374579550871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108245776664596499439401161 81184332498447374579550871)
                ·
                  refine ⟨121776498747671061869326307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81184332498447374579550871 121776498747671061869326307)
                  ·
                    refine ⟨182664748121506592803989461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121776498747671061869326307 182664748121506592803989461)
                    ·
                      refine ⟨4281205034097810768843503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182664748121506592803989461 4281205034097810768843503)
                      ·
                        rfl

theorem cell23_8337617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_8337617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337617 prefixEnd_8337617 := by exact prefixLift 8337617
  have htrace : WordTrace (prefixWord ++ tailWord_8337617) baseStart_8337617 baseEnd_8337617 := by
    simpa [prefixWord, tailWord_8337617, baseEnd_8337617] using wordTrace_append hprefix tailTrace_8337617
  have hstable : (prefixWord ++ tailWord_8337617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337617).length < 2 ^ (prefixWord ++ tailWord_8337617).sum := by decide
  have hdescent : baseEnd_8337617 < baseStart_8337617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337624 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_8337624 : Nat := 118140960795 + 8337624 * 2 ^ 59
def prefixEnd_8337624 : Nat := 4983230072969 + 3 ^ 40 * 8337624 * 2
def baseEnd_8337624 : Nat := 1427069542820797413818657

theorem tailTrace_8337624 : CollatzResearch.WordTrace tailWord_8337624 prefixEnd_8337624 1427069542820797413818657 := by
  unfold tailWord_8337624
  simp only [CollatzResearch.WordTrace]
  refine ⟨152049064973109837828817963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202732086630813117105090617 152049064973109837828817963)
  ·
    refine ⟨228073597459664756743226945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152049064973109837828817963 228073597459664756743226945)
    ·
      refine ⟨171055198094748567557420209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228073597459664756743226945 171055198094748567557420209)
      ·
        refine ⟨128291398571061425668065157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171055198094748567557420209 128291398571061425668065157)
        ·
          refine ⟨24054637232074017312762217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128291398571061425668065157 24054637232074017312762217)
          ·
            refine ⟨18040977924055512984571663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24054637232074017312762217 18040977924055512984571663)
            ·
              refine ⟨27061466886083269476857495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18040977924055512984571663 27061466886083269476857495)
              ·
                refine ⟨40592200329124904215286243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27061466886083269476857495 40592200329124904215286243)
                ·
                  refine ⟨60888300493687356322929365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40592200329124904215286243 60888300493687356322929365)
                  ·
                    refine ⟨1427069542820797413818657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60888300493687356322929365 1427069542820797413818657)
                    ·
                      rfl

theorem cell23_8337624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_8337624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337624 prefixEnd_8337624 := by exact prefixLift 8337624
  have htrace : WordTrace (prefixWord ++ tailWord_8337624) baseStart_8337624 baseEnd_8337624 := by
    simpa [prefixWord, tailWord_8337624, baseEnd_8337624] using wordTrace_append hprefix tailTrace_8337624
  have hstable : (prefixWord ++ tailWord_8337624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337624).length < 2 ^ (prefixWord ++ tailWord_8337624).sum := by decide
  have hdescent : baseEnd_8337624 < baseStart_8337624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337644 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_8337644 : Nat := 118140960795 + 8337644 * 2 ^ 59
def prefixEnd_8337644 : Nat := 4983230072969 + 3 ^ 40 * 8337644 * 2
def baseEnd_8337644 : Nat := 4281218898075482163205879

theorem tailTrace_8337644 : CollatzResearch.WordTrace tailWord_8337644 prefixEnd_8337644 4281218898075482163205879 := by
  unfold tailWord_8337644
  simp only [CollatzResearch.WordTrace]
  refine ⟨152049429703073609536681993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202732572937431479382242657 152049429703073609536681993)
  ·
    refine ⟨114037072277305207152511495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152049429703073609536681993 114037072277305207152511495)
    ·
      refine ⟨171055608415957810728767243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114037072277305207152511495 171055608415957810728767243)
      ·
        refine ⟨256583412623936716093150865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171055608415957810728767243 256583412623936716093150865)
        ·
          refine ⟨192437559467952537069863149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256583412623936716093150865 192437559467952537069863149)
          ·
            refine ⟨72164084800482201401198681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192437559467952537069863149 72164084800482201401198681)
            ·
              refine ⟨54123063600361651050899011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72164084800482201401198681 54123063600361651050899011)
              ·
                refine ⟨81184595400542476576348517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54123063600361651050899011 81184595400542476576348517)
                ·
                  refine ⟨15222111637601714358065347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81184595400542476576348517 15222111637601714358065347)
                  ·
                    refine ⟨22833167456402571537098021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15222111637601714358065347 22833167456402571537098021)
                    ·
                      refine ⟨4281218898075482163205879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22833167456402571537098021 4281218898075482163205879)
                      ·
                        rfl

theorem cell23_8337644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_8337644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337644 prefixEnd_8337644 := by exact prefixLift 8337644
  have htrace : WordTrace (prefixWord ++ tailWord_8337644) baseStart_8337644 baseEnd_8337644 := by
    simpa [prefixWord, tailWord_8337644, baseEnd_8337644] using wordTrace_append hprefix tailTrace_8337644
  have hstable : (prefixWord ++ tailWord_8337644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337644).length < 2 ^ (prefixWord ++ tailWord_8337644).sum := by decide
  have hdescent : baseEnd_8337644 < baseStart_8337644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337664 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_8337664 : Nat := 118140960795 + 8337664 * 2 ^ 59
def prefixEnd_8337664 : Nat := 4983230072969 + 3 ^ 40 * 8337664 * 2
def baseEnd_8337664 : Nat := 4281229167688572084955787

theorem tailTrace_8337664 : CollatzResearch.WordTrace tailWord_8337664 prefixEnd_8337664 4281229167688572084955787 := by
  unfold tailWord_8337664
  simp only [CollatzResearch.WordTrace]
  refine ⟨152049794433037381244546023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202733059244049841659394697 152049794433037381244546023)
  ·
    refine ⟨228074691649556071866819035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152049794433037381244546023 228074691649556071866819035)
    ·
      refine ⟨342112037474334107800228553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228074691649556071866819035 342112037474334107800228553)
      ·
        refine ⟨256584028105750580850171415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342112037474334107800228553 256584028105750580850171415)
        ·
          refine ⟨384876042158625871275257123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256584028105750580850171415 384876042158625871275257123)
          ·
            refine ⟨577314063237938806912885685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384876042158625871275257123 577314063237938806912885685)
            ·
              refine ⟨54123193428556763148083033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 577314063237938806912885685 54123193428556763148083033)
              ·
                refine ⟨40592395071417572361062275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54123193428556763148083033 40592395071417572361062275)
                ·
                  refine ⟨60888592607126358541593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40592395071417572361062275 60888592607126358541593413)
                  ·
                    refine ⟨11416611113836192226548765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60888592607126358541593413 11416611113836192226548765)
                    ·
                      refine ⟨4281229167688572084955787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416611113836192226548765 4281229167688572084955787)
                      ·
                        rfl

theorem cell23_8337664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_8337664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337664 prefixEnd_8337664 := by exact prefixLift 8337664
  have htrace : WordTrace (prefixWord ++ tailWord_8337664) baseStart_8337664 baseEnd_8337664 := by
    simpa [prefixWord, tailWord_8337664, baseEnd_8337664] using wordTrace_append hprefix tailTrace_8337664
  have hstable : (prefixWord ++ tailWord_8337664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337664).length < 2 ^ (prefixWord ++ tailWord_8337664).sum := by decide
  have hdescent : baseEnd_8337664 < baseStart_8337664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337698 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_8337698 : Nat := 118140960795 + 8337698 * 2 ^ 59
def prefixEnd_8337698 : Nat := 4983230072969 + 3 ^ 40 * 8337698 * 2
def baseEnd_8337698 : Nat := 4281246626030824951930631

theorem tailTrace_8337698 : CollatzResearch.WordTrace tailWord_8337698 prefixEnd_8337698 4281246626030824951930631 := by
  unfold tailWord_8337698
  simp only [CollatzResearch.WordTrace]
  refine ⟨76025207236987896573957437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202733885965301057530553165 76025207236987896573957437)
  ·
    refine ⟨28509452713870461215234039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76025207236987896573957437 28509452713870461215234039)
    ·
      refine ⟨42764179070805691822851059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28509452713870461215234039 42764179070805691822851059)
      ·
        refine ⟨64146268606208537734276589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42764179070805691822851059 64146268606208537734276589)
        ·
          refine ⟨24054850727328201650353721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64146268606208537734276589 24054850727328201650353721)
          ·
            refine ⟨18041138045496151237765291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24054850727328201650353721 18041138045496151237765291)
            ·
              refine ⟨27061707068244226856647937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18041138045496151237765291 27061707068244226856647937)
              ·
                refine ⟨20296280301183170142485953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27061707068244226856647937 20296280301183170142485953)
                ·
                  refine ⟨15222210225887377606864465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20296280301183170142485953 15222210225887377606864465)
                  ·
                    refine ⟨11416657669415533205148349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15222210225887377606864465 11416657669415533205148349)
                    ·
                      refine ⟨4281246626030824951930631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416657669415533205148349 4281246626030824951930631)
                      ·
                        rfl

theorem cell23_8337698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_8337698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337698 prefixEnd_8337698 := by exact prefixLift 8337698
  have htrace : WordTrace (prefixWord ++ tailWord_8337698) baseStart_8337698 baseEnd_8337698 := by
    simpa [prefixWord, tailWord_8337698, baseEnd_8337698] using wordTrace_append hprefix tailTrace_8337698
  have hstable : (prefixWord ++ tailWord_8337698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337698).length < 2 ^ (prefixWord ++ tailWord_8337698).sum := by decide
  have hdescent : baseEnd_8337698 < baseStart_8337698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337731 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 1, 5]
def baseStart_8337731 : Nat := 118140960795 + 8337731 * 2 ^ 59
def prefixEnd_8337731 : Nat := 4983230072969 + 3 ^ 40 * 8337731 * 2
def baseEnd_8337731 : Nat := 1427087856964141107605993

theorem tailTrace_8337731 : CollatzResearch.WordTrace tailWord_8337731 prefixEnd_8337731 1427087856964141107605993 := by
  unfold tailWord_8337731
  simp only [CollatzResearch.WordTrace]
  refine ⟨304102032556832032931781047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202734688371221355287854031 304102032556832032931781047)
  ·
    refine ⟨456153048835248049397671571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304102032556832032931781047 456153048835248049397671571)
    ·
      refine ⟨684229573252872074096507357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456153048835248049397671571 684229573252872074096507357)
      ·
        refine ⟨256586089969827027786190259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684229573252872074096507357 256586089969827027786190259)
        ·
          refine ⟨384879134954740541679285389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256586089969827027786190259 384879134954740541679285389)
          ·
            refine ⟨144329675608027703129732021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384879134954740541679285389 144329675608027703129732021)
            ·
              refine ⟨13530907088252597168412377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144329675608027703129732021 13530907088252597168412377)
              ·
                refine ⟨10148180316189447876309283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13530907088252597168412377 10148180316189447876309283)
                ·
                  refine ⟨15222270474284171814463925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10148180316189447876309283 15222270474284171814463925)
                  ·
                    refine ⟨1427087856964141107605993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15222270474284171814463925 1427087856964141107605993)
                    ·
                      rfl

theorem cell23_8337731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 5].length) (baseStart_8337731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337731 prefixEnd_8337731 := by exact prefixLift 8337731
  have htrace : WordTrace (prefixWord ++ tailWord_8337731) baseStart_8337731 baseEnd_8337731 := by
    simpa [prefixWord, tailWord_8337731, baseEnd_8337731] using wordTrace_append hprefix tailTrace_8337731
  have hstable : (prefixWord ++ tailWord_8337731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337731).length < 2 ^ (prefixWord ++ tailWord_8337731).sum := by decide
  have hdescent : baseEnd_8337731 < baseStart_8337731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337744 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_8337744 : Nat := 118140960795 + 8337744 * 2 ^ 59
def prefixEnd_8337744 : Nat := 4983230072969 + 3 ^ 40 * 8337744 * 2
def baseEnd_8337744 : Nat := 1427090082046977257318473

theorem tailTrace_8337744 : CollatzResearch.WordTrace tailWord_8337744 prefixEnd_8337744 1427090082046977257318473 := by
  unfold tailWord_8337744
  simp only [CollatzResearch.WordTrace]
  refine ⟨152051253352892468076002143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202735004470523290768002857 152051253352892468076002143)
  ·
    refine ⟨228076880029338702114003215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152051253352892468076002143 228076880029338702114003215)
    ·
      refine ⟨342115320044008053171004823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228076880029338702114003215 342115320044008053171004823)
      ·
        refine ⟨513172980066012079756507235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342115320044008053171004823 513172980066012079756507235)
        ·
          refine ⟨769759470099018119634760853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513172980066012079756507235 769759470099018119634760853)
          ·
            refine ⟨36082475160891474357879415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 769759470099018119634760853 36082475160891474357879415)
            ·
              refine ⟨54123712741337211536819123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36082475160891474357879415 54123712741337211536819123)
              ·
                refine ⟨81185569112005817305228685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54123712741337211536819123 81185569112005817305228685)
                ·
                  refine ⟨30444588417002181489460757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81185569112005817305228685 30444588417002181489460757)
                  ·
                    refine ⟨1427090082046977257318473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30444588417002181489460757 1427090082046977257318473)
                    ·
                      rfl

theorem cell23_8337744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_8337744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337744 prefixEnd_8337744 := by exact prefixLift 8337744
  have htrace : WordTrace (prefixWord ++ tailWord_8337744) baseStart_8337744 baseEnd_8337744 := by
    simpa [prefixWord, tailWord_8337744, baseEnd_8337744] using wordTrace_append hprefix tailTrace_8337744
  have hstable : (prefixWord ++ tailWord_8337744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337744).length < 2 ^ (prefixWord ++ tailWord_8337744).sum := by decide
  have hdescent : baseEnd_8337744 < baseStart_8337744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337756 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_8337756 : Nat := 118140960795 + 8337756 * 2 ^ 59
def prefixEnd_8337756 : Nat := 4983230072969 + 3 ^ 40 * 8337756 * 2
def baseEnd_8337756 : Nat := 1427092135969595241668455

theorem tailTrace_8337756 : CollatzResearch.WordTrace tailWord_8337756 prefixEnd_8337756 1427092135969595241668455 := by
  unfold tailWord_8337756
  simp only [CollatzResearch.WordTrace]
  refine ⟨152051472190870731100720561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202735296254494308134294081 152051472190870731100720561)
  ·
    refine ⟨114038604143153048325540421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152051472190870731100720561 114038604143153048325540421)
    ·
      refine ⟨21382238276841196561038829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114038604143153048325540421 21382238276841196561038829)
      ·
        refine ⟨8018339353815448710389561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21382238276841196561038829 8018339353815448710389561)
        ·
          refine ⟨6013754515361586532792171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018339353815448710389561 6013754515361586532792171)
          ·
            refine ⟨9020631773042379799188257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013754515361586532792171 9020631773042379799188257)
            ·
              refine ⟨6765473829781784849391193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020631773042379799188257 6765473829781784849391193)
              ·
                refine ⟨5074105372336338637043395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765473829781784849391193 5074105372336338637043395)
                ·
                  refine ⟨7611158058504507955565093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074105372336338637043395 7611158058504507955565093)
                  ·
                    refine ⟨1427092135969595241668455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611158058504507955565093 1427092135969595241668455)
                    ·
                      rfl

theorem cell23_8337756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_8337756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337756 prefixEnd_8337756 := by exact prefixLift 8337756
  have htrace : WordTrace (prefixWord ++ tailWord_8337756) baseStart_8337756 baseEnd_8337756 := by
    simpa [prefixWord, tailWord_8337756, baseEnd_8337756] using wordTrace_append hprefix tailTrace_8337756
  have hstable : (prefixWord ++ tailWord_8337756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337756).length < 2 ^ (prefixWord ++ tailWord_8337756).sum := by decide
  have hdescent : baseEnd_8337756 < baseStart_8337756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337762 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_8337762 : Nat := 118140960795 + 8337762 * 2 ^ 59
def prefixEnd_8337762 : Nat := 4983230072969 + 3 ^ 40 * 8337762 * 2
def baseEnd_8337762 : Nat := 4281279488792712701530337

theorem tailTrace_8337762 : CollatzResearch.WordTrace tailWord_8337762 prefixEnd_8337762 4281279488792712701530337 := by
  unfold tailWord_8337762
  simp only [CollatzResearch.WordTrace]
  refine ⟨76025790804929931306539885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202735442146479816817439693 76025790804929931306539885)
  ·
    refine ⟨28509671551848724239952457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76025790804929931306539885 28509671551848724239952457)
    ·
      refine ⟨21382253663886543179964343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28509671551848724239952457 21382253663886543179964343)
      ·
        refine ⟨32073380495829814769946515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382253663886543179964343 32073380495829814769946515)
        ·
          refine ⟨48110070743744722154919773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32073380495829814769946515 48110070743744722154919773)
          ·
            refine ⟨18041276528904270808094915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48110070743744722154919773 18041276528904270808094915)
            ·
              refine ⟨27061914793356406212142373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18041276528904270808094915 27061914793356406212142373)
              ·
                refine ⟨5074109023754326164776695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27061914793356406212142373 5074109023754326164776695)
                ·
                  refine ⟨7611163535631489247165043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074109023754326164776695 7611163535631489247165043)
                  ·
                    refine ⟨11416745303447233870747565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7611163535631489247165043 11416745303447233870747565)
                    ·
                      refine ⟨4281279488792712701530337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11416745303447233870747565 4281279488792712701530337)
                      ·
                        rfl

theorem cell23_8337762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_8337762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337762 prefixEnd_8337762 := by exact prefixLift 8337762
  have htrace : WordTrace (prefixWord ++ tailWord_8337762) baseStart_8337762 baseEnd_8337762 := by
    simpa [prefixWord, tailWord_8337762, baseEnd_8337762] using wordTrace_append hprefix tailTrace_8337762
  have hstable : (prefixWord ++ tailWord_8337762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337762).length < 2 ^ (prefixWord ++ tailWord_8337762).sum := by decide
  have hdescent : baseEnd_8337762 < baseStart_8337762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337778 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_8337778 : Nat := 118140960795 + 8337778 * 2 ^ 59
def prefixEnd_8337778 : Nat := 4983230072969 + 3 ^ 40 * 8337778 * 2
def baseEnd_8337778 : Nat := 1427095901494394879643421

theorem tailTrace_8337778 : CollatzResearch.WordTrace tailWord_8337778 prefixEnd_8337778 1427095901494394879643421 := by
  unfold tailWord_8337778
  simp only [CollatzResearch.WordTrace]
  refine ⟨76025936696915439989685497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202735831191774506639161325 76025936696915439989685497)
  ·
    refine ⟨57019452522686579992264123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76025936696915439989685497 57019452522686579992264123)
    ·
      refine ⟨85529178784029869988396185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57019452522686579992264123 85529178784029869988396185)
      ·
        refine ⟨64146884088022402491297139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85529178784029869988396185 64146884088022402491297139)
        ·
          refine ⟨96220326132033603736945709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64146884088022402491297139 96220326132033603736945709)
          ·
            refine ⟨36082622299512601401354641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96220326132033603736945709 36082622299512601401354641)
            ·
              refine ⟨27061966724634451051015981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36082622299512601401354641 27061966724634451051015981)
              ·
                refine ⟨10148237521737919144130993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27061966724634451051015981 10148237521737919144130993)
                ·
                  refine ⟨7611178141303439358098245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10148237521737919144130993 7611178141303439358098245)
                  ·
                    refine ⟨1427095901494394879643421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611178141303439358098245 1427095901494394879643421)
                    ·
                      rfl

theorem cell23_8337778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_8337778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337778 prefixEnd_8337778 := by exact prefixLift 8337778
  have htrace : WordTrace (prefixWord ++ tailWord_8337778) baseStart_8337778 baseEnd_8337778 := by
    simpa [prefixWord, tailWord_8337778, baseEnd_8337778] using wordTrace_append hprefix tailTrace_8337778
  have hstable : (prefixWord ++ tailWord_8337778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337778).length < 2 ^ (prefixWord ++ tailWord_8337778).sum := by decide
  have hdescent : baseEnd_8337778 < baseStart_8337778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337812 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_8337812 : Nat := 118140960795 + 8337812 * 2 ^ 59
def prefixEnd_8337812 : Nat := 4983230072969 + 3 ^ 40 * 8337812 * 2
def baseEnd_8337812 : Nat := 1427101720941812501968369

theorem tailTrace_8337812 : CollatzResearch.WordTrace tailWord_8337812 prefixEnd_8337812 1427101720941812501968369 := by
  unfold tailWord_8337812
  simp only [CollatzResearch.WordTrace]
  refine ⟨152052493434769291882739845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202736657913025722510319793 152052493434769291882739845)
  ·
    refine ⟨28509842519019242228013721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152052493434769291882739845 28509842519019242228013721)
    ·
      refine ⟨21382381889264431671010291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28509842519019242228013721 21382381889264431671010291)
      ·
        refine ⟨32073572833896647506515437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382381889264431671010291 32073572833896647506515437)
        ·
          refine ⟨12027589812711242814943289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32073572833896647506515437 12027589812711242814943289)
          ·
            refine ⟨9020692359533432111207467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12027589812711242814943289 9020692359533432111207467)
            ·
              refine ⟨13531038539300148166811201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020692359533432111207467 13531038539300148166811201)
              ·
                refine ⟨10148278904475111125108401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13531038539300148166811201 10148278904475111125108401)
                ·
                  refine ⟨7611209178356333343831301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10148278904475111125108401 7611209178356333343831301)
                  ·
                    refine ⟨1427101720941812501968369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7611209178356333343831301 1427101720941812501968369)
                    ·
                      rfl

theorem cell23_8337812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_8337812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337812 prefixEnd_8337812 := by exact prefixLift 8337812
  have htrace : WordTrace (prefixWord ++ tailWord_8337812) baseStart_8337812 baseEnd_8337812 := by
    simpa [prefixWord, tailWord_8337812, baseEnd_8337812] using wordTrace_append hprefix tailTrace_8337812
  have hstable : (prefixWord ++ tailWord_8337812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337812).length < 2 ^ (prefixWord ++ tailWord_8337812).sum := by decide
  have hdescent : baseEnd_8337812 < baseStart_8337812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337828 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_8337828 : Nat := 118140960795 + 8337828 * 2 ^ 59
def prefixEnd_8337828 : Nat := 4983230072969 + 3 ^ 40 * 8337828 * 2
def baseEnd_8337828 : Nat := 4281313378515909443305033

theorem tailTrace_8337828 : CollatzResearch.WordTrace tailWord_8337828 prefixEnd_8337828 4281313378515909443305033 := by
  unfold tailWord_8337828
  simp only [CollatzResearch.WordTrace]
  refine ⟨152052785218740309249031069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202737046958320412332041425 152052785218740309249031069)
  ·
    refine ⟨57019794457027615968386651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152052785218740309249031069 57019794457027615968386651)
    ·
      refine ⟨85529691685541423952579977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57019794457027615968386651 85529691685541423952579977)
      ·
        refine ⟨64147268764156067964434983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85529691685541423952579977 64147268764156067964434983)
        ·
          refine ⟨96220903146234101946652475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64147268764156067964434983 96220903146234101946652475)
          ·
            refine ⟨144331354719351152919978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96220903146234101946652475 144331354719351152919978713)
            ·
              refine ⟨108248516039513364689984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144331354719351152919978713 108248516039513364689984035)
              ·
                refine ⟨162372774059270047034976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108248516039513364689984035 162372774059270047034976053)
                ·
                  refine ⟨15222447568056566909529005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162372774059270047034976053 15222447568056566909529005)
                  ·
                    refine ⟨5708417838021212591073377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15222447568056566909529005 5708417838021212591073377)
                    ·
                      refine ⟨4281313378515909443305033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708417838021212591073377 4281313378515909443305033)
                      ·
                        rfl

theorem cell23_8337828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_8337828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337828 prefixEnd_8337828 := by exact prefixLift 8337828
  have htrace : WordTrace (prefixWord ++ tailWord_8337828) baseStart_8337828 baseEnd_8337828 := by
    simpa [prefixWord, tailWord_8337828, baseEnd_8337828] using wordTrace_append hprefix tailTrace_8337828
  have hstable : (prefixWord ++ tailWord_8337828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337828).length < 2 ^ (prefixWord ++ tailWord_8337828).sum := by decide
  have hdescent : baseEnd_8337828 < baseStart_8337828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337878 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_8337878 : Nat := 118140960795 + 8337878 * 2 ^ 59
def prefixEnd_8337878 : Nat := 4983230072969 + 3 ^ 40 * 8337878 * 2
def baseEnd_8337878 : Nat := 4281339052548634247679803

theorem tailTrace_8337878 : CollatzResearch.WordTrace tailWord_8337878 prefixEnd_8337878 4281339052548634247679803 := by
  unfold tailWord_8337878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19006712130456217314836393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202738262724866318024921525 19006712130456217314836393)
  ·
    refine ⟨14255034097842162986127295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19006712130456217314836393 14255034097842162986127295)
    ·
      refine ⟨21382551146763244479190943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255034097842162986127295 21382551146763244479190943)
      ·
        refine ⟨32073826720144866718786415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382551146763244479190943 32073826720144866718786415)
        ·
          refine ⟨48110740080217300078179623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32073826720144866718786415 48110740080217300078179623)
          ·
            refine ⟨72166110120325950117269435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48110740080217300078179623 72166110120325950117269435)
            ·
              refine ⟨108249165180488925175904153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72166110120325950117269435 108249165180488925175904153)
              ·
                refine ⟨81186873885366693881928115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108249165180488925175904153 81186873885366693881928115)
                ·
                  refine ⟨121780310828050040822892173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81186873885366693881928115 121780310828050040822892173)
                  ·
                    refine ⟨45667616560518765308584565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121780310828050040822892173 45667616560518765308584565)
                    ·
                      refine ⟨4281339052548634247679803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45667616560518765308584565 4281339052548634247679803)
                      ·
                        rfl

theorem cell23_8337878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_8337878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337878 prefixEnd_8337878 := by exact prefixLift 8337878
  have htrace : WordTrace (prefixWord ++ tailWord_8337878) baseStart_8337878 baseEnd_8337878 := by
    simpa [prefixWord, tailWord_8337878, baseEnd_8337878] using wordTrace_append hprefix tailTrace_8337878
  have hstable : (prefixWord ++ tailWord_8337878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337878).length < 2 ^ (prefixWord ++ tailWord_8337878).sum := by decide
  have hdescent : baseEnd_8337878 < baseStart_8337878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337932 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 5]
def baseStart_8337932 : Nat := 118140960795 + 8337932 * 2 ^ 59
def prefixEnd_8337932 : Nat := 4983230072969 + 3 ^ 40 * 8337932 * 2
def baseEnd_8337932 : Nat := 475707420055997448489395

theorem tailTrace_8337932 : CollatzResearch.WordTrace tailWord_8337932 prefixEnd_8337932 475707420055997448489395 := by
  unfold tailWord_8337932
  simp only [CollatzResearch.WordTrace]
  refine ⟨152054681814551922129924025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202739575752735896173232033 152054681814551922129924025)
  ·
    refine ⟨114041011360913941597443019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152054681814551922129924025 114041011360913941597443019)
    ·
      refine ⟨171061517041370912396164529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114041011360913941597443019 171061517041370912396164529)
      ·
        refine ⟨128296137781028184297123397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171061517041370912396164529 128296137781028184297123397)
        ·
          refine ⟨24055525833942784555710637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128296137781028184297123397 24055525833942784555710637)
          ·
            refine ⟨9020822187728544208391489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24055525833942784555710637 9020822187728544208391489)
            ·
              refine ⟨6765616640796408156293617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020822187728544208391489 6765616640796408156293617)
              ·
                refine ⟨5074212480597306117220213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765616640796408156293617 5074212480597306117220213)
                ·
                  refine ⟨475707420055997448489395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5074212480597306117220213 475707420055997448489395)
                  ·
                    rfl

theorem cell23_8337932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_8337932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337932 prefixEnd_8337932 := by exact prefixLift 8337932
  have htrace : WordTrace (prefixWord ++ tailWord_8337932) baseStart_8337932 baseEnd_8337932 := by
    simpa [prefixWord, tailWord_8337932, baseEnd_8337932] using wordTrace_append hprefix tailTrace_8337932
  have hstable : (prefixWord ++ tailWord_8337932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337932).length < 2 ^ (prefixWord ++ tailWord_8337932).sum := by decide
  have hdescent : baseEnd_8337932 < baseStart_8337932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8337971 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 8]
def baseStart_8337971 : Nat := 118140960795 + 8337971 * 2 ^ 59
def prefixEnd_8337971 : Nat := 4983230072969 + 3 ^ 40 * 8337971 * 2
def baseEnd_8337971 : Nat := 475709645138833598201875

theorem tailTrace_8337971 : CollatzResearch.WordTrace tailWord_8337971 prefixEnd_8337971 475709645138833598201875 := by
  unfold tailWord_8337971
  simp only [CollatzResearch.WordTrace]
  refine ⟨304110786075962553920517767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202740524050641702613678511 304110786075962553920517767)
  ·
    refine ⟨456166179113943830880776651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304110786075962553920517767 456166179113943830880776651)
    ·
      refine ⟨684249268670915746321164977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456166179113943830880776651 684249268670915746321164977)
      ·
        refine ⟨513186951503186809740873733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684249268670915746321164977 513186951503186809740873733)
        ·
          refine ⟨96222553406847526826413825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513186951503186809740873733 96222553406847526826413825)
          ·
            refine ⟨72166915055135645119810369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96222553406847526826413825 72166915055135645119810369)
            ·
              refine ⟨54125186291351733839857777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72166915055135645119810369 54125186291351733839857777)
              ·
                refine ⟨40593889718513800379893333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54125186291351733839857777 40593889718513800379893333)
                ·
                  refine ⟨475709645138833598201875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40593889718513800379893333 475709645138833598201875)
                  ·
                    rfl

theorem cell23_8337971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 8].length) (baseStart_8337971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8337971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8337971 prefixEnd_8337971 := by exact prefixLift 8337971
  have htrace : WordTrace (prefixWord ++ tailWord_8337971) baseStart_8337971 baseEnd_8337971 := by
    simpa [prefixWord, tailWord_8337971, baseEnd_8337971] using wordTrace_append hprefix tailTrace_8337971
  have hstable : (prefixWord ++ tailWord_8337971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8337971).length < 2 ^ (prefixWord ++ tailWord_8337971).sum := by decide
  have hdescent : baseEnd_8337971 < baseStart_8337971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8337971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338025 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 2, 3, 2]
def baseStart_8338025 : Nat := 118140960795 + 8338025 * 2 ^ 59
def prefixEnd_8338025 : Nat := 4983230072969 + 3 ^ 40 * 8338025 * 2
def baseEnd_8338025 : Nat := 4281414534204845172541627

theorem tailTrace_8338025 : CollatzResearch.WordTrace tailWord_8338025 prefixEnd_8338025 4281414534204845172541627 := by
  unfold tailWord_8338025
  simp only [CollatzResearch.WordTrace]
  refine ⟨304112755617766921142983529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202741837078511280761989019 304112755617766921142983529)
  ·
    refine ⟨228084566713325190857237647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304112755617766921142983529 228084566713325190857237647)
    ·
      refine ⟨342126850069987786285856471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228084566713325190857237647 342126850069987786285856471)
      ·
        refine ⟨513190275104981679428784707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342126850069987786285856471 513190275104981679428784707)
        ·
          refine ⟨769785412657472519143177061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513190275104981679428784707 769785412657472519143177061)
          ·
            refine ⟨144334764873276097339345699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 769785412657472519143177061 144334764873276097339345699)
            ·
              refine ⟨216502147309914146009018549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144334764873276097339345699 216502147309914146009018549)
              ·
                refine ⟨20297076310304451188345489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216502147309914146009018549 20297076310304451188345489)
                ·
                  refine ⟨15222807232728338391259117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20297076310304451188345489 15222807232728338391259117)
                  ·
                    refine ⟨5708552712273126896722169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15222807232728338391259117 5708552712273126896722169)
                    ·
                      refine ⟨4281414534204845172541627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708552712273126896722169 4281414534204845172541627)
                      ·
                        rfl

theorem cell23_8338025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3, 2].length) (baseStart_8338025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338025 prefixEnd_8338025 := by exact prefixLift 8338025
  have htrace : WordTrace (prefixWord ++ tailWord_8338025) baseStart_8338025 baseEnd_8338025 := by
    simpa [prefixWord, tailWord_8338025, baseEnd_8338025] using wordTrace_append hprefix tailTrace_8338025
  have hstable : (prefixWord ++ tailWord_8338025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338025).length < 2 ^ (prefixWord ++ tailWord_8338025).sum := by decide
  have hdescent : baseEnd_8338025 < baseStart_8338025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338072 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_8338072 : Nat := 118140960795 + 8338072 * 2 ^ 59
def prefixEnd_8338072 : Nat := 4983230072969 + 3 ^ 40 * 8338072 * 2
def baseEnd_8338072 : Nat := 4281438667795606488653911

theorem tailTrace_8338072 : CollatzResearch.WordTrace tailWord_8338072 prefixEnd_8338072 4281438667795606488653911 := by
  unfold tailWord_8338072
  simp only [CollatzResearch.WordTrace]
  refine ⟨152057234924298324084972235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202742979899064432113296313 152057234924298324084972235)
  ·
    refine ⟨228085852386447486127458353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152057234924298324084972235 228085852386447486127458353)
    ·
      refine ⟨171064389289835614595593765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228085852386447486127458353 171064389289835614595593765)
      ·
        refine ⟨32074572991844177736673831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171064389289835614595593765 32074572991844177736673831)
        ·
          refine ⟨48111859487766266605010747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32074572991844177736673831 48111859487766266605010747)
          ·
            refine ⟨72167789231649399907516121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48111859487766266605010747 72167789231649399907516121)
            ·
              refine ⟨54125841923737049930637091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72167789231649399907516121 54125841923737049930637091)
              ·
                refine ⟨81188762885605574895955637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54125841923737049930637091 81188762885605574895955637)
                ·
                  refine ⟨7611446520525522646495841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81188762885605574895955637 7611446520525522646495841)
                  ·
                    refine ⟨5708584890394141984871881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7611446520525522646495841 5708584890394141984871881)
                    ·
                      refine ⟨4281438667795606488653911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708584890394141984871881 4281438667795606488653911)
                      ·
                        rfl

theorem cell23_8338072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_8338072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338072 prefixEnd_8338072 := by exact prefixLift 8338072
  have htrace : WordTrace (prefixWord ++ tailWord_8338072) baseStart_8338072 baseEnd_8338072 := by
    simpa [prefixWord, tailWord_8338072, baseEnd_8338072] using wordTrace_append hprefix tailTrace_8338072
  have hstable : (prefixWord ++ tailWord_8338072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338072).length < 2 ^ (prefixWord ++ tailWord_8338072).sum := by decide
  have hdescent : baseEnd_8338072 < baseStart_8338072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338108 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_8338108 : Nat := 118140960795 + 8338108 * 2 ^ 59
def prefixEnd_8338108 : Nat := 4983230072969 + 3 ^ 40 * 8338108 * 2
def baseEnd_8338108 : Nat := 1427152384366389449267915

theorem tailTrace_8338108 : CollatzResearch.WordTrace tailWord_8338108 prefixEnd_8338108 1427152384366389449267915 := by
  unfold tailWord_8338108
  simp only [CollatzResearch.WordTrace]
  refine ⟨152057891438233113159127489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202743855250977484212169985 152057891438233113159127489)
  ·
    refine ⟨114043418578674834869345617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152057891438233113159127489 114043418578674834869345617)
    ·
      refine ⟨85532563934006126152009213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114043418578674834869345617 85532563934006126152009213)
      ·
        refine ⟨32074711475252297307003455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85532563934006126152009213 32074711475252297307003455)
        ·
          refine ⟨48112067212878445960505183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32074711475252297307003455 48112067212878445960505183)
          ·
            refine ⟨72168100819317668940757775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48112067212878445960505183 72168100819317668940757775)
            ·
              refine ⟨108252151228976503411136663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72168100819317668940757775 108252151228976503411136663)
              ·
                refine ⟨162378226843464755116704995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108252151228976503411136663 162378226843464755116704995)
                ·
                  refine ⟨243567340265197132675057493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162378226843464755116704995 243567340265197132675057493)
                  ·
                    refine ⟨1427152384366389449267915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243567340265197132675057493 1427152384366389449267915)
                    ·
                      rfl

theorem cell23_8338108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_8338108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338108 prefixEnd_8338108 := by exact prefixLift 8338108
  have htrace : WordTrace (prefixWord ++ tailWord_8338108) baseStart_8338108 baseEnd_8338108 := by
    simpa [prefixWord, tailWord_8338108, baseEnd_8338108] using wordTrace_append hprefix tailTrace_8338108
  have hstable : (prefixWord ++ tailWord_8338108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338108).length < 2 ^ (prefixWord ++ tailWord_8338108).sum := by decide
  have hdescent : baseEnd_8338108 < baseStart_8338108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338122 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_8338122 : Nat := 118140960795 + 8338122 * 2 ^ 59
def prefixEnd_8338122 : Nat := 4983230072969 + 3 ^ 40 * 8338122 * 2
def baseEnd_8338122 : Nat := 4281464341828331293028681

theorem tailTrace_8338122 : CollatzResearch.WordTrace tailWord_8338122 prefixEnd_8338122 4281464341828331293028681 := by
  unfold tailWord_8338122
  simp only [CollatzResearch.WordTrace]
  refine ⟨76029073374603876677316155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202744195665610337806176413 76029073374603876677316155)
  ·
    refine ⟨114043610061905815015974233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76029073374603876677316155 114043610061905815015974233)
    ·
      refine ⟨85532707546429361261980675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114043610061905815015974233 85532707546429361261980675)
      ·
        refine ⟨128299061319644041892971013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85532707546429361261980675 128299061319644041892971013)
        ·
          refine ⟨24056073997433257854932065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128299061319644041892971013 24056073997433257854932065)
          ·
            refine ⟨18042055498074943391199049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24056073997433257854932065 18042055498074943391199049)
            ·
              refine ⟨13531541623556207543399287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18042055498074943391199049 13531541623556207543399287)
              ·
                refine ⟨20297312435334311315098931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531541623556207543399287 20297312435334311315098931)
                ·
                  refine ⟨30445968653001466972648397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20297312435334311315098931 30445968653001466972648397)
                  ·
                    refine ⟨11417238244875550114743149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30445968653001466972648397 11417238244875550114743149)
                    ·
                      refine ⟨4281464341828331293028681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11417238244875550114743149 4281464341828331293028681)
                      ·
                        rfl

theorem cell23_8338122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_8338122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338122 prefixEnd_8338122 := by exact prefixLift 8338122
  have htrace : WordTrace (prefixWord ++ tailWord_8338122) baseStart_8338122 baseEnd_8338122 := by
    simpa [prefixWord, tailWord_8338122, baseEnd_8338122] using wordTrace_append hprefix tailTrace_8338122
  have hstable : (prefixWord ++ tailWord_8338122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338122).length < 2 ^ (prefixWord ++ tailWord_8338122).sum := by decide
  have hdescent : baseEnd_8338122 < baseStart_8338122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338138 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_8338138 : Nat := 118140960795 + 8338138 * 2 ^ 59
def prefixEnd_8338138 : Nat := 4983230072969 + 3 ^ 40 * 8338138 * 2
def baseEnd_8338138 : Nat := 1427157519172934410142869

theorem tailTrace_8338138 : CollatzResearch.WordTrace tailWord_8338138 prefixEnd_8338138 1427157519172934410142869 := by
  unfold tailWord_8338138
  simp only [CollatzResearch.WordTrace]
  refine ⟨76029219266589385360461767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202744584710905027627898045 76029219266589385360461767)
  ·
    refine ⟨114043828899884078040692651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76029219266589385360461767 114043828899884078040692651)
    ·
      refine ⟨171065743349826117061038977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114043828899884078040692651 171065743349826117061038977)
      ·
        refine ⟨128299307512369587795779233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171065743349826117061038977 128299307512369587795779233)
        ·
          refine ⟨96224480634277190846834425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128299307512369587795779233 96224480634277190846834425)
          ·
            refine ⟨72168360475707893135125819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96224480634277190846834425 72168360475707893135125819)
            ·
              refine ⟨108252540713561839702688729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72168360475707893135125819 108252540713561839702688729)
              ·
                refine ⟨81189405535171379777016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108252540713561839702688729 81189405535171379777016547)
                ·
                  refine ⟨121784108302757069665524821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81189405535171379777016547 121784108302757069665524821)
                  ·
                    refine ⟨1427157519172934410142869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121784108302757069665524821 1427157519172934410142869)
                    ·
                      rfl

theorem cell23_8338138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_8338138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338138 prefixEnd_8338138 := by exact prefixLift 8338138
  have htrace : WordTrace (prefixWord ++ tailWord_8338138) baseStart_8338138 baseEnd_8338138 := by
    simpa [prefixWord, tailWord_8338138, baseEnd_8338138] using wordTrace_append hprefix tailTrace_8338138
  have hstable : (prefixWord ++ tailWord_8338138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338138).length < 2 ^ (prefixWord ++ tailWord_8338138).sum := by decide
  have hdescent : baseEnd_8338138 < baseStart_8338138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338149 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_8338149 : Nat := 118140960795 + 8338149 * 2 ^ 59
def prefixEnd_8338149 : Nat := 4983230072969 + 3 ^ 40 * 8338149 * 2
def baseEnd_8338149 : Nat := 4281478205806002687391057

theorem tailTrace_8338149 : CollatzResearch.WordTrace tailWord_8338149 prefixEnd_8338149 4281478205806002687391057 := by
  unfold tailWord_8338149
  simp only [CollatzResearch.WordTrace]
  refine ⟨304117278269317690320497501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202744852179545126880331667 304117278269317690320497501)
  ·
    refine ⟨114043979350994133870186563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304117278269317690320497501 114043979350994133870186563)
    ·
      refine ⟨171065969026491200805279845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114043979350994133870186563 171065969026491200805279845)
      ·
        refine ⟨32074869192467100150989971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171065969026491200805279845 32074869192467100150989971)
        ·
          refine ⟨48112303788700650226484957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32074869192467100150989971 48112303788700650226484957)
          ·
            refine ⟨18042113920762743834931859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48112303788700650226484957 18042113920762743834931859)
            ·
              refine ⟨27063170881144115752397789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042113920762743834931859 27063170881144115752397789)
              ·
                refine ⟨10148689080429043407149171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27063170881144115752397789 10148689080429043407149171)
                ·
                  refine ⟨15223033620643565110723757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10148689080429043407149171 15223033620643565110723757)
                  ·
                    refine ⟨5708637607741336916521409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15223033620643565110723757 5708637607741336916521409)
                    ·
                      refine ⟨4281478205806002687391057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708637607741336916521409 4281478205806002687391057)
                      ·
                        rfl

theorem cell23_8338149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_8338149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338149 prefixEnd_8338149 := by exact prefixLift 8338149
  have htrace : WordTrace (prefixWord ++ tailWord_8338149) baseStart_8338149 baseEnd_8338149 := by
    simpa [prefixWord, tailWord_8338149, baseEnd_8338149] using wordTrace_append hprefix tailTrace_8338149
  have hstable : (prefixWord ++ tailWord_8338149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338149).length < 2 ^ (prefixWord ++ tailWord_8338149).sum := by decide
  have hdescent : baseEnd_8338149 < baseStart_8338149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338225 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_8338225 : Nat := 118140960795 + 8338225 * 2 ^ 59
def prefixEnd_8338225 : Nat := 4983230072969 + 3 ^ 40 * 8338225 * 2
def baseEnd_8338225 : Nat := 4281517230335744390040707

theorem tailTrace_8338225 : CollatzResearch.WordTrace tailWord_8338225 prefixEnd_8338225 4281517230335744390040707 := by
  unfold tailWord_8338225
  simp only [CollatzResearch.WordTrace]
  refine ⟨304120050217042355300264129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202746700144694903533509419 304120050217042355300264129)
  ·
    refine ⟨228090037662781766475198097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304120050217042355300264129 228090037662781766475198097)
    ·
      refine ⟨171067528247086324856398573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228090037662781766475198097 171067528247086324856398573)
      ·
        refine ⟨64150323092657371821149465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171067528247086324856398573 64150323092657371821149465)
        ·
          refine ⟨48112742319493028865862099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64150323092657371821149465 48112742319493028865862099)
          ·
            refine ⟨72169113479239543298793149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48112742319493028865862099 72169113479239543298793149)
            ·
              refine ⟨27063417554714828737047431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72169113479239543298793149 27063417554714828737047431)
              ·
                refine ⟨40595126332072243105571147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27063417554714828737047431 40595126332072243105571147)
                ·
                  refine ⟨60892689498108364658356721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40595126332072243105571147 60892689498108364658356721)
                  ·
                    refine ⟨45669517123581273493767541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60892689498108364658356721 45669517123581273493767541)
                    ·
                      refine ⟨4281517230335744390040707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45669517123581273493767541 4281517230335744390040707)
                      ·
                        rfl

theorem cell23_8338225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_8338225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338225 prefixEnd_8338225 := by exact prefixLift 8338225
  have htrace : WordTrace (prefixWord ++ tailWord_8338225) baseStart_8338225 baseEnd_8338225 := by
    simpa [prefixWord, tailWord_8338225, baseEnd_8338225] using wordTrace_append hprefix tailTrace_8338225
  have hstable : (prefixWord ++ tailWord_8338225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338225).length < 2 ^ (prefixWord ++ tailWord_8338225).sum := by decide
  have hdescent : baseEnd_8338225 < baseStart_8338225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338252 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_8338252 : Nat := 118140960795 + 8338252 * 2 ^ 59
def prefixEnd_8338252 : Nat := 4983230072969 + 3 ^ 40 * 8338252 * 2
def baseEnd_8338252 : Nat := 4281531094313415784403083

theorem tailTrace_8338252 : CollatzResearch.WordTrace tailWord_8338252 prefixEnd_8338252 4281531094313415784403083 := by
  unfold tailWord_8338252
  simp only [CollatzResearch.WordTrace]
  refine ⟨152060517493972269455748505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202747356658629692607664673 152060517493972269455748505)
  ·
    refine ⟨114045388120479202091811379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152060517493972269455748505 114045388120479202091811379)
    ·
      refine ⟨171068082180718803137717069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114045388120479202091811379 171068082180718803137717069)
      ·
        refine ⟨64150530817769551176643901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171068082180718803137717069 64150530817769551176643901)
        ·
          refine ⟨24056449056663581691241463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64150530817769551176643901 24056449056663581691241463)
          ·
            refine ⟨36084673584995372536862195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24056449056663581691241463 36084673584995372536862195)
            ·
              refine ⟨54127010377493058805293293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36084673584995372536862195 54127010377493058805293293)
              ·
                refine ⟨20297628891559897051984985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54127010377493058805293293 20297628891559897051984985)
                ·
                  refine ⟨15223221668669922788988739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20297628891559897051984985 15223221668669922788988739)
                  ·
                    refine ⟨22834832503004884183483109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15223221668669922788988739 22834832503004884183483109)
                    ·
                      refine ⟨4281531094313415784403083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22834832503004884183483109 4281531094313415784403083)
                      ·
                        rfl

theorem cell23_8338252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_8338252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338252 prefixEnd_8338252 := by exact prefixLift 8338252
  have htrace : WordTrace (prefixWord ++ tailWord_8338252) baseStart_8338252 baseEnd_8338252 := by
    simpa [prefixWord, tailWord_8338252, baseEnd_8338252] using wordTrace_append hprefix tailTrace_8338252
  have hstable : (prefixWord ++ tailWord_8338252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338252).length < 2 ^ (prefixWord ++ tailWord_8338252).sum := by decide
  have hdescent : baseEnd_8338252 < baseStart_8338252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338272 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_8338272 : Nat := 118140960795 + 8338272 * 2 ^ 59
def prefixEnd_8338272 : Nat := 4983230072969 + 3 ^ 40 * 8338272 * 2
def baseEnd_8338272 : Nat := 4281541363926505706152991

theorem tailTrace_8338272 : CollatzResearch.WordTrace tailWord_8338272 prefixEnd_8338272 4281541363926505706152991 := by
  unfold tailWord_8338272
  simp only [CollatzResearch.WordTrace]
  refine ⟨152060882223936041163612535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202747842965248054884816713 152060882223936041163612535)
  ·
    refine ⟨228091323335904061745418803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152060882223936041163612535 228091323335904061745418803)
    ·
      refine ⟨342136985003856092618128205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228091323335904061745418803 342136985003856092618128205)
      ·
        refine ⟨128301369376446034731798077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342136985003856092618128205 128301369376446034731798077)
        ·
          refine ⟨48113013516167263024424279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128301369376446034731798077 48113013516167263024424279)
          ·
            refine ⟨72169520274250894536636419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48113013516167263024424279 72169520274250894536636419)
            ·
              refine ⟨108254280411376341804954629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72169520274250894536636419 108254280411376341804954629)
              ·
                refine ⟨20297677577133064088428993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108254280411376341804954629 20297677577133064088428993)
                ·
                  refine ⟨15223258182849798066321745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20297677577133064088428993 15223258182849798066321745)
                  ·
                    refine ⟨11417443637137348549741309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15223258182849798066321745 11417443637137348549741309)
                    ·
                      refine ⟨4281541363926505706152991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11417443637137348549741309 4281541363926505706152991)
                      ·
                        rfl

theorem cell23_8338272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_8338272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338272 prefixEnd_8338272 := by exact prefixLift 8338272
  have htrace : WordTrace (prefixWord ++ tailWord_8338272) baseStart_8338272 baseEnd_8338272 := by
    simpa [prefixWord, tailWord_8338272, baseEnd_8338272] using wordTrace_append hprefix tailTrace_8338272
  have hstable : (prefixWord ++ tailWord_8338272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338272).length < 2 ^ (prefixWord ++ tailWord_8338272).sum := by decide
  have hdescent : baseEnd_8338272 < baseStart_8338272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338286 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_8338286 : Nat := 118140960795 + 8338286 * 2 ^ 59
def prefixEnd_8338286 : Nat := 4983230072969 + 3 ^ 40 * 8338286 * 2
def baseEnd_8338286 : Nat := 4281548552655668651377927

theorem tailTrace_8338286 : CollatzResearch.WordTrace tailWord_8338286 prefixEnd_8338286 4281548552655668651377927 := by
  unfold tailWord_8338286
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015284383727670339779339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202748183379880908478823141 38015284383727670339779339)
  ·
    refine ⟨57022926575591505509669009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38015284383727670339779339 57022926575591505509669009)
    ·
      refine ⟨42767194931693629132251757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57022926575591505509669009 42767194931693629132251757)
      ·
        refine ⟨16037698099385110924594409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42767194931693629132251757 16037698099385110924594409)
        ·
          refine ⟨12028273574538833193445807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16037698099385110924594409 12028273574538833193445807)
          ·
            refine ⟨18042410361808249790168711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028273574538833193445807 18042410361808249790168711)
            ·
              refine ⟨27063615542712374685253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042410361808249790168711 27063615542712374685253067)
              ·
                refine ⟨40595423314068562027879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27063615542712374685253067 40595423314068562027879601)
                ·
                  refine ⟨30446567485551421520909701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40595423314068562027879601 30446567485551421520909701)
                  ·
                    refine ⟨5708731403540891535170569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30446567485551421520909701 5708731403540891535170569)
                    ·
                      refine ⟨4281548552655668651377927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708731403540891535170569 4281548552655668651377927)
                      ·
                        rfl

theorem cell23_8338286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_8338286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338286 prefixEnd_8338286 := by exact prefixLift 8338286
  have htrace : WordTrace (prefixWord ++ tailWord_8338286) baseStart_8338286 baseEnd_8338286 := by
    simpa [prefixWord, tailWord_8338286, baseEnd_8338286] using wordTrace_append hprefix tailTrace_8338286
  have hstable : (prefixWord ++ tailWord_8338286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338286).length < 2 ^ (prefixWord ++ tailWord_8338286).sum := by decide
  have hdescent : baseEnd_8338286 < baseStart_8338286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338326 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_8338326 : Nat := 118140960795 + 8338326 * 2 ^ 59
def prefixEnd_8338326 : Nat := 4983230072969 + 3 ^ 40 * 8338326 * 2
def baseEnd_8338326 : Nat := 475729899097983166097527

theorem tailTrace_8338326 : CollatzResearch.WordTrace tailWord_8338326 prefixEnd_8338326 475729899097983166097527 := by
  unfold tailWord_8338326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007733374354778096855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202749155993117633033127221 19007733374354778096855677)
  ·
    refine ⟨7127900015383041786320879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19007733374354778096855677 7127900015383041786320879)
    ·
      refine ⟨10691850023074562679481319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127900015383041786320879 10691850023074562679481319)
      ·
        refine ⟨16037775034611844019221979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691850023074562679481319 16037775034611844019221979)
        ·
          refine ⟨24056662551917766028832969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037775034611844019221979 24056662551917766028832969)
          ·
            refine ⟨18042496913938324521624727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24056662551917766028832969 18042496913938324521624727)
            ·
              refine ⟨27063745370907486782437091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042496913938324521624727 27063745370907486782437091)
              ·
                refine ⟨40595618056361230173655637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27063745370907486782437091 40595618056361230173655637)
                ·
                  refine ⟨475729899097983166097527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40595618056361230173655637 475729899097983166097527)
                  ·
                    rfl

theorem cell23_8338326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_8338326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338326 prefixEnd_8338326 := by exact prefixLift 8338326
  have htrace : WordTrace (prefixWord ++ tailWord_8338326) baseStart_8338326 baseEnd_8338326 := by
    simpa [prefixWord, tailWord_8338326, baseEnd_8338326] using wordTrace_append hprefix tailTrace_8338326
  have hstable : (prefixWord ++ tailWord_8338326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338326).length < 2 ^ (prefixWord ++ tailWord_8338326).sum := by decide
  have hdescent : baseEnd_8338326 < baseStart_8338326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338336 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 1, 1, 3]
def baseStart_8338336 : Nat := 118140960795 + 8338336 * 2 ^ 59
def prefixEnd_8338336 : Nat := 4983230072969 + 3 ^ 40 * 8338336 * 2
def baseEnd_8338336 : Nat := 4281574226688393455752697

theorem tailTrace_8338336 : CollatzResearch.WordTrace tailWord_8338336 prefixEnd_8338336 4281574226688393455752697 := by
  unfold tailWord_8338336
  simp only [CollatzResearch.WordTrace]
  refine ⟨152062049359820110628777431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202749399146426814171703241 152062049359820110628777431)
  ·
    refine ⟨228093074039730165943166147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152062049359820110628777431 228093074039730165943166147)
    ·
      refine ⟨342139611059595248914749221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228093074039730165943166147 342139611059595248914749221)
      ·
        refine ⟨64151177073674109171515479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342139611059595248914749221 64151177073674109171515479)
        ·
          refine ⟨96226765610511163757273219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64151177073674109171515479 96226765610511163757273219)
          ·
            refine ⟨144340148415766745635909829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96226765610511163757273219 144340148415766745635909829)
            ·
              refine ⟨27063777827956264806733093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144340148415766745635909829 27063777827956264806733093)
              ·
                refine ⟨5074458342741799651262455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27063777827956264806733093 5074458342741799651262455)
                ·
                  refine ⟨7611687514112699476893683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074458342741799651262455 7611687514112699476893683)
                  ·
                    refine ⟨11417531271169049215340525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7611687514112699476893683 11417531271169049215340525)
                    ·
                      refine ⟨4281574226688393455752697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11417531271169049215340525 4281574226688393455752697)
                      ·
                        rfl

theorem cell23_8338336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_8338336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338336 prefixEnd_8338336 := by exact prefixLift 8338336
  have htrace : WordTrace (prefixWord ++ tailWord_8338336) baseStart_8338336 baseEnd_8338336 := by
    simpa [prefixWord, tailWord_8338336, baseEnd_8338336] using wordTrace_append hprefix tailTrace_8338336
  have hstable : (prefixWord ++ tailWord_8338336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338336).length < 2 ^ (prefixWord ++ tailWord_8338336).sum := by decide
  have hdescent : baseEnd_8338336 < baseStart_8338336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338356 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_8338356 : Nat := 118140960795 + 8338356 * 2 ^ 59
def prefixEnd_8338356 : Nat := 4983230072969 + 3 ^ 40 * 8338356 * 2
def baseEnd_8338356 : Nat := 1427194832100494459167535

theorem tailTrace_8338356 : CollatzResearch.WordTrace tailWord_8338356 prefixEnd_8338356 1427194832100494459167535 := by
  unfold tailWord_8338356
  simp only [CollatzResearch.WordTrace]
  refine ⟨152062414089783882336641461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202749885453045176448855281 152062414089783882336641461)
  ·
    refine ⟨14255851320917238969060137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152062414089783882336641461 14255851320917238969060137)
    ·
      refine ⟨10691888490687929226795103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14255851320917238969060137 10691888490687929226795103)
      ·
        refine ⟨16037832736031893840192655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691888490687929226795103 16037832736031893840192655)
        ·
          refine ⟨24056749104047840760288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037832736031893840192655 24056749104047840760288983)
          ·
            refine ⟨36085123656071761140433475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24056749104047840760288983 36085123656071761140433475)
            ·
              refine ⟨54127685484107641710650213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36085123656071761140433475 54127685484107641710650213)
              ·
                refine ⟨10148941028270182820746915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54127685484107641710650213 10148941028270182820746915)
                ·
                  refine ⟨15223411542405274231120373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10148941028270182820746915 15223411542405274231120373)
                  ·
                    refine ⟨1427194832100494459167535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15223411542405274231120373 1427194832100494459167535)
                    ·
                      rfl

theorem cell23_8338356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_8338356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338356 prefixEnd_8338356 := by exact prefixLift 8338356
  have htrace : WordTrace (prefixWord ++ tailWord_8338356) baseStart_8338356 baseEnd_8338356 := by
    simpa [prefixWord, tailWord_8338356, baseEnd_8338356] using wordTrace_append hprefix tailTrace_8338356
  have hstable : (prefixWord ++ tailWord_8338356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338356).length < 2 ^ (prefixWord ++ tailWord_8338356).sum := by decide
  have hdescent : baseEnd_8338356 < baseStart_8338356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338379 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 3]
def baseStart_8338379 : Nat := 118140960795 + 8338379 * 2 ^ 59
def prefixEnd_8338379 : Nat := 4983230072969 + 3 ^ 40 * 8338379 * 2
def baseEnd_8338379 : Nat := 4281596306356536787514999

theorem tailTrace_8338379 : CollatzResearch.WordTrace tailWord_8338379 prefixEnd_8338379 4281596306356536787514999 := by
  unfold tailWord_8338379
  simp only [CollatzResearch.WordTrace]
  refine ⟨304125667058484439601370191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202750444705656293067580127 304125667058484439601370191)
  ·
    refine ⟨456188500587726659402055287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304125667058484439601370191 456188500587726659402055287)
    ·
      refine ⟨684282750881589989103082931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456188500587726659402055287 684282750881589989103082931)
      ·
        refine ⟨1026424126322384983654624397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684282750881589989103082931 1026424126322384983654624397)
        ·
          refine ⟨384909047370894368870484149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026424126322384983654624397 384909047370894368870484149)
          ·
            refine ⟨36085223191021347081607889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384909047370894368870484149 36085223191021347081607889)
            ·
              refine ⟨27063917393266010311205917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36085223191021347081607889 27063917393266010311205917)
              ·
                refine ⟨10148969022474753866702219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27063917393266010311205917 10148969022474753866702219)
                ·
                  refine ⟨15223453533712130800053329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10148969022474753866702219 15223453533712130800053329)
                  ·
                    refine ⟨11417590150284098100039997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15223453533712130800053329 11417590150284098100039997)
                    ·
                      refine ⟨4281596306356536787514999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11417590150284098100039997 4281596306356536787514999)
                      ·
                        rfl

theorem cell23_8338379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 3].length) (baseStart_8338379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338379 prefixEnd_8338379 := by exact prefixLift 8338379
  have htrace : WordTrace (prefixWord ++ tailWord_8338379) baseStart_8338379 baseEnd_8338379 := by
    simpa [prefixWord, tailWord_8338379, baseEnd_8338379] using wordTrace_append hprefix tailTrace_8338379
  have hstable : (prefixWord ++ tailWord_8338379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338379).length < 2 ^ (prefixWord ++ tailWord_8338379).sum := by decide
  have hdescent : baseEnd_8338379 < baseStart_8338379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338382 : List Nat := [4, 1, 1, 1, 2, 5, 9]
def baseStart_8338382 : Nat := 118140960795 + 8338382 * 2 ^ 59
def prefixEnd_8338382 : Nat := 4983230072969 + 3 ^ 40 * 8338382 * 2
def baseEnd_8338382 : Nat := 52859232676524694762685

theorem tailTrace_8338382 : CollatzResearch.WordTrace tailWord_8338382 prefixEnd_8338382 52859232676524694762685 := by
  unfold tailWord_8338382
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015722059684196389216175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202750517651649047409152933 38015722059684196389216175)
  ·
    refine ⟨57023583089526294583824263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38015722059684196389216175 57023583089526294583824263)
    ·
      refine ⟨85535374634289441875736395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57023583089526294583824263 85535374634289441875736395)
      ·
        refine ⟨128303061951434162813604593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85535374634289441875736395 128303061951434162813604593)
        ·
          refine ⟨96227296463575622110203445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128303061951434162813604593 96227296463575622110203445)
          ·
            refine ⟨9021309043460214572831573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96227296463575622110203445 9021309043460214572831573)
            ·
              refine ⟨52859232676524694762685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9021309043460214572831573 52859232676524694762685)
              ·
                rfl

theorem cell23_8338382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 9].length) (baseStart_8338382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338382 prefixEnd_8338382 := by exact prefixLift 8338382
  have htrace : WordTrace (prefixWord ++ tailWord_8338382) baseStart_8338382 baseEnd_8338382 := by
    simpa [prefixWord, tailWord_8338382, baseEnd_8338382] using wordTrace_append hprefix tailTrace_8338382
  have hstable : (prefixWord ++ tailWord_8338382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338382).length < 2 ^ (prefixWord ++ tailWord_8338382).sum := by decide
  have hdescent : baseEnd_8338382 < baseStart_8338382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338393 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 3, 2, 2]
def baseStart_8338393 : Nat := 118140960795 + 8338393 * 2 ^ 59
def prefixEnd_8338393 : Nat := 4983230072969 + 3 ^ 40 * 8338393 * 2
def baseEnd_8338393 : Nat := 4281603495085699732739935

theorem tailTrace_8338393 : CollatzResearch.WordTrace tailWord_8338393 prefixEnd_8338393 4281603495085699732739935 := by
  unfold tailWord_8338393
  simp only [CollatzResearch.WordTrace]
  refine ⟨304126177680433719992379833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202750785120289146661586555 304126177680433719992379833)
  ·
    refine ⟨228094633260325289994284875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304126177680433719992379833 228094633260325289994284875)
    ·
      refine ⟨342141949890487934991427313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228094633260325289994284875 342141949890487934991427313)
      ·
        refine ⟨256606462417865951243570485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342141949890487934991427313 256606462417865951243570485)
        ·
          refine ⟨24056855851674932929084733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256606462417865951243570485 24056855851674932929084733)
          ·
            refine ⟨9021320944378099848406775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24056855851674932929084733 9021320944378099848406775)
            ·
              refine ⟨13531981416567149772610163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021320944378099848406775 13531981416567149772610163)
              ·
                refine ⟨20297972124850724658915245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531981416567149772610163 20297972124850724658915245)
                ·
                  refine ⟨7611739546819021747093217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20297972124850724658915245 7611739546819021747093217)
                  ·
                    refine ⟨5708804660114266310319913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7611739546819021747093217 5708804660114266310319913)
                    ·
                      refine ⟨4281603495085699732739935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708804660114266310319913 4281603495085699732739935)
                      ·
                        rfl

theorem cell23_8338393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_8338393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338393 prefixEnd_8338393 := by exact prefixLift 8338393
  have htrace : WordTrace (prefixWord ++ tailWord_8338393) baseStart_8338393 baseEnd_8338393 := by
    simpa [prefixWord, tailWord_8338393, baseEnd_8338393] using wordTrace_append hprefix tailTrace_8338393
  have hstable : (prefixWord ++ tailWord_8338393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338393).length < 2 ^ (prefixWord ++ tailWord_8338393).sum := by decide
  have hdescent : baseEnd_8338393 < baseStart_8338393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338420 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8338420 : Nat := 118140960795 + 8338420 * 2 ^ 59
def prefixEnd_8338420 : Nat := 4983230072969 + 3 ^ 40 * 8338420 * 2
def baseEnd_8338420 : Nat := 1427205786354457042367437

theorem tailTrace_8338420 : CollatzResearch.WordTrace tailWord_8338420 prefixEnd_8338420 1427205786354457042367437 := by
  unfold tailWord_8338420
  simp only [CollatzResearch.WordTrace]
  refine ⟨152063581225667951801806357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202751441634223935735741809 152063581225667951801806357)
  ·
    refine ⟨7127980369953185240709673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152063581225667951801806357 7127980369953185240709673)
    ·
      refine ⟨5345985277464888930532255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7127980369953185240709673 5345985277464888930532255)
      ·
        refine ⟨8018977916197333395798383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345985277464888930532255 8018977916197333395798383)
        ·
          refine ⟨12028466874296000093697575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018977916197333395798383 12028466874296000093697575)
          ·
            refine ⟨18042700311444000140546363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028466874296000093697575 18042700311444000140546363)
            ·
              refine ⟨27064050467166000210819545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042700311444000140546363 27064050467166000210819545)
              ·
                refine ⟨20298037850374500158114659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27064050467166000210819545 20298037850374500158114659)
                ·
                  refine ⟨30447056775561750237171989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20298037850374500158114659 30447056775561750237171989)
                  ·
                    refine ⟨1427205786354457042367437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30447056775561750237171989 1427205786354457042367437)
                    ·
                      rfl

theorem cell23_8338420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8338420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338420 prefixEnd_8338420 := by exact prefixLift 8338420
  have htrace : WordTrace (prefixWord ++ tailWord_8338420) baseStart_8338420 baseEnd_8338420 := by
    simpa [prefixWord, tailWord_8338420, baseEnd_8338420] using wordTrace_append hprefix tailTrace_8338420
  have hstable : (prefixWord ++ tailWord_8338420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338420).length < 2 ^ (prefixWord ++ tailWord_8338420).sum := by decide
  have hdescent : baseEnd_8338420 < baseStart_8338420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338430 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_8338430 : Nat := 118140960795 + 8338430 * 2 ^ 59
def prefixEnd_8338430 : Nat := 4983230072969 + 3 ^ 40 * 8338430 * 2
def baseEnd_8338430 : Nat := 4281622493869916087977265

theorem tailTrace_8338430 : CollatzResearch.WordTrace tailWord_8338430 prefixEnd_8338430 4281622493869916087977265 := by
  unfold tailWord_8338430
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015940897662459413934593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202751684787533116874317829 38015940897662459413934593)
  ·
    refine ⟨28511955673246844560450945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38015940897662459413934593 28511955673246844560450945)
    ·
      refine ⟨21383966754935133420338209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28511955673246844560450945 21383966754935133420338209)
      ·
        refine ⟨16037975066201350065253657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21383966754935133420338209 16037975066201350065253657)
        ·
          refine ⟨12028481299651012548940243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16037975066201350065253657 12028481299651012548940243)
          ·
            refine ⟨18042721949476518823410365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028481299651012548940243 18042721949476518823410365)
            ·
              refine ⟨6766020731053694558778887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18042721949476518823410365 6766020731053694558778887)
              ·
                refine ⟨10149031096580541838168331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766020731053694558778887 10149031096580541838168331)
                ·
                  refine ⟨15223546644870812757252497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10149031096580541838168331 15223546644870812757252497)
                  ·
                    refine ⟨11417659983653109567939373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15223546644870812757252497 11417659983653109567939373)
                    ·
                      refine ⟨4281622493869916087977265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11417659983653109567939373 4281622493869916087977265)
                      ·
                        rfl

theorem cell23_8338430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_8338430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338430 prefixEnd_8338430 := by exact prefixLift 8338430
  have htrace : WordTrace (prefixWord ++ tailWord_8338430) baseStart_8338430 baseEnd_8338430 := by
    simpa [prefixWord, tailWord_8338430, baseEnd_8338430] using wordTrace_append hprefix tailTrace_8338430
  have hstable : (prefixWord ++ tailWord_8338430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338430).length < 2 ^ (prefixWord ++ tailWord_8338430).sum := by decide
  have hdescent : baseEnd_8338430 < baseStart_8338430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338450 : List Nat := [3, 2, 5, 1, 2, 1, 1, 8]
def baseStart_8338450 : Nat := 118140960795 + 8338450 * 2 ^ 59
def prefixEnd_8338450 : Nat := 4983230072969 + 3 ^ 40 * 8338450 * 2
def baseEnd_8338450 : Nat := 158578991240111333693599

theorem tailTrace_8338450 : CollatzResearch.WordTrace tailWord_8338450 prefixEnd_8338450 158578991240111333693599 := by
  unfold tailWord_8338450
  simp only [CollatzResearch.WordTrace]
  refine ⟨76032064160306804681801201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202752171094151479151469869 76032064160306804681801201)
  ·
    refine ⟨57024048120230103511350901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76032064160306804681801201 57024048120230103511350901)
    ·
      refine ⟨5346004511271572204189147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57024048120230103511350901 5346004511271572204189147)
      ·
        refine ⟨8019006766907358306283721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346004511271572204189147 8019006766907358306283721)
        ·
          refine ⟨6014255075180518729712791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019006766907358306283721 6014255075180518729712791)
          ·
            refine ⟨9021382612770778094569187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014255075180518729712791 9021382612770778094569187)
            ·
              refine ⟨13532073919156167141853781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021382612770778094569187 13532073919156167141853781)
              ·
                refine ⟨158578991240111333693599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13532073919156167141853781 158578991240111333693599)
                ·
                  rfl

theorem cell23_8338450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_8338450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338450 prefixEnd_8338450 := by exact prefixLift 8338450
  have htrace : WordTrace (prefixWord ++ tailWord_8338450) baseStart_8338450 baseEnd_8338450 := by
    simpa [prefixWord, tailWord_8338450, baseEnd_8338450] using wordTrace_append hprefix tailTrace_8338450
  have hstable : (prefixWord ++ tailWord_8338450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338450).length < 2 ^ (prefixWord ++ tailWord_8338450).sum := by decide
  have hdescent : baseEnd_8338450 < baseStart_8338450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338466 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_8338466 : Nat := 118140960795 + 8338466 * 2 ^ 59
def prefixEnd_8338466 : Nat := 4983230072969 + 3 ^ 40 * 8338466 * 2
def baseEnd_8338466 : Nat := 4281640979173477947127099

theorem tailTrace_8338466 : CollatzResearch.WordTrace tailWord_8338466 prefixEnd_8338466 4281640979173477947127099 := by
  unfold tailWord_8338466
  simp only [CollatzResearch.WordTrace]
  refine ⟨76032210052292313364946813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202752560139446168973191501 76032210052292313364946813)
  ·
    refine ⟨28512078769609617511855055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76032210052292313364946813 28512078769609617511855055)
    ·
      refine ⟨42768118154414426267782583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28512078769609617511855055 42768118154414426267782583)
      ·
        refine ⟨64152177231621639401673875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42768118154414426267782583 64152177231621639401673875)
        ·
          refine ⟨96228265847432459102510813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64152177231621639401673875 96228265847432459102510813)
          ·
            refine ⟨36085599692787172163441555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96228265847432459102510813 36085599692787172163441555)
            ·
              refine ⟨54128399539180758245162333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36085599692787172163441555 54128399539180758245162333)
              ·
                refine ⟨20298149827192784341935875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54128399539180758245162333 20298149827192784341935875)
                ·
                  refine ⟨30447224740789176512903813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20298149827192784341935875 30447224740789176512903813)
                  ·
                    refine ⟨5708854638897970596169465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30447224740789176512903813 5708854638897970596169465)
                    ·
                      refine ⟨4281640979173477947127099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708854638897970596169465 4281640979173477947127099)
                      ·
                        rfl

theorem cell23_8338466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_8338466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338466 prefixEnd_8338466 := by exact prefixLift 8338466
  have htrace : WordTrace (prefixWord ++ tailWord_8338466) baseStart_8338466 baseEnd_8338466 := by
    simpa [prefixWord, tailWord_8338466, baseEnd_8338466] using wordTrace_append hprefix tailTrace_8338466
  have hstable : (prefixWord ++ tailWord_8338466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338466).length < 2 ^ (prefixWord ++ tailWord_8338466).sum := by decide
  have hdescent : baseEnd_8338466 < baseStart_8338466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338512 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_8338512 : Nat := 118140960795 + 8338512 * 2 ^ 59
def prefixEnd_8338512 : Nat := 4983230072969 + 3 ^ 40 * 8338512 * 2
def baseEnd_8338512 : Nat := 4281664599283584767151887

theorem tailTrace_8338512 : CollatzResearch.WordTrace tailWord_8338512 prefixEnd_8338512 4281664599283584767151887 := by
  unfold tailWord_8338512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152065258983501301657980895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202753678644668402210641193 152065258983501301657980895)
  ·
    refine ⟨228097888475251952486971343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152065258983501301657980895 228097888475251952486971343)
    ·
      refine ⟨342146832712877928730457015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228097888475251952486971343 342146832712877928730457015)
      ·
        refine ⟨513220249069316893095685523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342146832712877928730457015 513220249069316893095685523)
        ·
          refine ⟨769830373603975339643528285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513220249069316893095685523 769830373603975339643528285)
          ·
            refine ⟨288686390101490752366323107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769830373603975339643528285 288686390101490752366323107)
            ·
              refine ⟨433029585152236128549484661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288686390101490752366323107 433029585152236128549484661)
              ·
                refine ⟨40596523608022137051514187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433029585152236128549484661 40596523608022137051514187)
                ·
                  refine ⟨60894785412033205577271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40596523608022137051514187 60894785412033205577271281)
                  ·
                    refine ⟨45671089059024904182953461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60894785412033205577271281 45671089059024904182953461)
                    ·
                      refine ⟨4281664599283584767151887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45671089059024904182953461 4281664599283584767151887)
                      ·
                        rfl

theorem cell23_8338512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_8338512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338512 prefixEnd_8338512 := by exact prefixLift 8338512
  have htrace : WordTrace (prefixWord ++ tailWord_8338512) baseStart_8338512 baseEnd_8338512 := by
    simpa [prefixWord, tailWord_8338512, baseEnd_8338512] using wordTrace_append hprefix tailTrace_8338512
  have hstable : (prefixWord ++ tailWord_8338512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338512).length < 2 ^ (prefixWord ++ tailWord_8338512).sum := by decide
  have hdescent : baseEnd_8338512 < baseStart_8338512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338532 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_8338532 : Nat := 118140960795 + 8338532 * 2 ^ 59
def prefixEnd_8338532 : Nat := 4983230072969 + 3 ^ 40 * 8338532 * 2
def baseEnd_8338532 : Nat := 1427224956298891562967265

theorem tailTrace_8338532 : CollatzResearch.WordTrace tailWord_8338532 prefixEnd_8338532 1427224956298891562967265 := by
  unfold tailWord_8338532
  simp only [CollatzResearch.WordTrace]
  refine ⟨152065623713465073365844925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202754164951286764487793233 152065623713465073365844925)
  ·
    refine ⟨57024608892549402512191847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152065623713465073365844925 57024608892549402512191847)
    ·
      refine ⟨85536913338824103768287771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57024608892549402512191847 85536913338824103768287771)
      ·
        refine ⟨128305370008236155652431657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85536913338824103768287771 128305370008236155652431657)
        ·
          refine ⟨96229027506177116739323743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128305370008236155652431657 96229027506177116739323743)
          ·
            refine ⟨144343541259265675108985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96229027506177116739323743 144343541259265675108985615)
            ·
              refine ⟨216515311888898512663478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144343541259265675108985615 216515311888898512663478423)
              ·
                refine ⟨324772967833347768995217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216515311888898512663478423 324772967833347768995217635)
                ·
                  refine ⟨487159451750021653492826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324772967833347768995217635 487159451750021653492826453)
                  ·
                    refine ⟨1427224956298891562967265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 487159451750021653492826453 1427224956298891562967265)
                    ·
                      rfl

theorem cell23_8338532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_8338532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338532 prefixEnd_8338532 := by exact prefixLift 8338532
  have htrace : WordTrace (prefixWord ++ tailWord_8338532) baseStart_8338532 baseEnd_8338532 := by
    simpa [prefixWord, tailWord_8338532, baseEnd_8338532] using wordTrace_append hprefix tailTrace_8338532
  have hstable : (prefixWord ++ tailWord_8338532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338532).length < 2 ^ (prefixWord ++ tailWord_8338532).sum := by decide
  have hdescent : baseEnd_8338532 < baseStart_8338532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338552 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_8338552 : Nat := 118140960795 + 8338552 * 2 ^ 59
def prefixEnd_8338552 : Nat := 4983230072969 + 3 ^ 40 * 8338552 * 2
def baseEnd_8338552 : Nat := 4281685138509764610651703

theorem tailTrace_8338552 : CollatzResearch.WordTrace tailWord_8338552 prefixEnd_8338552 4281685138509764610651703 := by
  unfold tailWord_8338552
  simp only [CollatzResearch.WordTrace]
  refine ⟨152065988443428845073708955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202754651257905126764945273 152065988443428845073708955)
  ·
    refine ⟨228098982665143267610563433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152065988443428845073708955 228098982665143267610563433)
    ·
      refine ⟨171074236998857450707922575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228098982665143267610563433 171074236998857450707922575)
      ·
        refine ⟨256611355498286176061883863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171074236998857450707922575 256611355498286176061883863)
        ·
          refine ⟨384917033247429264092825795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256611355498286176061883863 384917033247429264092825795)
          ·
            refine ⟨577375549871143896139238693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384917033247429264092825795 577375549871143896139238693)
            ·
              refine ⟨108257915600839480526107255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577375549871143896139238693 108257915600839480526107255)
              ·
                refine ⟨162386873401259220789160883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108257915600839480526107255 162386873401259220789160883)
                ·
                  refine ⟨243580310101888831183741325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162386873401259220789160883 243580310101888831183741325)
                  ·
                    refine ⟨91342616288208311693902997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243580310101888831183741325 91342616288208311693902997)
                    ·
                      refine ⟨4281685138509764610651703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91342616288208311693902997 4281685138509764610651703)
                      ·
                        rfl

theorem cell23_8338552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_8338552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338552 prefixEnd_8338552 := by exact prefixLift 8338552
  have htrace : WordTrace (prefixWord ++ tailWord_8338552) baseStart_8338552 baseEnd_8338552 := by
    simpa [prefixWord, tailWord_8338552, baseEnd_8338552] using wordTrace_append hprefix tailTrace_8338552
  have hstable : (prefixWord ++ tailWord_8338552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338552).length < 2 ^ (prefixWord ++ tailWord_8338552).sum := by decide
  have hdescent : baseEnd_8338552 < baseStart_8338552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_8338616 : Nat := 118140960795 + 8338616 * 2 ^ 59
def prefixEnd_8338616 : Nat := 4983230072969 + 3 ^ 40 * 8338616 * 2
def baseEnd_8338616 : Nat := 4281718001271652360251409

theorem tailTrace_8338616 : CollatzResearch.WordTrace tailWord_8338616 prefixEnd_8338616 4281718001271652360251409 := by
  unfold tailWord_8338616
  simp only [CollatzResearch.WordTrace]
  refine ⟨152067155579312914538873851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202756207439083886051831801 152067155579312914538873851)
  ·
    refine ⟨228100733368969371808310777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152067155579312914538873851 228100733368969371808310777)
    ·
      refine ⟨171075550026727028856233083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228100733368969371808310777 171075550026727028856233083)
      ·
        refine ⟨256613325040090543284349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171075550026727028856233083 256613325040090543284349625)
        ·
          refine ⟨192459993780067907463262219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256613325040090543284349625 192459993780067907463262219)
          ·
            refine ⟨288689990670101861194893329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192459993780067907463262219 288689990670101861194893329)
            ·
              refine ⟨216517493002576395896169997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288689990670101861194893329 216517493002576395896169997)
              ·
                refine ⟨81194059875966148461063749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216517493002576395896169997 81194059875966148461063749)
                ·
                  refine ⟨15223886226743652836449453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81194059875966148461063749 15223886226743652836449453)
                  ·
                    refine ⟨5708957335028869813668545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15223886226743652836449453 5708957335028869813668545)
                    ·
                      refine ⟨4281718001271652360251409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5708957335028869813668545 4281718001271652360251409)
                      ·
                        rfl

theorem cell23_8338616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_8338616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338616 prefixEnd_8338616 := by exact prefixLift 8338616
  have htrace : WordTrace (prefixWord ++ tailWord_8338616) baseStart_8338616 baseEnd_8338616 := by
    simpa [prefixWord, tailWord_8338616, baseEnd_8338616] using wordTrace_append hprefix tailTrace_8338616
  have hstable : (prefixWord ++ tailWord_8338616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338616).length < 2 ^ (prefixWord ++ tailWord_8338616).sum := by decide
  have hdescent : baseEnd_8338616 < baseStart_8338616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338690 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_8338690 : Nat := 118140960795 + 8338690 * 2 ^ 59
def prefixEnd_8338690 : Nat := 4983230072969 + 3 ^ 40 * 8338690 * 2
def baseEnd_8338690 : Nat := 1427251999613361690242023

theorem tailTrace_8338690 : CollatzResearch.WordTrace tailWord_8338690 prefixEnd_8338690 1427251999613361690242023 := by
  unfold tailWord_8338690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76034252540089434928985381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202758006773571826477294349 76034252540089434928985381)
  ·
    refine ⟨14256422351266769049184759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76034252540089434928985381 14256422351266769049184759)
    ·
      refine ⟨21384633526900153573777139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256422351266769049184759 21384633526900153573777139)
      ·
        refine ⟨32076950290350230360665709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384633526900153573777139 32076950290350230360665709)
        ·
          refine ⟨12028856358881336385249641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32076950290350230360665709 12028856358881336385249641)
          ·
            refine ⟨9021642269161002288937231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12028856358881336385249641 9021642269161002288937231)
            ·
              refine ⟨13532463403741503433405847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021642269161002288937231 13532463403741503433405847)
              ·
                refine ⟨20298695105612255150108771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13532463403741503433405847 20298695105612255150108771)
                ·
                  refine ⟨30448042658418382725163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20298695105612255150108771 30448042658418382725163157)
                  ·
                    refine ⟨1427251999613361690242023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30448042658418382725163157 1427251999613361690242023)
                    ·
                      rfl

theorem cell23_8338690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_8338690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338690 prefixEnd_8338690 := by exact prefixLift 8338690
  have htrace : WordTrace (prefixWord ++ tailWord_8338690) baseStart_8338690 baseEnd_8338690 := by
    simpa [prefixWord, tailWord_8338690, baseEnd_8338690] using wordTrace_append hprefix tailTrace_8338690
  have hstable : (prefixWord ++ tailWord_8338690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338690).length < 2 ^ (prefixWord ++ tailWord_8338690).sum := by decide
  have hdescent : baseEnd_8338690 < baseStart_8338690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338714 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_8338714 : Nat := 118140960795 + 8338714 * 2 ^ 59
def prefixEnd_8338714 : Nat := 4983230072969 + 3 ^ 40 * 8338714 * 2
def baseEnd_8338714 : Nat := 4281768322375792976825959

theorem tailTrace_8338714 : CollatzResearch.WordTrace tailWord_8338714 prefixEnd_8338714 4281768322375792976825959 := by
  unfold tailWord_8338714
  simp only [CollatzResearch.WordTrace]
  refine ⟨76034471378067697953703799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202758590341513861209876797 76034471378067697953703799)
  ·
    refine ⟨114051707067101546930555699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76034471378067697953703799 114051707067101546930555699)
    ·
      refine ⟨171077560600652320395833549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114051707067101546930555699 171077560600652320395833549)
      ·
        refine ⟨64154085225244620148437581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171077560600652320395833549 64154085225244620148437581)
        ·
          refine ⟨24057781959466732555664093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64154085225244620148437581 24057781959466732555664093)
          ·
            refine ⟨9021668234800024708374035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24057781959466732555664093 9021668234800024708374035)
            ·
              refine ⟨13532502352200037062561053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021668234800024708374035 13532502352200037062561053)
              ·
                refine ⟨5074688382075013898460395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13532502352200037062561053 5074688382075013898460395)
                ·
                  refine ⟨7612032573112520847690593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074688382075013898460395 7612032573112520847690593)
                  ·
                    refine ⟨5709024429834390635767945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7612032573112520847690593 5709024429834390635767945)
                    ·
                      refine ⟨4281768322375792976825959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709024429834390635767945 4281768322375792976825959)
                      ·
                        rfl

theorem cell23_8338714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_8338714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338714 prefixEnd_8338714 := by exact prefixLift 8338714
  have htrace : WordTrace (prefixWord ++ tailWord_8338714) baseStart_8338714 baseEnd_8338714 := by
    simpa [prefixWord, tailWord_8338714, baseEnd_8338714] using wordTrace_append hprefix tailTrace_8338714
  have hstable : (prefixWord ++ tailWord_8338714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338714).length < 2 ^ (prefixWord ++ tailWord_8338714).sum := by decide
  have hdescent : baseEnd_8338714 < baseStart_8338714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338730 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_8338730 : Nat := 118140960795 + 8338730 * 2 ^ 59
def prefixEnd_8338730 : Nat := 4983230072969 + 3 ^ 40 * 8338730 * 2
def baseEnd_8338730 : Nat := 4281776538066264914225885

theorem tailTrace_8338730 : CollatzResearch.WordTrace tailWord_8338730 prefixEnd_8338730 4281776538066264914225885 := by
  unfold tailWord_8338730
  simp only [CollatzResearch.WordTrace]
  refine ⟨76034617270053206636849411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202758979386808551031598429 76034617270053206636849411)
  ·
    refine ⟨114051925905079809955274117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76034617270053206636849411 114051925905079809955274117)
    ·
      refine ⟨21384736107202464366613897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114051925905079809955274117 21384736107202464366613897)
      ·
        refine ⟨16038552080401848274960423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21384736107202464366613897 16038552080401848274960423)
        ·
          refine ⟨24057828120602772412440635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038552080401848274960423 24057828120602772412440635)
          ·
            refine ⟨36086742180904158618660953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24057828120602772412440635 36086742180904158618660953)
            ·
              refine ⟨27065056635678118963995715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36086742180904158618660953 27065056635678118963995715)
              ·
                refine ⟨40597584953517178445993573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27065056635678118963995715 40597584953517178445993573)
                ·
                  refine ⟨7612047178784470958623795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40597584953517178445993573 7612047178784470958623795)
                  ·
                    refine ⟨11418070768176706437935693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7612047178784470958623795 11418070768176706437935693)
                    ·
                      refine ⟨4281776538066264914225885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11418070768176706437935693 4281776538066264914225885)
                      ·
                        rfl

theorem cell23_8338730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_8338730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338730 prefixEnd_8338730 := by exact prefixLift 8338730
  have htrace : WordTrace (prefixWord ++ tailWord_8338730) baseStart_8338730 baseEnd_8338730 := by
    simpa [prefixWord, tailWord_8338730, baseEnd_8338730] using wordTrace_append hprefix tailTrace_8338730
  have hstable : (prefixWord ++ tailWord_8338730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338730).length < 2 ^ (prefixWord ++ tailWord_8338730).sum := by decide
  have hdescent : baseEnd_8338730 < baseStart_8338730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338740 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_8338740 : Nat := 118140960795 + 8338740 * 2 ^ 59
def prefixEnd_8338740 : Nat := 4983230072969 + 3 ^ 40 * 8338740 * 2
def baseEnd_8338740 : Nat := 4281781672872809875100839

theorem tailTrace_8338740 : CollatzResearch.WordTrace tailWord_8338740 prefixEnd_8338740 4281781672872809875100839 := by
  unfold tailWord_8338740
  simp only [CollatzResearch.WordTrace]
  refine ⟨152069416905088299127630837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202759222540117732170174449 152069416905088299127630837)
  ·
    refine ⟨14256507834852028043215391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152069416905088299127630837 14256507834852028043215391)
    ·
      refine ⟨21384761752278042064823087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256507834852028043215391 21384761752278042064823087)
      ·
        refine ⟨32077142628417063097234631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384761752278042064823087 32077142628417063097234631)
        ·
          refine ⟨48115713942625594645851947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32077142628417063097234631 48115713942625594645851947)
          ·
            refine ⟨72173570913938391968777921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48115713942625594645851947 72173570913938391968777921)
            ·
              refine ⟨54130178185453793976583441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72173570913938391968777921 54130178185453793976583441)
              ·
                refine ⟨40597633639090345482437581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54130178185453793976583441 40597633639090345482437581)
                ·
                  refine ⟨15224112614658879555914093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40597633639090345482437581 15224112614658879555914093)
                  ·
                    refine ⟨5709042230497079833467785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15224112614658879555914093 5709042230497079833467785)
                    ·
                      refine ⟨4281781672872809875100839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709042230497079833467785 4281781672872809875100839)
                      ·
                        rfl

theorem cell23_8338740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_8338740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338740 prefixEnd_8338740 := by exact prefixLift 8338740
  have htrace : WordTrace (prefixWord ++ tailWord_8338740) baseStart_8338740 baseEnd_8338740 := by
    simpa [prefixWord, tailWord_8338740, baseEnd_8338740] using wordTrace_append hprefix tailTrace_8338740
  have hstable : (prefixWord ++ tailWord_8338740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338740).length < 2 ^ (prefixWord ++ tailWord_8338740).sum := by decide
  have hdescent : baseEnd_8338740 < baseStart_8338740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338781 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8338781 : Nat := 118140960795 + 8338781 * 2 ^ 59
def prefixEnd_8338781 : Nat := 4983230072969 + 3 ^ 40 * 8338781 * 2
def baseEnd_8338781 : Nat := 4281802725579644214688151

theorem tailTrace_8338781 : CollatzResearch.WordTrace tailWord_8338781 prefixEnd_8338781 4281802725579644214688151 := by
  unfold tailWord_8338781
  simp only [CollatzResearch.WordTrace]
  refine ⟨304140329203028062257504197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202760219468685374838336131 304140329203028062257504197)
  ·
    refine ⟨57026311725567761673282037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304140329203028062257504197 57026311725567761673282037)
    ·
      refine ⟨5346216724271977656870191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57026311725567761673282037 5346216724271977656870191)
      ·
        refine ⟨8019325086407966485305287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346216724271977656870191 8019325086407966485305287)
        ·
          refine ⟨12028987629611949727957931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019325086407966485305287 12028987629611949727957931)
          ·
            refine ⟨18043481444417924591936897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028987629611949727957931 18043481444417924591936897)
            ·
              refine ⟨13532611083313443443952673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18043481444417924591936897 13532611083313443443952673)
              ·
                refine ⟨10149458312485082582964505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13532611083313443443952673 10149458312485082582964505)
                ·
                  refine ⟨7612093734363811937223379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10149458312485082582964505 7612093734363811937223379)
                  ·
                    refine ⟨11418140601545717905835069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7612093734363811937223379 11418140601545717905835069)
                    ·
                      refine ⟨4281802725579644214688151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11418140601545717905835069 4281802725579644214688151)
                      ·
                        rfl

theorem cell23_8338781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8338781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338781 prefixEnd_8338781 := by exact prefixLift 8338781
  have htrace : WordTrace (prefixWord ++ tailWord_8338781) baseStart_8338781 baseEnd_8338781 := by
    simpa [prefixWord, tailWord_8338781, baseEnd_8338781] using wordTrace_append hprefix tailTrace_8338781
  have hstable : (prefixWord ++ tailWord_8338781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338781).length < 2 ^ (prefixWord ++ tailWord_8338781).sum := by decide
  have hdescent : baseEnd_8338781 < baseStart_8338781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338787 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 2, 2, 2]
def baseStart_8338787 : Nat := 118140960795 + 8338787 * 2 ^ 59
def prefixEnd_8338787 : Nat := 4983230072969 + 3 ^ 40 * 8338787 * 2
def baseEnd_8338787 : Nat := 4281805806463571191213123

theorem tailTrace_8338787 : CollatzResearch.WordTrace tailWord_8338787 prefixEnd_8338787 4281805806463571191213123 := by
  unfold tailWord_8338787
  simp only [CollatzResearch.WordTrace]
  refine ⟨304140548041006325282222615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202760365360670883521481743 304140548041006325282222615)
  ·
    refine ⟨456210822061509487923333923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304140548041006325282222615 456210822061509487923333923)
    ·
      refine ⟨684316233092264231885000885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456210822061509487923333923 684316233092264231885000885)
      ·
        refine ⟨64154646852399771739218833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 684316233092264231885000885 64154646852399771739218833)
        ·
          refine ⟨48115985139299828804414125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64154646852399771739218833 48115985139299828804414125)
          ·
            refine ⟨18043494427237435801655297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48115985139299828804414125 18043494427237435801655297)
            ·
              refine ⟨13532620820428076851241473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18043494427237435801655297 13532620820428076851241473)
              ·
                refine ⟨10149465615321057638431105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13532620820428076851241473 10149465615321057638431105)
                ·
                  refine ⟨7612099211490793228823329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10149465615321057638431105 7612099211490793228823329)
                  ·
                    refine ⟨5709074408618094921617497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7612099211490793228823329 5709074408618094921617497)
                    ·
                      refine ⟨4281805806463571191213123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709074408618094921617497 4281805806463571191213123)
                      ·
                        rfl

theorem cell23_8338787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_8338787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338787 prefixEnd_8338787 := by exact prefixLift 8338787
  have htrace : WordTrace (prefixWord ++ tailWord_8338787) baseStart_8338787 baseEnd_8338787 := by
    simpa [prefixWord, tailWord_8338787, baseEnd_8338787] using wordTrace_append hprefix tailTrace_8338787
  have hstable : (prefixWord ++ tailWord_8338787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338787).length < 2 ^ (prefixWord ++ tailWord_8338787).sum := by decide
  have hdescent : baseEnd_8338787 < baseStart_8338787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338813 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_8338813 : Nat := 118140960795 + 8338813 * 2 ^ 59
def prefixEnd_8338813 : Nat := 4983230072969 + 3 ^ 40 * 8338813 * 2
def baseEnd_8338813 : Nat := 4281819156960588089488003

theorem tailTrace_8338813 : CollatzResearch.WordTrace tailWord_8338813 prefixEnd_8338813 4281819156960588089488003 := by
  unfold tailWord_8338813
  simp only [CollatzResearch.WordTrace]
  refine ⟨304141496338912131722669093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202760997559274754481779395 304141496338912131722669093)
  ·
    refine ⟨57026530563546024698000455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304141496338912131722669093 57026530563546024698000455)
    ·
      refine ⟨85539795845319037047000683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57026530563546024698000455 85539795845319037047000683)
      ·
        refine ⟨128309693767978555570501025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85539795845319037047000683 128309693767978555570501025)
        ·
          refine ⟨96232270325983916677875769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128309693767978555570501025 96232270325983916677875769)
          ·
            refine ⟨72174202744487937508406827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96232270325983916677875769 72174202744487937508406827)
            ·
              refine ⟨108261304116731906262610241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72174202744487937508406827 108261304116731906262610241)
              ·
                refine ⟨81195978087548929696957681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108261304116731906262610241 81195978087548929696957681)
                ·
                  refine ⟨60896983565661697272718261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81195978087548929696957681 60896983565661697272718261)
                  ·
                    refine ⟨5709092209280784119317337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60896983565661697272718261 5709092209280784119317337)
                    ·
                      refine ⟨4281819156960588089488003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709092209280784119317337 4281819156960588089488003)
                      ·
                        rfl

theorem cell23_8338813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_8338813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338813 prefixEnd_8338813 := by exact prefixLift 8338813
  have htrace : WordTrace (prefixWord ++ tailWord_8338813) baseStart_8338813 baseEnd_8338813 := by
    simpa [prefixWord, tailWord_8338813, baseEnd_8338813] using wordTrace_append hprefix tailTrace_8338813
  have hstable : (prefixWord ++ tailWord_8338813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338813).length < 2 ^ (prefixWord ++ tailWord_8338813).sum := by decide
  have hdescent : baseEnd_8338813 < baseStart_8338813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338823 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 2, 5]
def baseStart_8338823 : Nat := 118140960795 + 8338823 * 2 ^ 59
def prefixEnd_8338823 : Nat := 4983230072969 + 3 ^ 40 * 8338823 * 2
def baseEnd_8338823 : Nat := 1427274763922377683454319

theorem tailTrace_8338823 : CollatzResearch.WordTrace tailWord_8338823 prefixEnd_8338823 1427274763922377683454319 := by
  unfold tailWord_8338823
  simp only [CollatzResearch.WordTrace]
  refine ⟨304141861068875903430533123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202761240712583935620355415 304141861068875903430533123)
  ·
    refine ⟨456212791603313855145799685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304141861068875903430533123 456212791603313855145799685)
    ·
      refine ⟨85539898425621347839837441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456212791603313855145799685 85539898425621347839837441)
      ·
        refine ⟨64154923819216010879878081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85539898425621347839837441 64154923819216010879878081)
        ·
          refine ⟨48116192864412008159908561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64154923819216010879878081 48116192864412008159908561)
          ·
            refine ⟨36087144648309006119931421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48116192864412008159908561 36087144648309006119931421)
            ·
              refine ⟨13532679243115877294974283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36087144648309006119931421 13532679243115877294974283)
              ·
                refine ⟨20299018864673815942461425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13532679243115877294974283 20299018864673815942461425)
                ·
                  refine ⟨15224264148505361956846069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20299018864673815942461425 15224264148505361956846069)
                  ·
                    refine ⟨1427274763922377683454319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15224264148505361956846069 1427274763922377683454319)
                    ·
                      rfl

theorem cell23_8338823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_8338823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338823 prefixEnd_8338823 := by exact prefixLift 8338823
  have htrace : WordTrace (prefixWord ++ tailWord_8338823) baseStart_8338823 baseEnd_8338823 := by
    simpa [prefixWord, tailWord_8338823, baseEnd_8338823] using wordTrace_append hprefix tailTrace_8338823
  have hstable : (prefixWord ++ tailWord_8338823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338823).length < 2 ^ (prefixWord ++ tailWord_8338823).sum := by decide
  have hdescent : baseEnd_8338823 < baseStart_8338823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338917 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 6]
def baseStart_8338917 : Nat := 118140960795 + 8338917 * 2 ^ 59
def prefixEnd_8338917 : Nat := 4983230072969 + 3 ^ 40 * 8338917 * 2
def baseEnd_8338917 : Nat := 475763617660961742509725

theorem tailTrace_8338917 : CollatzResearch.WordTrace tailWord_8338917 prefixEnd_8338917 475763617660961742509725 := by
  unfold tailWord_8338917
  simp only [CollatzResearch.WordTrace]
  refine ⟨304145289530535357484455005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202763526353690238322970003 304145289530535357484455005)
  ·
    refine ⟨114054483573950759056670627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304145289530535357484455005 114054483573950759056670627)
    ·
      refine ⟨171081725360926138585005941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114054483573950759056670627 171081725360926138585005941)
      ·
        refine ⟨16038911752586825492344307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171081725360926138585005941 16038911752586825492344307)
        ·
          refine ⟨24058367628880238238516461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038911752586825492344307 24058367628880238238516461)
          ·
            refine ⟨9021887860830089339443673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24058367628880238238516461 9021887860830089339443673)
            ·
              refine ⟨6766415895622567004582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021887860830089339443673 6766415895622567004582755)
              ·
                refine ⟨10149623843433850506874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766415895622567004582755 10149623843433850506874133)
                ·
                  refine ⟨475763617660961742509725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10149623843433850506874133 475763617660961742509725)
                  ·
                    rfl

theorem cell23_8338917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_8338917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338917 prefixEnd_8338917 := by exact prefixLift 8338917
  have htrace : WordTrace (prefixWord ++ tailWord_8338917) baseStart_8338917 baseEnd_8338917 := by
    simpa [prefixWord, tailWord_8338917, baseEnd_8338917] using wordTrace_append hprefix tailTrace_8338917
  have hstable : (prefixWord ++ tailWord_8338917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338917).length < 2 ^ (prefixWord ++ tailWord_8338917).sum := by decide
  have hdescent : baseEnd_8338917 < baseStart_8338917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338920 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_8338920 : Nat := 118140960795 + 8338920 * 2 ^ 59
def prefixEnd_8338920 : Nat := 4983230072969 + 3 ^ 40 * 8338920 * 2
def baseEnd_8338920 : Nat := 4281874099390619170850011

theorem tailTrace_8338920 : CollatzResearch.WordTrace tailWord_8338920 prefixEnd_8338920 4281874099390619170850011 := by
  unfold tailWord_8338920
  simp only [CollatzResearch.WordTrace]
  refine ⟨152072699474762244498407107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202763599299682992664542809 152072699474762244498407107)
  ·
    refine ⟨228109049212143366747610661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152072699474762244498407107 228109049212143366747610661)
    ·
      refine ⟨42770446727276881265176999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228109049212143366747610661 42770446727276881265176999)
      ·
        refine ⟨64155670090915321897765499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42770446727276881265176999 64155670090915321897765499)
        ·
          refine ⟨96233505136372982846648249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64155670090915321897765499 96233505136372982846648249)
          ·
            refine ⟨72175128852279737134986187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96233505136372982846648249 72175128852279737134986187)
            ·
              refine ⟨108262693278419605702479281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72175128852279737134986187 108262693278419605702479281)
              ·
                refine ⟨81197019958814704276859461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108262693278419605702479281 81197019958814704276859461)
                ·
                  refine ⟨15224441242277757051911149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81197019958814704276859461 15224441242277757051911149)
                  ·
                    refine ⟨5709165465854158894466681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15224441242277757051911149 5709165465854158894466681)
                    ·
                      refine ⟨4281874099390619170850011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709165465854158894466681 4281874099390619170850011)
                      ·
                        rfl

theorem cell23_8338920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_8338920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338920 prefixEnd_8338920 := by exact prefixLift 8338920
  have htrace : WordTrace (prefixWord ++ tailWord_8338920) baseStart_8338920 baseEnd_8338920 := by
    simpa [prefixWord, tailWord_8338920, baseEnd_8338920] using wordTrace_append hprefix tailTrace_8338920
  have hstable : (prefixWord ++ tailWord_8338920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338920).length < 2 ^ (prefixWord ++ tailWord_8338920).sum := by decide
  have hdescent : baseEnd_8338920 < baseStart_8338920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338930 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_8338930 : Nat := 118140960795 + 8338930 * 2 ^ 59
def prefixEnd_8338930 : Nat := 4983230072969 + 3 ^ 40 * 8338930 * 2
def baseEnd_8338930 : Nat := 1427293078065721377241655

theorem tailTrace_8338930 : CollatzResearch.WordTrace tailWord_8338930 prefixEnd_8338930 1427293078065721377241655 := by
  unfold tailWord_8338930
  simp only [CollatzResearch.WordTrace]
  refine ⟨76036440919872065176169561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202763842452992173803118829 76036440919872065176169561)
  ·
    refine ⟨57027330689904048882127171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76036440919872065176169561 57027330689904048882127171)
    ·
      refine ⟨85540996034856073323190757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57027330689904048882127171 85540996034856073323190757)
      ·
        refine ⟨16038936756535513748098267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85540996034856073323190757 16038936756535513748098267)
        ·
          refine ⟨24058405134803270622147401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038936756535513748098267 24058405134803270622147401)
          ·
            refine ⟨18043803851102452966610551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24058405134803270622147401 18043803851102452966610551)
            ·
              refine ⟨27065705776653679449915827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18043803851102452966610551 27065705776653679449915827)
              ·
                refine ⟨40598558664980519174873741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27065705776653679449915827 40598558664980519174873741)
                ·
                  refine ⟨15224459499367694690577653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40598558664980519174873741 15224459499367694690577653)
                  ·
                    refine ⟨1427293078065721377241655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15224459499367694690577653 1427293078065721377241655)
                    ·
                      rfl

theorem cell23_8338930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_8338930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338930 prefixEnd_8338930 := by exact prefixLift 8338930
  have htrace : WordTrace (prefixWord ++ tailWord_8338930) baseStart_8338930 baseEnd_8338930 := by
    simpa [prefixWord, tailWord_8338930, baseEnd_8338930] using wordTrace_append hprefix tailTrace_8338930
  have hstable : (prefixWord ++ tailWord_8338930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338930).length < 2 ^ (prefixWord ++ tailWord_8338930).sum := by decide
  have hdescent : baseEnd_8338930 < baseStart_8338930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338943 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 4, 4]
def baseStart_8338943 : Nat := 118140960795 + 8338943 * 2 ^ 59
def prefixEnd_8338943 : Nat := 4983230072969 + 3 ^ 40 * 8338943 * 2
def baseEnd_8338943 : Nat := 1427295303148557526954135

theorem tailTrace_8338943 : CollatzResearch.WordTrace tailWord_8338943 prefixEnd_8338943 1427295303148557526954135 := by
  unfold tailWord_8338943
  simp only [CollatzResearch.WordTrace]
  refine ⟨304146237828441163924901483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202764158552294109283267655 304146237828441163924901483)
  ·
    refine ⟨456219356742661745887352225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304146237828441163924901483 456219356742661745887352225)
    ·
      refine ⟨342164517556996309415514169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456219356742661745887352225 342164517556996309415514169)
      ·
        refine ⟨256623388167747232061635627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342164517556996309415514169 256623388167747232061635627)
        ·
          refine ⟨384935082251620848092453441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256623388167747232061635627 384935082251620848092453441)
          ·
            refine ⟨288701311688715636069340081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384935082251620848092453441 288701311688715636069340081)
            ·
              refine ⟨216525983766536727052005061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288701311688715636069340081 216525983766536727052005061)
              ·
                refine ⟨40598621956225636322250949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216525983766536727052005061 40598621956225636322250949)
                ·
                  refine ⟨7612241616792306810422053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40598621956225636322250949 7612241616792306810422053)
                  ·
                    refine ⟨1427295303148557526954135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7612241616792306810422053 1427295303148557526954135)
                    ·
                      rfl

theorem cell23_8338943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_8338943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338943 prefixEnd_8338943 := by exact prefixLift 8338943
  have htrace : WordTrace (prefixWord ++ tailWord_8338943) baseStart_8338943 baseEnd_8338943 := by
    simpa [prefixWord, tailWord_8338943, baseEnd_8338943] using wordTrace_append hprefix tailTrace_8338943
  have hstable : (prefixWord ++ tailWord_8338943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338943).length < 2 ^ (prefixWord ++ tailWord_8338943).sum := by decide
  have hdescent : baseEnd_8338943 < baseStart_8338943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8338956 : List Nat := [2, 2, 1, 2, 16]
def baseStart_8338956 : Nat := 118140960795 + 8338956 * 2 ^ 59
def prefixEnd_8338956 : Nat := 4983230072969 + 3 ^ 40 * 8338956 * 2
def baseEnd_8338956 : Nat := 5873652379553060397805

theorem tailTrace_8338956 : CollatzResearch.WordTrace tailWord_8338956 prefixEnd_8338956 5873652379553060397805 := by
  unfold tailWord_8338956
  simp only [CollatzResearch.WordTrace]
  refine ⟨152073355988697033572562361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202764474651596044763416481 152073355988697033572562361)
  ·
    refine ⟨114055016991522775179421771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152073355988697033572562361 114055016991522775179421771)
    ·
      refine ⟨171082525487284162769132657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114055016991522775179421771 171082525487284162769132657)
      ·
        refine ⟨128311894115463122076849493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171082525487284162769132657 128311894115463122076849493)
        ·
          refine ⟨5873652379553060397805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 128311894115463122076849493 5873652379553060397805)
          ·
            rfl

theorem cell23_8338956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 16].length) (baseStart_8338956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8338956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8338956 prefixEnd_8338956 := by exact prefixLift 8338956
  have htrace : WordTrace (prefixWord ++ tailWord_8338956) baseStart_8338956 baseEnd_8338956 := by
    simpa [prefixWord, tailWord_8338956, baseEnd_8338956] using wordTrace_append hprefix tailTrace_8338956
  have hstable : (prefixWord ++ tailWord_8338956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8338956).length < 2 ^ (prefixWord ++ tailWord_8338956).sum := by decide
  have hdescent : baseEnd_8338956 < baseStart_8338956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8338956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339000 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_8339000 : Nat := 118140960795 + 8339000 * 2 ^ 59
def prefixEnd_8339000 : Nat := 4983230072969 + 3 ^ 40 * 8339000 * 2
def baseEnd_8339000 : Nat := 4281915177842978857849643

theorem tailTrace_8339000 : CollatzResearch.WordTrace tailWord_8339000 prefixEnd_8339000 4281915177842978857849643 := by
  unfold tailWord_8339000
  simp only [CollatzResearch.WordTrace]
  refine ⟨152074158394617331329863227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202765544526156441773150969 152074158394617331329863227)
  ·
    refine ⟨228111237591925996994794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152074158394617331329863227 228111237591925996994794841)
    ·
      refine ⟨171083428193944497746096131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228111237591925996994794841 171083428193944497746096131)
      ·
        refine ⟨256625142290916746619144197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171083428193944497746096131 256625142290916746619144197)
        ·
          refine ⟨48117214179546889991089537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256625142290916746619144197 48117214179546889991089537)
          ·
            refine ⟨36087910634660167493317153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48117214179546889991089537 36087910634660167493317153)
            ·
              refine ⟨27065932975995125619987865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36087910634660167493317153 27065932975995125619987865)
              ·
                refine ⟨20299449731996344214990899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27065932975995125619987865 20299449731996344214990899)
                ·
                  refine ⟨30449174597994516322486349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20299449731996344214990899 30449174597994516322486349)
                  ·
                    refine ⟨11418440474247943620932381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30449174597994516322486349 11418440474247943620932381)
                    ·
                      refine ⟨4281915177842978857849643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11418440474247943620932381 4281915177842978857849643)
                      ·
                        rfl

theorem cell23_8339000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_8339000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339000 prefixEnd_8339000 := by exact prefixLift 8339000
  have htrace : WordTrace (prefixWord ++ tailWord_8339000) baseStart_8339000 baseEnd_8339000 := by
    simpa [prefixWord, tailWord_8339000, baseEnd_8339000] using wordTrace_append hprefix tailTrace_8339000
  have hstable : (prefixWord ++ tailWord_8339000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339000).length < 2 ^ (prefixWord ++ tailWord_8339000).sum := by decide
  have hdescent : baseEnd_8339000 < baseStart_8339000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339001 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 1, 2, 2]
def baseStart_8339001 : Nat := 118140960795 + 8339001 * 2 ^ 59
def prefixEnd_8339001 : Nat := 4983230072969 + 3 ^ 40 * 8339001 * 2
def baseEnd_8339001 : Nat := 4281915691323633353937139

theorem tailTrace_8339001 : CollatzResearch.WordTrace tailWord_8339001 prefixEnd_8339001 4281915691323633353937139 := by
  unfold tailWord_8339001
  simp only [CollatzResearch.WordTrace]
  refine ⟨304148353262231039830512857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202765568841487359887008571 304148353262231039830512857)
  ·
    refine ⟨228111264946673279872884643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304148353262231039830512857 228111264946673279872884643)
    ·
      refine ⟨342166897420009919809326965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228111264946673279872884643 342166897420009919809326965)
      ·
        refine ⟨32078146633125929982124403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342166897420009919809326965 32078146633125929982124403)
        ·
          refine ⟨48117219949688894973186605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32078146633125929982124403 48117219949688894973186605)
          ·
            refine ⟨18043957481133335614944977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48117219949688894973186605 18043957481133335614944977)
            ·
              refine ⟨13532968110850001711208733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18043957481133335614944977 13532968110850001711208733)
              ·
                refine ⟨5074863041568750641703275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13532968110850001711208733 5074863041568750641703275)
                ·
                  refine ⟨7612294562353125962554913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074863041568750641703275 7612294562353125962554913)
                  ·
                    refine ⟨5709220921764844471916185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7612294562353125962554913 5709220921764844471916185)
                    ·
                      refine ⟨4281915691323633353937139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709220921764844471916185 4281915691323633353937139)
                      ·
                        rfl

theorem cell23_8339001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_8339001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339001 prefixEnd_8339001 := by exact prefixLift 8339001
  have htrace : WordTrace (prefixWord ++ tailWord_8339001) baseStart_8339001 baseEnd_8339001 := by
    simpa [prefixWord, tailWord_8339001, baseEnd_8339001] using wordTrace_append hprefix tailTrace_8339001
  have hstable : (prefixWord ++ tailWord_8339001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339001).length < 2 ^ (prefixWord ++ tailWord_8339001).sum := by decide
  have hdescent : baseEnd_8339001 < baseStart_8339001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339044 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_8339044 : Nat := 118140960795 + 8339044 * 2 ^ 59
def prefixEnd_8339044 : Nat := 4983230072969 + 3 ^ 40 * 8339044 * 2
def baseEnd_8339044 : Nat := 4281937770991776685699441

theorem tailTrace_8339044 : CollatzResearch.WordTrace tailWord_8339044 prefixEnd_8339044 4281937770991776685699441 := by
  unfold tailWord_8339044
  simp only [CollatzResearch.WordTrace]
  refine ⟨152074960800537629087164093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202766614400716838782885457 152074960800537629087164093)
  ·
    refine ⟨57028110300201610907686535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152074960800537629087164093 57028110300201610907686535)
    ·
      refine ⟨85542165450302416361529803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57028110300201610907686535 85542165450302416361529803)
      ·
        refine ⟨128313248175453624542294705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85542165450302416361529803 128313248175453624542294705)
        ·
          refine ⟨96234936131590218406721029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128313248175453624542294705 96234936131590218406721029)
          ·
            refine ⟨18044050524673165951260193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96234936131590218406721029 18044050524673165951260193)
            ·
              refine ⟨13533037893504874463445145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18044050524673165951260193 13533037893504874463445145)
              ·
                refine ⟨10149778420128655847583859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13533037893504874463445145 10149778420128655847583859)
                ·
                  refine ⟨15224667630192983771375789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10149778420128655847583859 15224667630192983771375789)
                  ·
                    refine ⟨5709250361322368914265921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15224667630192983771375789 5709250361322368914265921)
                    ·
                      refine ⟨4281937770991776685699441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709250361322368914265921 4281937770991776685699441)
                      ·
                        rfl

theorem cell23_8339044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_8339044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339044 prefixEnd_8339044 := by exact prefixLift 8339044
  have htrace : WordTrace (prefixWord ++ tailWord_8339044) baseStart_8339044 baseEnd_8339044 := by
    simpa [prefixWord, tailWord_8339044, baseEnd_8339044] using wordTrace_append hprefix tailTrace_8339044
  have hstable : (prefixWord ++ tailWord_8339044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339044).length < 2 ^ (prefixWord ++ tailWord_8339044).sum := by decide
  have hdescent : baseEnd_8339044 < baseStart_8339044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339093 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_8339093 : Nat := 118140960795 + 8339093 * 2 ^ 59
def prefixEnd_8339093 : Nat := 4983230072969 + 3 ^ 40 * 8339093 * 2
def baseEnd_8339093 : Nat := 1427320977181282331328905

theorem tailTrace_8339093 : CollatzResearch.WordTrace tailWord_8339093 prefixEnd_8339093 1427320977181282331328905 := by
  unfold tailWord_8339093
  simp only [CollatzResearch.WordTrace]
  refine ⟨304151708777897739542861933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202767805851931826361907955 304151708777897739542861933)
  ·
    refine ⟨114056890791711652328573225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304151708777897739542861933 114056890791711652328573225)
    ·
      refine ⟨85542668093783739246429919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114056890791711652328573225 85542668093783739246429919)
      ·
        refine ⟨128314002140675608869644879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85542668093783739246429919 128314002140675608869644879)
        ·
          refine ⟨192471003211013413304467319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128314002140675608869644879 192471003211013413304467319)
          ·
            refine ⟨288706504816520119956700979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192471003211013413304467319 288706504816520119956700979)
            ·
              refine ⟨433059757224780179935051469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288706504816520119956700979 433059757224780179935051469)
              ·
                refine ⟨162397408959292567475644301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433059757224780179935051469 162397408959292567475644301)
                ·
                  refine ⟨60899028359734712803366613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162397408959292567475644301 60899028359734712803366613)
                  ·
                    refine ⟨1427320977181282331328905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60899028359734712803366613 1427320977181282331328905)
                    ·
                      rfl

theorem cell23_8339093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_8339093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339093 prefixEnd_8339093 := by exact prefixLift 8339093
  have htrace : WordTrace (prefixWord ++ tailWord_8339093) baseStart_8339093 baseEnd_8339093 := by
    simpa [prefixWord, tailWord_8339093, baseEnd_8339093] using wordTrace_append hprefix tailTrace_8339093
  have hstable : (prefixWord ++ tailWord_8339093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339093).length < 2 ^ (prefixWord ++ tailWord_8339093).sum := by decide
  have hdescent : baseEnd_8339093 < baseStart_8339093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339163 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_8339163 : Nat := 118140960795 + 8339163 * 2 ^ 59
def prefixEnd_8339163 : Nat := 4983230072969 + 3 ^ 40 * 8339163 * 2
def baseEnd_8339163 : Nat := 4281998875189661720111393

theorem tailTrace_8339163 : CollatzResearch.WordTrace tailWord_8339163 prefixEnd_8339163 4281998875189661720111393 := by
  unfold tailWord_8339163
  simp only [CollatzResearch.WordTrace]
  refine ⟨304154261887644141497910143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202769507925096094331940095 304154261887644141497910143)
  ·
    refine ⟨456231392831466212246865215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304154261887644141497910143 456231392831466212246865215)
    ·
      refine ⟨684347089247199318370297823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456231392831466212246865215 684347089247199318370297823)
      ·
        refine ⟨1026520633870798977555446735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684347089247199318370297823 1026520633870798977555446735)
        ·
          refine ⟨1539780950806198466333170103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026520633870798977555446735 1539780950806198466333170103)
          ·
            refine ⟨2309671426209297699499755155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539780950806198466333170103 2309671426209297699499755155)
            ·
              refine ⟨3464507139313946549249632733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309671426209297699499755155 3464507139313946549249632733)
              ·
                refine ⟨1299190177242729955968612275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464507139313946549249632733 1299190177242729955968612275)
                ·
                  refine ⟨1948785265864094933952918413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299190177242729955968612275 1948785265864094933952918413)
                  ·
                    refine ⟨730794474699035600232344405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948785265864094933952918413 730794474699035600232344405)
                    ·
                      refine ⟨4281998875189661720111393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 730794474699035600232344405 4281998875189661720111393)
                      ·
                        rfl

theorem cell23_8339163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_8339163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339163 prefixEnd_8339163 := by exact prefixLift 8339163
  have htrace : WordTrace (prefixWord ++ tailWord_8339163) baseStart_8339163 baseEnd_8339163 := by
    simpa [prefixWord, tailWord_8339163, baseEnd_8339163] using wordTrace_append hprefix tailTrace_8339163
  have hstable : (prefixWord ++ tailWord_8339163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339163).length < 2 ^ (prefixWord ++ tailWord_8339163).sum := by decide
  have hdescent : baseEnd_8339163 < baseStart_8339163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339164 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_8339164 : Nat := 118140960795 + 8339164 * 2 ^ 59
def prefixEnd_8339164 : Nat := 4983230072969 + 3 ^ 40 * 8339164 * 2
def baseEnd_8339164 : Nat := 4281999388670316216198889

theorem tailTrace_8339164 : CollatzResearch.WordTrace tailWord_8339164 prefixEnd_8339164 4281999388670316216198889 := by
  unfold tailWord_8339164
  simp only [CollatzResearch.WordTrace]
  refine ⟨152077149180320259334348273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202769532240427012445797697 152077149180320259334348273)
  ·
    refine ⟨114057861885240194500761205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152077149180320259334348273 114057861885240194500761205)
    ·
      refine ⟨10692924551741268234446363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114057861885240194500761205 10692924551741268234446363)
      ·
        refine ⟨16039386827611902351669545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692924551741268234446363 16039386827611902351669545)
        ·
          refine ⟨12029540120708926763752159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16039386827611902351669545 12029540120708926763752159)
          ·
            refine ⟨18044310181063390145628239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029540120708926763752159 18044310181063390145628239)
            ·
              refine ⟨27066465271595085218442359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18044310181063390145628239 27066465271595085218442359)
              ·
                refine ⟨40599697907392627827663539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27066465271595085218442359 40599697907392627827663539)
                ·
                  refine ⟨60899546861088941741495309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40599697907392627827663539 60899546861088941741495309)
                  ·
                    refine ⟨22837330072908353153060741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60899546861088941741495309 22837330072908353153060741)
                    ·
                      refine ⟨4281999388670316216198889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22837330072908353153060741 4281999388670316216198889)
                      ·
                        rfl

theorem cell23_8339164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_8339164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339164 prefixEnd_8339164 := by exact prefixLift 8339164
  have htrace : WordTrace (prefixWord ++ tailWord_8339164) baseStart_8339164 baseEnd_8339164 := by
    simpa [prefixWord, tailWord_8339164, baseEnd_8339164] using wordTrace_append hprefix tailTrace_8339164
  have hstable : (prefixWord ++ tailWord_8339164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339164).length < 2 ^ (prefixWord ++ tailWord_8339164).sum := by decide
  have hdescent : baseEnd_8339164 < baseStart_8339164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339204 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 6]
def baseStart_8339204 : Nat := 118140960795 + 8339204 * 2 ^ 59
def prefixEnd_8339204 : Nat := 4983230072969 + 3 ^ 40 * 8339204 * 2
def baseEnd_8339204 : Nat := 475779991988499562188745

theorem tailTrace_8339204 : CollatzResearch.WordTrace tailWord_8339204 prefixEnd_8339204 475779991988499562188745 := by
  unfold tailWord_8339204
  simp only [CollatzResearch.WordTrace]
  refine ⟨152077878640247802750076333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202770504853663737000101777 152077878640247802750076333)
  ·
    refine ⟨57029204490092926031278625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152077878640247802750076333 57029204490092926031278625)
    ·
      refine ⟨42771903367569694523458969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57029204490092926031278625 42771903367569694523458969)
      ·
        refine ⟨32078927525677270892594227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42771903367569694523458969 32078927525677270892594227)
        ·
          refine ⟨48118391288515906338891341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32078927525677270892594227 48118391288515906338891341)
          ·
            refine ⟨18044396733193464877084253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48118391288515906338891341 18044396733193464877084253)
            ·
              refine ⟨6766648774947549328906595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18044396733193464877084253 6766648774947549328906595)
              ·
                refine ⟨10149973162421323993359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766648774947549328906595 10149973162421323993359893)
                ·
                  refine ⟨475779991988499562188745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10149973162421323993359893 475779991988499562188745)
                  ·
                    rfl

theorem cell23_8339204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_8339204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339204 prefixEnd_8339204 := by exact prefixLift 8339204
  have htrace : WordTrace (prefixWord ++ tailWord_8339204) baseStart_8339204 baseEnd_8339204 := by
    simpa [prefixWord, tailWord_8339204, baseEnd_8339204] using wordTrace_append hprefix tailTrace_8339204
  have hstable : (prefixWord ++ tailWord_8339204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339204).length < 2 ^ (prefixWord ++ tailWord_8339204).sum := by decide
  have hdescent : baseEnd_8339204 < baseStart_8339204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339214 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_8339214 : Nat := 118140960795 + 8339214 * 2 ^ 59
def prefixEnd_8339214 : Nat := 4983230072969 + 3 ^ 40 * 8339214 * 2
def baseEnd_8339214 : Nat := 4282025062703041020573659

theorem tailTrace_8339214 : CollatzResearch.WordTrace tailWord_8339214 prefixEnd_8339214 4282025062703041020573659 := by
  unfold tailWord_8339214
  simp only [CollatzResearch.WordTrace]
  refine ⟨38019515251307422151002087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202770748006972918138677797 38019515251307422151002087)
  ·
    refine ⟨57029272876961133226503131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38019515251307422151002087 57029272876961133226503131)
    ·
      refine ⟨85543909315441699839754697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57029272876961133226503131 85543909315441699839754697)
      ·
        refine ⟨64157931986581274879816023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85543909315441699839754697 64157931986581274879816023)
        ·
          refine ⟨96236897979871912319724035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64157931986581274879816023 96236897979871912319724035)
          ·
            refine ⟨144355346969807868479586053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96236897979871912319724035 144355346969807868479586053)
            ·
              refine ⟨27066627556838975339922385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144355346969807868479586053 27066627556838975339922385)
              ·
                refine ⟨20299970667629231504941789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27066627556838975339922385 20299970667629231504941789)
                ·
                  refine ⟨7612489000360961814353171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20299970667629231504941789 7612489000360961814353171)
                  ·
                    refine ⟨11418733500541442721529757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7612489000360961814353171 11418733500541442721529757)
                    ·
                      refine ⟨4282025062703041020573659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11418733500541442721529757 4282025062703041020573659)
                      ·
                        rfl

theorem cell23_8339214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_8339214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339214 prefixEnd_8339214 := by exact prefixLift 8339214
  have htrace : WordTrace (prefixWord ++ tailWord_8339214) baseStart_8339214 baseEnd_8339214 := by
    simpa [prefixWord, tailWord_8339214, baseEnd_8339214] using wordTrace_append hprefix tailTrace_8339214
  have hstable : (prefixWord ++ tailWord_8339214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339214).length < 2 ^ (prefixWord ++ tailWord_8339214).sum := by decide
  have hdescent : baseEnd_8339214 < baseStart_8339214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339260 : List Nat := [2, 2, 2, 2, 1, 1, 3, 10]
def baseStart_8339260 : Nat := 118140960795 + 8339260 * 2 ^ 59
def prefixEnd_8339260 : Nat := 4983230072969 + 3 ^ 40 * 8339260 * 2
def baseEnd_8339260 : Nat := 158594395659746216318461

theorem tailTrace_8339260 : CollatzResearch.WordTrace tailWord_8339260 prefixEnd_8339260 158594395659746216318461 := by
  unfold tailWord_8339260
  simp only [CollatzResearch.WordTrace]
  refine ⟨152078899884146363532095617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202771866512195151376127489 152078899884146363532095617)
  ·
    refine ⟨114059174913109772649071713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152078899884146363532095617 114059174913109772649071713)
    ·
      refine ⟨85544381184832329486803785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114059174913109772649071713 85544381184832329486803785)
      ·
        refine ⟨64158285888624247115102839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85544381184832329486803785 64158285888624247115102839)
        ·
          refine ⟨96237428832936370672654259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64158285888624247115102839 96237428832936370672654259)
          ·
            refine ⟨144356143249404556008981389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96237428832936370672654259 144356143249404556008981389)
            ·
              refine ⟨54133553718526708503368021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144356143249404556008981389 54133553718526708503368021)
              ·
                refine ⟨158594395659746216318461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54133553718526708503368021 158594395659746216318461)
                ·
                  rfl

theorem cell23_8339260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 10].length) (baseStart_8339260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339260 prefixEnd_8339260 := by exact prefixLift 8339260
  have htrace : WordTrace (prefixWord ++ tailWord_8339260) baseStart_8339260 baseEnd_8339260 := by
    simpa [prefixWord, tailWord_8339260, baseEnd_8339260] using wordTrace_append hprefix tailTrace_8339260
  have hstable : (prefixWord ++ tailWord_8339260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339260).length < 2 ^ (prefixWord ++ tailWord_8339260).sum := by decide
  have hdescent : baseEnd_8339260 < baseStart_8339260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339284 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_8339284 : Nat := 118140960795 + 8339284 * 2 ^ 59
def prefixEnd_8339284 : Nat := 4983230072969 + 3 ^ 40 * 8339284 * 2
def baseEnd_8339284 : Nat := 4282061006348855746698337

theorem tailTrace_8339284 : CollatzResearch.WordTrace tailWord_8339284 prefixEnd_8339284 4282061006348855746698337 := by
  unfold tailWord_8339284
  simp only [CollatzResearch.WordTrace]
  refine ⟨152079337560102889581532453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202772450080137186108709937 152079337560102889581532453)
  ·
    refine ⟨28514875792519291796537335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152079337560102889581532453 28514875792519291796537335)
    ·
      refine ⟨42772313688778937694806003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28514875792519291796537335 42772313688778937694806003)
      ·
        refine ⟨64158470533168406542209005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42772313688778937694806003 64158470533168406542209005)
        ·
          refine ⟨24059426449938152453328377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64158470533168406542209005 24059426449938152453328377)
          ·
            refine ⟨18044569837453614339996283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24059426449938152453328377 18044569837453614339996283)
            ·
              refine ⟨27066854756180421509994425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18044569837453614339996283 27066854756180421509994425)
              ·
                refine ⟨20300141067135316132495819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27066854756180421509994425 20300141067135316132495819)
                ·
                  refine ⟨30450211600702974198743729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20300141067135316132495819 30450211600702974198743729)
                  ·
                    refine ⟨22837658700527230649057797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30450211600702974198743729 22837658700527230649057797)
                    ·
                      refine ⟨4282061006348855746698337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22837658700527230649057797 4282061006348855746698337)
                      ·
                        rfl

theorem cell23_8339284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_8339284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339284 prefixEnd_8339284 := by exact prefixLift 8339284
  have htrace : WordTrace (prefixWord ++ tailWord_8339284) baseStart_8339284 baseEnd_8339284 := by
    simpa [prefixWord, tailWord_8339284, baseEnd_8339284] using wordTrace_append hprefix tailTrace_8339284
  have hstable : (prefixWord ++ tailWord_8339284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339284).length < 2 ^ (prefixWord ++ tailWord_8339284).sum := by decide
  have hdescent : baseEnd_8339284 < baseStart_8339284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339342 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8339342 : Nat := 118140960795 + 8339342 * 2 ^ 59
def prefixEnd_8339342 : Nat := 4983230072969 + 3 ^ 40 * 8339342 * 2
def baseEnd_8339342 : Nat := 4282090788226816519773071

theorem tailTrace_8339342 : CollatzResearch.WordTrace tailWord_8339342 prefixEnd_8339342 4282090788226816519773071 := by
  unfold tailWord_8339342
  simp only [CollatzResearch.WordTrace]
  refine ⟨38020098819249456883584535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202773860369330436712450853 38020098819249456883584535)
  ·
    refine ⟨57030148228874185325376803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38020098819249456883584535 57030148228874185325376803)
    ·
      refine ⟨85545222343311277988065205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57030148228874185325376803 85545222343311277988065205)
      ·
        refine ⟨8019864594685432311381113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85545222343311277988065205 8019864594685432311381113)
        ·
          refine ⟨6014898446014074233535835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019864594685432311381113 6014898446014074233535835)
          ·
            refine ⟨9022347669021111350303753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014898446014074233535835 9022347669021111350303753)
            ·
              refine ⟨6766760751765833512727815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022347669021111350303753 6766760751765833512727815)
              ·
                refine ⟨10150141127648750269091723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766760751765833512727815 10150141127648750269091723)
                ·
                  refine ⟨15225211691473125403637585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150141127648750269091723 15225211691473125403637585)
                  ·
                    refine ⟨11418908768604844052728189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15225211691473125403637585 11418908768604844052728189)
                    ·
                      refine ⟨4282090788226816519773071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11418908768604844052728189 4282090788226816519773071)
                      ·
                        rfl

theorem cell23_8339342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8339342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339342 prefixEnd_8339342 := by exact prefixLift 8339342
  have htrace : WordTrace (prefixWord ++ tailWord_8339342) baseStart_8339342 baseEnd_8339342 := by
    simpa [prefixWord, tailWord_8339342, baseEnd_8339342] using wordTrace_append hprefix tailTrace_8339342
  have hstable : (prefixWord ++ tailWord_8339342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339342).length < 2 ^ (prefixWord ++ tailWord_8339342).sum := by decide
  have hdescent : baseEnd_8339342 < baseStart_8339342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339348 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_8339348 : Nat := 118140960795 + 8339348 * 2 ^ 59
def prefixEnd_8339348 : Nat := 4983230072969 + 3 ^ 40 * 8339348 * 2
def baseEnd_8339348 : Nat := 4282093869110743496298043

theorem tailTrace_8339348 : CollatzResearch.WordTrace tailWord_8339348 prefixEnd_8339348 4282093869110743496298043 := by
  unfold tailWord_8339348
  simp only [CollatzResearch.WordTrace]
  refine ⟨152080504695986959046697349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202774006261315945395596465 152080504695986959046697349)
  ·
    refine ⟨28515094630497554821255753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152080504695986959046697349 28515094630497554821255753)
    ·
      refine ⟨21386320972873166115941815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28515094630497554821255753 21386320972873166115941815)
      ·
        refine ⟨32079481459309749173912723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21386320972873166115941815 32079481459309749173912723)
        ·
          refine ⟨48119222188964623760869085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32079481459309749173912723 48119222188964623760869085)
          ·
            refine ⟨18044708320861733910325907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48119222188964623760869085 18044708320861733910325907)
            ·
              refine ⟨27067062481292600865488861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18044708320861733910325907 27067062481292600865488861)
              ·
                refine ⟨10150148430484725324558323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27067062481292600865488861 10150148430484725324558323)
                ·
                  refine ⟨15225222645727087986837485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150148430484725324558323 15225222645727087986837485)
                  ·
                    refine ⟨5709458492147657995064057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15225222645727087986837485 5709458492147657995064057)
                    ·
                      refine ⟨4282093869110743496298043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709458492147657995064057 4282093869110743496298043)
                      ·
                        rfl

theorem cell23_8339348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_8339348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339348 prefixEnd_8339348 := by exact prefixLift 8339348
  have htrace : WordTrace (prefixWord ++ tailWord_8339348) baseStart_8339348 baseEnd_8339348 := by
    simpa [prefixWord, tailWord_8339348, baseEnd_8339348] using wordTrace_append hprefix tailTrace_8339348
  have hstable : (prefixWord ++ tailWord_8339348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339348).length < 2 ^ (prefixWord ++ tailWord_8339348).sum := by decide
  have hdescent : baseEnd_8339348 < baseStart_8339348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339407 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_8339407 : Nat := 118140960795 + 8339407 * 2 ^ 59
def prefixEnd_8339407 : Nat := 4983230072969 + 3 ^ 40 * 8339407 * 2
def baseEnd_8339407 : Nat := 4282124164469358765460271

theorem tailTrace_8339407 : CollatzResearch.WordTrace tailWord_8339407 prefixEnd_8339407 4282124164469358765460271 := by
  unfold tailWord_8339407
  simp only [CollatzResearch.WordTrace]
  refine ⟨304163161298760171169792475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202775440865840114113194983 304163161298760171169792475)
  ·
    refine ⟨456244741948140256754688713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304163161298760171169792475 456244741948140256754688713)
    ·
      refine ⟨342183556461105192566016535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456244741948140256754688713 342183556461105192566016535)
      ·
        refine ⟨513275334691657788849024803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342183556461105192566016535 513275334691657788849024803)
        ·
          refine ⟨769913002037486683273537205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513275334691657788849024803 769913002037486683273537205)
          ·
            refine ⟨72179343941014376556894113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 769913002037486683273537205 72179343941014376556894113)
            ·
              refine ⟨54134507955760782417670585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72179343941014376556894113 54134507955760782417670585)
              ·
                refine ⟨40600880966820586813252939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54134507955760782417670585 40600880966820586813252939)
                ·
                  refine ⟨60901321450230880219879409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40600880966820586813252939 60901321450230880219879409)
                  ·
                    refine ⟨45675991087673160164909557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60901321450230880219879409 45675991087673160164909557)
                    ·
                      refine ⟨4282124164469358765460271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45675991087673160164909557 4282124164469358765460271)
                      ·
                        rfl

theorem cell23_8339407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_8339407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339407 prefixEnd_8339407 := by exact prefixLift 8339407
  have htrace : WordTrace (prefixWord ++ tailWord_8339407) baseStart_8339407 baseEnd_8339407 := by
    simpa [prefixWord, tailWord_8339407, baseEnd_8339407] using wordTrace_append hprefix tailTrace_8339407
  have hstable : (prefixWord ++ tailWord_8339407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339407).length < 2 ^ (prefixWord ++ tailWord_8339407).sum := by decide
  have hdescent : baseEnd_8339407 < baseStart_8339407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339418 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_8339418 : Nat := 118140960795 + 8339418 * 2 ^ 59
def prefixEnd_8339418 : Nat := 4983230072969 + 3 ^ 40 * 8339418 * 2
def baseEnd_8339418 : Nat := 475792201417395358046969

theorem tailTrace_8339418 : CollatzResearch.WordTrace tailWord_8339418 prefixEnd_8339418 475792201417395358046969 := by
  unfold tailWord_8339418
  simp only [CollatzResearch.WordTrace]
  refine ⟨76040890625430080012110727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202775708334480213365628605 76040890625430080012110727)
  ·
    refine ⟨114061335938145120018166091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76040890625430080012110727 114061335938145120018166091)
    ·
      refine ⟨171092003907217680027249137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114061335938145120018166091 171092003907217680027249137)
      ·
        refine ⟨128319002930413260020436853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171092003907217680027249137 128319002930413260020436853)
        ·
          refine ⟨12029906524726243126915955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128319002930413260020436853 12029906524726243126915955)
          ·
            refine ⟨18044859787089364690373933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029906524726243126915955 18044859787089364690373933)
            ·
              refine ⟨6766822420158511758890225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18044859787089364690373933 6766822420158511758890225)
              ·
                refine ⟨5075116815118883819167669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766822420158511758890225 5075116815118883819167669)
                ·
                  refine ⟨475792201417395358046969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075116815118883819167669 475792201417395358046969)
                  ·
                    rfl

theorem cell23_8339418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_8339418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339418 prefixEnd_8339418 := by exact prefixLift 8339418
  have htrace : WordTrace (prefixWord ++ tailWord_8339418) baseStart_8339418 baseEnd_8339418 := by
    simpa [prefixWord, tailWord_8339418, baseEnd_8339418] using wordTrace_append hprefix tailTrace_8339418
  have hstable : (prefixWord ++ tailWord_8339418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339418).length < 2 ^ (prefixWord ++ tailWord_8339418).sum := by decide
  have hdescent : baseEnd_8339418 < baseStart_8339418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339434 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_8339434 : Nat := 118140960795 + 8339434 * 2 ^ 59
def prefixEnd_8339434 : Nat := 4983230072969 + 3 ^ 40 * 8339434 * 2
def baseEnd_8339434 : Nat := 4282138028447030159822647

theorem tailTrace_8339434 : CollatzResearch.WordTrace tailWord_8339434 prefixEnd_8339434 4282138028447030159822647 := by
  unfold tailWord_8339434
  simp only [CollatzResearch.WordTrace]
  refine ⟨76041036517415588695256339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202776097379774903187350237 76041036517415588695256339)
  ·
    refine ⟨114061554776123383042884509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76041036517415588695256339 114061554776123383042884509)
    ·
      refine ⟨42773083041046268641081691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114061554776123383042884509 42773083041046268641081691)
      ·
        refine ⟨64159624561569402961622537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42773083041046268641081691 64159624561569402961622537)
        ·
          refine ⟨48119718421177052221216903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64159624561569402961622537 48119718421177052221216903)
          ·
            refine ⟨72179577631765578331825355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48119718421177052221216903 72179577631765578331825355)
            ·
              refine ⟨108269366447648367497738033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72179577631765578331825355 108269366447648367497738033)
              ·
                refine ⟨81202024835736275623303525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108269366447648367497738033 81202024835736275623303525)
                ·
                  refine ⟨15225379656700551679369411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81202024835736275623303525 15225379656700551679369411)
                  ·
                    refine ⟨22838069485050827519054117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15225379656700551679369411 22838069485050827519054117)
                    ·
                      refine ⟨4282138028447030159822647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22838069485050827519054117 4282138028447030159822647)
                      ·
                        rfl

theorem cell23_8339434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_8339434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339434 prefixEnd_8339434 := by exact prefixLift 8339434
  have htrace : WordTrace (prefixWord ++ tailWord_8339434) baseStart_8339434 baseEnd_8339434 := by
    simpa [prefixWord, tailWord_8339434, baseEnd_8339434] using wordTrace_append hprefix tailTrace_8339434
  have hstable : (prefixWord ++ tailWord_8339434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339434).length < 2 ^ (prefixWord ++ tailWord_8339434).sum := by decide
  have hdescent : baseEnd_8339434 < baseStart_8339434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339469 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 5]
def baseStart_8339469 : Nat := 118140960795 + 8339469 * 2 ^ 59
def prefixEnd_8339469 : Nat := 4983230072969 + 3 ^ 40 * 8339469 * 2
def baseEnd_8339469 : Nat := 475795111141104169209443

theorem tailTrace_8339469 : CollatzResearch.WordTrace tailWord_8339469 prefixEnd_8339469 475795111141104169209443 := by
  unfold tailWord_8339469
  simp only [CollatzResearch.WordTrace]
  refine ⟨304165422624535555758549461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202776948416357037172366307 304165422624535555758549461)
  ·
    refine ⟨7128877092762552088091003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 304165422624535555758549461 7128877092762552088091003)
    ·
      refine ⟨10693315639143828132136505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128877092762552088091003 10693315639143828132136505)
      ·
        refine ⟨8019986729357871099102379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10693315639143828132136505 8019986729357871099102379)
        ·
          refine ⟨12029980094036806648653569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019986729357871099102379 12029980094036806648653569)
          ·
            refine ⟨9022485070527604986490177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12029980094036806648653569 9022485070527604986490177)
            ·
              refine ⟨6766863802895703739867633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022485070527604986490177 6766863802895703739867633)
              ·
                refine ⟨5075147852171777804900725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766863802895703739867633 5075147852171777804900725)
                ·
                  refine ⟨475795111141104169209443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075147852171777804900725 475795111141104169209443)
                  ·
                    rfl

theorem cell23_8339469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_8339469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339469 prefixEnd_8339469 := by exact prefixLift 8339469
  have htrace : WordTrace (prefixWord ++ tailWord_8339469) baseStart_8339469 baseEnd_8339469 := by
    simpa [prefixWord, tailWord_8339469, baseEnd_8339469] using wordTrace_append hprefix tailTrace_8339469
  have hstable : (prefixWord ++ tailWord_8339469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339469).length < 2 ^ (prefixWord ++ tailWord_8339469).sum := by decide
  have hdescent : baseEnd_8339469 < baseStart_8339469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_8339497 : Nat := 118140960795 + 8339497 * 2 ^ 59
def prefixEnd_8339497 : Nat := 4983230072969 + 3 ^ 40 * 8339497 * 2
def baseEnd_8339497 : Nat := 4282170377728263413334857

theorem tailTrace_8339497 : CollatzResearch.WordTrace tailWord_8339497 prefixEnd_8339497 4282170377728263413334857 := by
  unfold tailWord_8339497
  simp only [CollatzResearch.WordTrace]
  refine ⟨304166443868434116540568745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202777629245622744360379163 304166443868434116540568745)
  ·
    refine ⟨228124832901325587405426559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304166443868434116540568745 228124832901325587405426559)
    ·
      refine ⟨342187249351988381108139839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228124832901325587405426559 342187249351988381108139839)
      ·
        refine ⟨513280874027982571662209759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342187249351988381108139839 513280874027982571662209759)
        ·
          refine ⟨769921311041973857493314639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513280874027982571662209759 769921311041973857493314639)
          ·
            refine ⟨1154881966562960786239971959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769921311041973857493314639 1154881966562960786239971959)
            ·
              refine ⟨1732322949844441179359957939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154881966562960786239971959 1732322949844441179359957939)
              ·
                refine ⟨2598484424766661769039936909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732322949844441179359957939 2598484424766661769039936909)
                ·
                  refine ⟨974431659287498163389976341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2598484424766661769039936909 974431659287498163389976341)
                  ·
                    refine ⟨45676484029101476408905141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 974431659287498163389976341 45676484029101476408905141)
                    ·
                      refine ⟨4282170377728263413334857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45676484029101476408905141 4282170377728263413334857)
                      ·
                        rfl

theorem cell23_8339497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_8339497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339497 prefixEnd_8339497 := by exact prefixLift 8339497
  have htrace : WordTrace (prefixWord ++ tailWord_8339497) baseStart_8339497 baseEnd_8339497 := by
    simpa [prefixWord, tailWord_8339497, baseEnd_8339497] using wordTrace_append hprefix tailTrace_8339497
  have hstable : (prefixWord ++ tailWord_8339497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339497).length < 2 ^ (prefixWord ++ tailWord_8339497).sum := by decide
  have hdescent : baseEnd_8339497 < baseStart_8339497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339504 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_8339504 : Nat := 118140960795 + 8339504 * 2 ^ 59
def prefixEnd_8339504 : Nat := 4983230072969 + 3 ^ 40 * 8339504 * 2
def baseEnd_8339504 : Nat := 1427391324030948295315775

theorem tailTrace_8339504 : CollatzResearch.WordTrace tailWord_8339504 prefixEnd_8339504 1427391324030948295315775 := by
  unfold tailWord_8339504
  simp only [CollatzResearch.WordTrace]
  refine ⟨152083349589704378368036783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202777799452939171157382377 152083349589704378368036783)
  ·
    refine ⟨228125024384556567552055175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152083349589704378368036783 228125024384556567552055175)
    ·
      refine ⟨342187536576834851328082763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228125024384556567552055175 342187536576834851328082763)
      ·
        refine ⟨513281304865252276992124145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342187536576834851328082763 513281304865252276992124145)
        ·
          refine ⟨384960978648939207744093109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513281304865252276992124145 384960978648939207744093109)
          ·
            refine ⟨36090091748338050726008729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384960978648939207744093109 36090091748338050726008729)
            ·
              refine ⟨27067568811253538044506547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36090091748338050726008729 27067568811253538044506547)
              ·
                refine ⟨40601353216880307066759821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27067568811253538044506547 40601353216880307066759821)
                ·
                  refine ⟨15225507456330115150034933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40601353216880307066759821 15225507456330115150034933)
                  ·
                    refine ⟨1427391324030948295315775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15225507456330115150034933 1427391324030948295315775)
                    ·
                      rfl

theorem cell23_8339504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_8339504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339504 prefixEnd_8339504 := by exact prefixLift 8339504
  have htrace : WordTrace (prefixWord ++ tailWord_8339504) baseStart_8339504 baseEnd_8339504 := by
    simpa [prefixWord, tailWord_8339504, baseEnd_8339504] using wordTrace_append hprefix tailTrace_8339504
  have hstable : (prefixWord ++ tailWord_8339504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339504).length < 2 ^ (prefixWord ++ tailWord_8339504).sum := by decide
  have hdescent : baseEnd_8339504 < baseStart_8339504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339544 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_8339544 : Nat := 118140960795 + 8339544 * 2 ^ 59
def prefixEnd_8339544 : Nat := 4983230072969 + 3 ^ 40 * 8339544 * 2
def baseEnd_8339544 : Nat := 4282194511319024729447141

theorem tailTrace_8339544 : CollatzResearch.WordTrace tailWord_8339544 prefixEnd_8339544 4282194511319024729447141 := by
  unfold tailWord_8339544
  simp only [CollatzResearch.WordTrace]
  refine ⟨152084079049631921783764843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202778772066175895711686457 152084079049631921783764843)
  ·
    refine ⟨228126118574447882675647265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152084079049631921783764843 228126118574447882675647265)
    ·
      refine ⟨171094588930835912006735449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228126118574447882675647265 171094588930835912006735449)
      ·
        refine ⟨128320941698126934005051587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171094588930835912006735449 128320941698126934005051587)
        ·
          refine ⟨192481412547190401007577381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128320941698126934005051587 192481412547190401007577381)
          ·
            refine ⟨36090264852598200188920759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192481412547190401007577381 36090264852598200188920759)
            ·
              refine ⟨54135397278897300283381139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36090264852598200188920759 54135397278897300283381139)
              ·
                refine ⟨81203095918345950425071709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54135397278897300283381139 81203095918345950425071709)
                ·
                  refine ⟨30451160969379731409401891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81203095918345950425071709 30451160969379731409401891)
                  ·
                    refine ⟨45676741454069597114102837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30451160969379731409401891 45676741454069597114102837)
                    ·
                      refine ⟨4282194511319024729447141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45676741454069597114102837 4282194511319024729447141)
                      ·
                        rfl

theorem cell23_8339544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_8339544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339544 prefixEnd_8339544 := by exact prefixLift 8339544
  have htrace : WordTrace (prefixWord ++ tailWord_8339544) baseStart_8339544 baseEnd_8339544 := by
    simpa [prefixWord, tailWord_8339544, baseEnd_8339544] using wordTrace_append hprefix tailTrace_8339544
  have hstable : (prefixWord ++ tailWord_8339544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339544).length < 2 ^ (prefixWord ++ tailWord_8339544).sum := by decide
  have hdescent : baseEnd_8339544 < baseStart_8339544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339564 : List Nat := [2, 2, 1, 1, 3, 4, 1, 9]
def baseStart_8339564 : Nat := 118140960795 + 8339564 * 2 ^ 59
def prefixEnd_8339564 : Nat := 4983230072969 + 3 ^ 40 * 8339564 * 2
def baseEnd_8339564 : Nat := 158600177071559801896187

theorem tailTrace_8339564 : CollatzResearch.WordTrace tailWord_8339564 prefixEnd_8339564 158600177071559801896187 := by
  unfold tailWord_8339564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152084443779595693491628873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202779258372794257988838497 152084443779595693491628873)
  ·
    refine ⟨114063332834696770118721655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152084443779595693491628873 114063332834696770118721655)
    ·
      refine ⟨171094999252045155178082483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114063332834696770118721655 171094999252045155178082483)
      ·
        refine ⟨256642498878067732767123725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171094999252045155178082483 256642498878067732767123725)
        ·
          refine ⟨96240937079275399787671397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256642498878067732767123725 96240937079275399787671397)
          ·
            refine ⟨18045175702364137460188387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96240937079275399787671397 18045175702364137460188387)
            ·
              refine ⟨27067763553546206190282581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045175702364137460188387 27067763553546206190282581)
              ·
                refine ⟨158600177071559801896187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27067763553546206190282581 158600177071559801896187)
                ·
                  rfl

theorem cell23_8339564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 9].length) (baseStart_8339564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339564 prefixEnd_8339564 := by exact prefixLift 8339564
  have htrace : WordTrace (prefixWord ++ tailWord_8339564) baseStart_8339564 baseEnd_8339564 := by
    simpa [prefixWord, tailWord_8339564, baseEnd_8339564] using wordTrace_append hprefix tailTrace_8339564
  have hstable : (prefixWord ++ tailWord_8339564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339564).length < 2 ^ (prefixWord ++ tailWord_8339564).sum := by decide
  have hdescent : baseEnd_8339564 < baseStart_8339564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339592 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_8339592 : Nat := 118140960795 + 8339592 * 2 ^ 59
def prefixEnd_8339592 : Nat := 4983230072969 + 3 ^ 40 * 8339592 * 2
def baseEnd_8339592 : Nat := 4282219158390440541646921

theorem tailTrace_8339592 : CollatzResearch.WordTrace tailWord_8339592 prefixEnd_8339592 4282219158390440541646921 := by
  unfold tailWord_8339592
  simp only [CollatzResearch.WordTrace]
  refine ⟨152084954401544973882638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202779939202059965176851353 152084954401544973882638515)
  ·
    refine ⟨228127431602317460823957773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152084954401544973882638515 228127431602317460823957773)
    ·
      refine ⟨85547786850869047808984165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228127431602317460823957773 85547786850869047808984165)
      ·
        refine ⟨16040210034537946464184531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85547786850869047808984165 16040210034537946464184531)
        ·
          refine ⟨24060315051806919696276797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16040210034537946464184531 24060315051806919696276797)
          ·
            refine ⟨9022618144427594886103799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24060315051806919696276797 9022618144427594886103799)
            ·
              refine ⟨13533927216641392329155699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9022618144427594886103799 13533927216641392329155699)
              ·
                refine ⟨20300890824962088493733549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13533927216641392329155699 20300890824962088493733549)
                ·
                  refine ⟨7612834059360783185150081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20300890824962088493733549 7612834059360783185150081)
                  ·
                    refine ⟨5709625544520587388862561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7612834059360783185150081 5709625544520587388862561)
                    ·
                      refine ⟨4282219158390440541646921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709625544520587388862561 4282219158390440541646921)
                      ·
                        rfl

theorem cell23_8339592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_8339592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339592 prefixEnd_8339592 := by exact prefixLift 8339592
  have htrace : WordTrace (prefixWord ++ tailWord_8339592) baseStart_8339592 baseEnd_8339592 := by
    simpa [prefixWord, tailWord_8339592, baseEnd_8339592] using wordTrace_append hprefix tailTrace_8339592
  have hstable : (prefixWord ++ tailWord_8339592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339592).length < 2 ^ (prefixWord ++ tailWord_8339592).sum := by decide
  have hdescent : baseEnd_8339592 < baseStart_8339592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339606 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8339606 : Nat := 118140960795 + 8339606 * 2 ^ 59
def prefixEnd_8339606 : Nat := 4983230072969 + 3 ^ 40 * 8339606 * 2
def baseEnd_8339606 : Nat := 1427408782373201162290619

theorem tailTrace_8339606 : CollatzResearch.WordTrace tailWord_8339606 prefixEnd_8339606 1427408782373201162290619 := by
  unfold tailWord_8339606
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010651214064951759767917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202780279616692818770857781 19010651214064951759767917)
  ·
    refine ⟨7128994205274356909912969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19010651214064951759767917 7128994205274356909912969)
    ·
      refine ⟨5346745653955767682434727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7128994205274356909912969 5346745653955767682434727)
      ·
        refine ⟨8020118480933651523652091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346745653955767682434727 8020118480933651523652091)
        ·
          refine ⟨12030177721400477285478137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020118480933651523652091 12030177721400477285478137)
          ·
            refine ⟨9022633291050357964108603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12030177721400477285478137 9022633291050357964108603)
            ·
              refine ⟨13533949936575536946162905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9022633291050357964108603 13533949936575536946162905)
              ·
                refine ⟨10150462452431652709622179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13533949936575536946162905 10150462452431652709622179)
                ·
                  refine ⟨15225693678647479064433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150462452431652709622179 15225693678647479064433269)
                  ·
                    refine ⟨1427408782373201162290619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15225693678647479064433269 1427408782373201162290619)
                    ·
                      rfl

theorem cell23_8339606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8339606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339606 prefixEnd_8339606 := by exact prefixLift 8339606
  have htrace : WordTrace (prefixWord ++ tailWord_8339606) baseStart_8339606 baseEnd_8339606 := by
    simpa [prefixWord, tailWord_8339606, baseEnd_8339606] using wordTrace_append hprefix tailTrace_8339606
  have hstable : (prefixWord ++ tailWord_8339606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339606).length < 2 ^ (prefixWord ++ tailWord_8339606).sum := by decide
  have hdescent : baseEnd_8339606 < baseStart_8339606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339665 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_8339665 : Nat := 118140960795 + 8339665 * 2 ^ 59
def prefixEnd_8339665 : Nat := 4983230072969 + 3 ^ 40 * 8339665 * 2
def baseEnd_8339665 : Nat := 4282256642478218756034085

theorem tailTrace_8339665 : CollatzResearch.WordTrace tailWord_8339665 prefixEnd_8339665 4282256642478218756034085 := by
  unfold tailWord_8339665
  simp only [CollatzResearch.WordTrace]
  refine ⟨304172571331825481232684449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202781714221216987488456299 304172571331825481232684449)
  ·
    refine ⟨228129428498869110924513337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304172571331825481232684449 228129428498869110924513337)
    ·
      refine ⟨171097071374151833193385003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228129428498869110924513337 171097071374151833193385003)
      ·
        refine ⟨256645607061227749790077505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171097071374151833193385003 256645607061227749790077505)
        ·
          refine ⟨192484205295920812342558129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256645607061227749790077505 192484205295920812342558129)
          ·
            refine ⟨144363153971940609256918597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192484205295920812342558129 144363153971940609256918597)
            ·
              refine ⟨27068091369738864235672237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144363153971940609256918597 27068091369738864235672237)
              ·
                refine ⟨10150534263652074088377089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27068091369738864235672237 10150534263652074088377089)
                ·
                  refine ⟨7612900697739055566282817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10150534263652074088377089 7612900697739055566282817)
                  ·
                    refine ⟨5709675523304291674712113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7612900697739055566282817 5709675523304291674712113)
                    ·
                      refine ⟨4282256642478218756034085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709675523304291674712113 4282256642478218756034085)
                      ·
                        rfl

theorem cell23_8339665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_8339665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339665 prefixEnd_8339665 := by exact prefixLift 8339665
  have htrace : WordTrace (prefixWord ++ tailWord_8339665) baseStart_8339665 baseEnd_8339665 := by
    simpa [prefixWord, tailWord_8339665, baseEnd_8339665] using wordTrace_append hprefix tailTrace_8339665
  have hstable : (prefixWord ++ tailWord_8339665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339665).length < 2 ^ (prefixWord ++ tailWord_8339665).sum := by decide
  have hdescent : baseEnd_8339665 < baseStart_8339665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339681 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_8339681 : Nat := 118140960795 + 8339681 * 2 ^ 59
def prefixEnd_8339681 : Nat := 4983230072969 + 3 ^ 40 * 8339681 * 2
def baseEnd_8339681 : Nat := 4282264858168690693434011

theorem tailTrace_8339681 : CollatzResearch.WordTrace tailWord_8339681 prefixEnd_8339681 4282264858168690693434011 := by
  unfold tailWord_8339681
  simp only [CollatzResearch.WordTrace]
  refine ⟨304173154899767515965266897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202782103266511677310177931 304173154899767515965266897)
  ·
    refine ⟨228129866174825636973950173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304173154899767515965266897 228129866174825636973950173)
    ·
      refine ⟨85548699815559613865231315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228129866174825636973950173 85548699815559613865231315)
      ·
        refine ⟨128323049723339420797846973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85548699815559613865231315 128323049723339420797846973)
        ·
          refine ⟨48121143646252282799192615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128323049723339420797846973 48121143646252282799192615)
          ·
            refine ⟨72181715469378424198788923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48121143646252282799192615 72181715469378424198788923)
            ·
              refine ⟨108272573204067636298183385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72181715469378424198788923 108272573204067636298183385)
              ·
                refine ⟨81204429903050727223637539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108272573204067636298183385 81204429903050727223637539)
                ·
                  refine ⟨121806644854576090835456309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81204429903050727223637539 121806644854576090835456309)
                  ·
                    refine ⟨11419372955116508515824029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121806644854576090835456309 11419372955116508515824029)
                    ·
                      refine ⟨4282264858168690693434011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419372955116508515824029 4282264858168690693434011)
                      ·
                        rfl

theorem cell23_8339681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_8339681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339681 prefixEnd_8339681 := by exact prefixLift 8339681
  have htrace : WordTrace (prefixWord ++ tailWord_8339681) baseStart_8339681 baseEnd_8339681 := by
    simpa [prefixWord, tailWord_8339681, baseEnd_8339681] using wordTrace_append hprefix tailTrace_8339681
  have hstable : (prefixWord ++ tailWord_8339681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339681).length < 2 ^ (prefixWord ++ tailWord_8339681).sum := by decide
  have hdescent : baseEnd_8339681 < baseStart_8339681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339688 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 5]
def baseStart_8339688 : Nat := 118140960795 + 8339688 * 2 ^ 59
def prefixEnd_8339688 : Nat := 4983230072969 + 3 ^ 40 * 8339688 * 2
def baseEnd_8339688 : Nat := 475807605837030240671831

theorem tailTrace_8339688 : CollatzResearch.WordTrace tailWord_8339688 prefixEnd_8339688 475807605837030240671831 := by
  unfold tailWord_8339688
  simp only [CollatzResearch.WordTrace]
  refine ⟨152086705105371078080385859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202782273473828104107181145 152086705105371078080385859)
  ·
    refine ⟨228130057658056617120578789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152086705105371078080385859 228130057658056617120578789)
    ·
      refine ⟨42774385810885615710108523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228130057658056617120578789 42774385810885615710108523)
      ·
        refine ⟨64161578716328423565162785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42774385810885615710108523 64161578716328423565162785)
        ·
          refine ⟨48121184037246317673872089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64161578716328423565162785 48121184037246317673872089)
          ·
            refine ⟨36090888027934738255404067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48121184037246317673872089 36090888027934738255404067)
            ·
              refine ⟨54136332041902107383106101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36090888027934738255404067 54136332041902107383106101)
              ·
                refine ⟨5075281128928322567166197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54136332041902107383106101 5075281128928322567166197)
                ·
                  refine ⟨475807605837030240671831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075281128928322567166197 475807605837030240671831)
                  ·
                    rfl

theorem cell23_8339688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 5].length) (baseStart_8339688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339688 prefixEnd_8339688 := by exact prefixLift 8339688
  have htrace : WordTrace (prefixWord ++ tailWord_8339688) baseStart_8339688 baseEnd_8339688 := by
    simpa [prefixWord, tailWord_8339688, baseEnd_8339688] using wordTrace_append hprefix tailTrace_8339688
  have hstable : (prefixWord ++ tailWord_8339688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339688).length < 2 ^ (prefixWord ++ tailWord_8339688).sum := by decide
  have hdescent : baseEnd_8339688 < baseStart_8339688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339698 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_8339698 : Nat := 118140960795 + 8339698 * 2 ^ 59
def prefixEnd_8339698 : Nat := 4983230072969 + 3 ^ 40 * 8339698 * 2
def baseEnd_8339698 : Nat := 4282273587339817126921433

theorem tailTrace_8339698 : CollatzResearch.WordTrace tailWord_8339698 prefixEnd_8339698 4282273587339817126921433 := by
  unfold tailWord_8339698
  simp only [CollatzResearch.WordTrace]
  refine ⟨76043443735176481967158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202782516627137285245757165 76043443735176481967158937)
  ·
    refine ⟨57032582801382361475369203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76043443735176481967158937 57032582801382361475369203)
    ·
      refine ⟨85548874202073542213053805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57032582801382361475369203 85548874202073542213053805)
      ·
        refine ⟨32080827825777578329895177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85548874202073542213053805 32080827825777578329895177)
        ·
          refine ⟨24060620869333183747421383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32080827825777578329895177 24060620869333183747421383)
          ·
            refine ⟨36090931303999775621132075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24060620869333183747421383 36090931303999775621132075)
            ·
              refine ⟨54136396955999663431698113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36090931303999775621132075 54136396955999663431698113)
              ·
                refine ⟨40602297716999747573773585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54136396955999663431698113 40602297716999747573773585)
                ·
                  refine ⟨30451723287749810680330189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40602297716999747573773585 30451723287749810680330189)
                  ·
                    refine ⟨11419396232906179005123821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30451723287749810680330189 11419396232906179005123821)
                    ·
                      refine ⟨4282273587339817126921433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419396232906179005123821 4282273587339817126921433)
                      ·
                        rfl

theorem cell23_8339698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_8339698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339698 prefixEnd_8339698 := by exact prefixLift 8339698
  have htrace : WordTrace (prefixWord ++ tailWord_8339698) baseStart_8339698 baseEnd_8339698 := by
    simpa [prefixWord, tailWord_8339698, baseEnd_8339698] using wordTrace_append hprefix tailTrace_8339698
  have hstable : (prefixWord ++ tailWord_8339698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339698).length < 2 ^ (prefixWord ++ tailWord_8339698).sum := by decide
  have hdescent : baseEnd_8339698 < baseStart_8339698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339721 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_8339721 : Nat := 118140960795 + 8339721 * 2 ^ 59
def prefixEnd_8339721 : Nat := 4983230072969 + 3 ^ 40 * 8339721 * 2
def baseEnd_8339721 : Nat := 4282285397394870536933827

theorem tailTrace_8339721 : CollatzResearch.WordTrace tailWord_8339721 prefixEnd_8339721 4282285397394870536933827 := by
  unfold tailWord_8339721
  simp only [CollatzResearch.WordTrace]
  refine ⟨304174613819622602796723017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202783075879748401864482011 304174613819622602796723017)
  ·
    refine ⟨228130960364716952097542263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304174613819622602796723017 228130960364716952097542263)
    ·
      refine ⟨342196440547075428146313395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228130960364716952097542263 342196440547075428146313395)
      ·
        refine ⟨513294660820613142219470093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342196440547075428146313395 513294660820613142219470093)
        ·
          refine ⟨192485497807729928332301285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513294660820613142219470093 192485497807729928332301285)
          ·
            refine ⟨36091030838949361562306491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192485497807729928332301285 36091030838949361562306491)
            ·
              refine ⟨54136546258424042343459737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36091030838949361562306491 54136546258424042343459737)
              ·
                refine ⟨40602409693818031757594803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54136546258424042343459737 40602409693818031757594803)
                ·
                  refine ⟨60903614540727047636392205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40602409693818031757594803 60903614540727047636392205)
                  ·
                    refine ⟨22838855452772642863647077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60903614540727047636392205 22838855452772642863647077)
                    ·
                      refine ⟨4282285397394870536933827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22838855452772642863647077 4282285397394870536933827)
                      ·
                        rfl

theorem cell23_8339721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_8339721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339721 prefixEnd_8339721 := by exact prefixLift 8339721
  have htrace : WordTrace (prefixWord ++ tailWord_8339721) baseStart_8339721 baseEnd_8339721 := by
    simpa [prefixWord, tailWord_8339721, baseEnd_8339721] using wordTrace_append hprefix tailTrace_8339721
  have hstable : (prefixWord ++ tailWord_8339721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339721).length < 2 ^ (prefixWord ++ tailWord_8339721).sum := by decide
  have hdescent : baseEnd_8339721 < baseStart_8339721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339865 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_8339865 : Nat := 118140960795 + 8339865 * 2 ^ 59
def prefixEnd_8339865 : Nat := 4983230072969 + 3 ^ 40 * 8339865 * 2
def baseEnd_8339865 : Nat := 4282359338609117973533165

theorem tailTrace_8339865 : CollatzResearch.WordTrace tailWord_8339865 prefixEnd_8339865 4282359338609117973533165 := by
  unfold tailWord_8339865
  simp only [CollatzResearch.WordTrace]
  refine ⟨304179865931100915389965049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202786577287400610259976699 304179865931100915389965049)
  ·
    refine ⟨228134899448325686542473787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304179865931100915389965049 228134899448325686542473787)
    ·
      refine ⟨342202349172488529813710681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228134899448325686542473787 342202349172488529813710681)
      ·
        refine ⟨256651761879366397360283011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342202349172488529813710681 256651761879366397360283011)
        ·
          refine ⟨384977642819049596040424517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256651761879366397360283011 384977642819049596040424517)
          ·
            refine ⟨72183308028571799257579597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384977642819049596040424517 72183308028571799257579597)
            ·
              refine ⟨27068740510714424721592349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72183308028571799257579597 27068740510714424721592349)
              ·
                refine ⟨10150777691517909270597131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27068740510714424721592349 10150777691517909270597131)
                ·
                  refine ⟨15226166537276863905895697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150777691517909270597131 15226166537276863905895697)
                  ·
                    refine ⟨11419624902957647929421773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15226166537276863905895697 11419624902957647929421773)
                    ·
                      refine ⟨4282359338609117973533165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419624902957647929421773 4282359338609117973533165)
                      ·
                        rfl

theorem cell23_8339865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_8339865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339865 prefixEnd_8339865 := by exact prefixLift 8339865
  have htrace : WordTrace (prefixWord ++ tailWord_8339865) baseStart_8339865 baseEnd_8339865 := by
    simpa [prefixWord, tailWord_8339865, baseEnd_8339865] using wordTrace_append hprefix tailTrace_8339865
  have hstable : (prefixWord ++ tailWord_8339865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339865).length < 2 ^ (prefixWord ++ tailWord_8339865).sum := by decide
  have hdescent : baseEnd_8339865 < baseStart_8339865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339872 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_8339872 : Nat := 118140960795 + 8339872 * 2 ^ 59
def prefixEnd_8339872 : Nat := 4983230072969 + 3 ^ 40 * 8339872 * 2
def baseEnd_8339872 : Nat := 1427454310991233148715211

theorem tailTrace_8339872 : CollatzResearch.WordTrace tailWord_8339872 prefixEnd_8339872 1427454310991233148715211 := by
  unfold tailWord_8339872
  simp only [CollatzResearch.WordTrace]
  refine ⟨152090060621037777792734935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202786747494717037056979913 152090060621037777792734935)
  ·
    refine ⟨228135090931556666689102403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152090060621037777792734935 228135090931556666689102403)
    ·
      refine ⟨342202636397335000033653605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228135090931556666689102403 342202636397335000033653605)
      ·
        refine ⟨64162994324500312506310051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342202636397335000033653605 64162994324500312506310051)
        ·
          refine ⟨96244491486750468759465077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64162994324500312506310051 96244491486750468759465077)
          ·
            refine ⟨9022921076882856446199851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96244491486750468759465077 9022921076882856446199851)
            ·
              refine ⟨13534381615324284669299777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9022921076882856446199851 13534381615324284669299777)
              ·
                refine ⟨10150786211493213501974833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13534381615324284669299777 10150786211493213501974833)
                ·
                  refine ⟨7613089658619910126481125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10150786211493213501974833 7613089658619910126481125)
                  ·
                    refine ⟨1427454310991233148715211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613089658619910126481125 1427454310991233148715211)
                    ·
                      rfl

theorem cell23_8339872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_8339872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339872 prefixEnd_8339872 := by exact prefixLift 8339872
  have htrace : WordTrace (prefixWord ++ tailWord_8339872) baseStart_8339872 baseEnd_8339872 := by
    simpa [prefixWord, tailWord_8339872, baseEnd_8339872] using wordTrace_append hprefix tailTrace_8339872
  have hstable : (prefixWord ++ tailWord_8339872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339872).length < 2 ^ (prefixWord ++ tailWord_8339872).sum := by decide
  have hdescent : baseEnd_8339872 < baseStart_8339872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339879 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_8339879 : Nat := 118140960795 + 8339879 * 2 ^ 59
def prefixEnd_8339879 : Nat := 4983230072969 + 3 ^ 40 * 8339879 * 2
def baseEnd_8339879 : Nat := 4282366527338280918758101

theorem tailTrace_8339879 : CollatzResearch.WordTrace tailWord_8339879 prefixEnd_8339879 4282366527338280918758101 := by
  unfold tailWord_8339879
  simp only [CollatzResearch.WordTrace]
  refine ⟨304180376553050195780974691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202786917702033463853983127 304180376553050195780974691)
  ·
    refine ⟨456270564829575293671462037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304180376553050195780974691 456270564829575293671462037)
    ·
      refine ⟨21387682726386341890849783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 456270564829575293671462037 21387682726386341890849783)
      ·
        refine ⟨32081524089579512836274675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21387682726386341890849783 32081524089579512836274675)
        ·
          refine ⟨48122286134369269254412013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32081524089579512836274675 48122286134369269254412013)
          ·
            refine ⟨18045857300388475970404505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48122286134369269254412013 18045857300388475970404505)
            ·
              refine ⟨13534392975291356977803379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18045857300388475970404505 13534392975291356977803379)
              ·
                refine ⟨20301589462937035466705069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13534392975291356977803379 20301589462937035466705069)
                ·
                  refine ⟨7613096048601388300014401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20301589462937035466705069 7613096048601388300014401)
                  ·
                    refine ⟨5709822036451041225010801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613096048601388300014401 5709822036451041225010801)
                    ·
                      refine ⟨4282366527338280918758101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709822036451041225010801 4282366527338280918758101)
                      ·
                        rfl

theorem cell23_8339879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_8339879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339879 prefixEnd_8339879 := by exact prefixLift 8339879
  have htrace : WordTrace (prefixWord ++ tailWord_8339879) baseStart_8339879 baseEnd_8339879 := by
    simpa [prefixWord, tailWord_8339879, baseEnd_8339879] using wordTrace_append hprefix tailTrace_8339879
  have hstable : (prefixWord ++ tailWord_8339879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339879).length < 2 ^ (prefixWord ++ tailWord_8339879).sum := by decide
  have hdescent : baseEnd_8339879 < baseStart_8339879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339881 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_8339881 : Nat := 118140960795 + 8339881 * 2 ^ 59
def prefixEnd_8339881 : Nat := 4983230072969 + 3 ^ 40 * 8339881 * 2
def baseEnd_8339881 : Nat := 1427455851433196636977697

theorem tailTrace_8339881 : CollatzResearch.WordTrace tailWord_8339881 prefixEnd_8339881 1427455851433196636977697 := by
  unfold tailWord_8339881
  simp only [CollatzResearch.WordTrace]
  refine ⟨304180449499042950122547497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202786966332695300081698331 304180449499042950122547497)
  ·
    refine ⟨228135337124282212591910623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304180449499042950122547497 228135337124282212591910623)
    ·
      refine ⟨342203005686423318887865935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228135337124282212591910623 342203005686423318887865935)
      ·
        refine ⟨513304508529634978331798903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342203005686423318887865935 513304508529634978331798903)
        ·
          refine ⟨769956762794452467497698355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513304508529634978331798903 769956762794452467497698355)
          ·
            refine ⟨1154935144191678701246547533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769956762794452467497698355 1154935144191678701246547533)
            ·
              refine ⟨433100679071879512967455325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154935144191678701246547533 433100679071879512967455325)
              ·
                refine ⟨162412754651954817362795747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433100679071879512967455325 162412754651954817362795747)
                ·
                  refine ⟨243619131977932226044193621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162412754651954817362795747 243619131977932226044193621)
                  ·
                    refine ⟨1427455851433196636977697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243619131977932226044193621 1427455851433196636977697)
                    ·
                      rfl

theorem cell23_8339881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_8339881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339881 prefixEnd_8339881 := by exact prefixLift 8339881
  have htrace : WordTrace (prefixWord ++ tailWord_8339881) baseStart_8339881 baseEnd_8339881 := by
    simpa [prefixWord, tailWord_8339881, baseEnd_8339881] using wordTrace_append hprefix tailTrace_8339881
  have hstable : (prefixWord ++ tailWord_8339881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339881).length < 2 ^ (prefixWord ++ tailWord_8339881).sum := by decide
  have hdescent : baseEnd_8339881 < baseStart_8339881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339895 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_8339895 : Nat := 118140960795 + 8339895 * 2 ^ 59
def prefixEnd_8339895 : Nat := 4983230072969 + 3 ^ 40 * 8339895 * 2
def baseEnd_8339895 : Nat := 4282374743028752856158027

theorem tailTrace_8339895 : CollatzResearch.WordTrace tailWord_8339895 prefixEnd_8339895 4282374743028752856158027 := by
  unfold tailWord_8339895
  simp only [CollatzResearch.WordTrace]
  refine ⟨304180960120992230513557139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202787306747328153675704759 304180960120992230513557139)
  ·
    refine ⟨456271440181488345770335709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304180960120992230513557139 456271440181488345770335709)
    ·
      refine ⟨171101790068058129663875891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456271440181488345770335709 171101790068058129663875891)
      ·
        refine ⟨256652685102087194495813837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171101790068058129663875891 256652685102087194495813837)
        ·
          refine ⟨96244756913282697935930189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256652685102087194495813837 96244756913282697935930189)
          ·
            refine ⟨36091783842481011725973821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96244756913282697935930189 36091783842481011725973821)
            ·
              refine ⟨13534418940930379397240183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36091783842481011725973821 13534418940930379397240183)
              ·
                refine ⟨20301628411395569095860275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13534418940930379397240183 20301628411395569095860275)
                ·
                  refine ⟨30452442617093353643790413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20301628411395569095860275 30452442617093353643790413)
                  ·
                    refine ⟨11419665981410007616421405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30452442617093353643790413 11419665981410007616421405)
                    ·
                      refine ⟨4282374743028752856158027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419665981410007616421405 4282374743028752856158027)
                      ·
                        rfl

theorem cell23_8339895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_8339895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339895 prefixEnd_8339895 := by exact prefixLift 8339895
  have htrace : WordTrace (prefixWord ++ tailWord_8339895) baseStart_8339895 baseEnd_8339895 := by
    simpa [prefixWord, tailWord_8339895, baseEnd_8339895] using wordTrace_append hprefix tailTrace_8339895
  have hstable : (prefixWord ++ tailWord_8339895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339895).length < 2 ^ (prefixWord ++ tailWord_8339895).sum := by decide
  have hdescent : baseEnd_8339895 < baseStart_8339895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339918 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_8339918 : Nat := 118140960795 + 8339918 * 2 ^ 59
def prefixEnd_8339918 : Nat := 4983230072969 + 3 ^ 40 * 8339918 * 2
def baseEnd_8339918 : Nat := 4282386553083806266170421

theorem tailTrace_8339918 : CollatzResearch.WordTrace tailWord_8339918 prefixEnd_8339918 4282386553083806266170421 := by
  unfold tailWord_8339918
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022724874988613180205551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202787865999939270294429605 38022724874988613180205551)
  ·
    refine ⟨57034087312482919770308327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38022724874988613180205551 57034087312482919770308327)
    ·
      refine ⟨85551130968724379655462491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57034087312482919770308327 85551130968724379655462491)
      ·
        refine ⟨128326696453086569483193737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85551130968724379655462491 128326696453086569483193737)
        ·
          refine ⟨96245022339814927112395303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128326696453086569483193737 96245022339814927112395303)
          ·
            refine ⟨144367533509722390668592955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96245022339814927112395303 144367533509722390668592955)
            ·
              refine ⟨216551300264583586002889433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144367533509722390668592955 216551300264583586002889433)
              ·
                refine ⟨162413475198437689502167075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216551300264583586002889433 162413475198437689502167075)
                ·
                  refine ⟨243620212797656534253250613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162413475198437689502167075 243620212797656534253250613)
                  ·
                    refine ⟨22839394949780300086242245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243620212797656534253250613 22839394949780300086242245)
                    ·
                      refine ⟨4282386553083806266170421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22839394949780300086242245 4282386553083806266170421)
                      ·
                        rfl

theorem cell23_8339918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_8339918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339918 prefixEnd_8339918 := by exact prefixLift 8339918
  have htrace : WordTrace (prefixWord ++ tailWord_8339918) baseStart_8339918 baseEnd_8339918 := by
    simpa [prefixWord, tailWord_8339918, baseEnd_8339918] using wordTrace_append hprefix tailTrace_8339918
  have hstable : (prefixWord ++ tailWord_8339918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339918).length < 2 ^ (prefixWord ++ tailWord_8339918).sum := by decide
  have hdescent : baseEnd_8339918 < baseStart_8339918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339946 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_8339946 : Nat := 118140960795 + 8339946 * 2 ^ 59
def prefixEnd_8339946 : Nat := 4983230072969 + 3 ^ 40 * 8339946 * 2
def baseEnd_8339946 : Nat := 4282400930542132156620293

theorem tailTrace_8339946 : CollatzResearch.WordTrace tailWord_8339946 prefixEnd_8339946 4282400930542132156620293 := by
  unfold tailWord_8339946
  simp only [CollatzResearch.WordTrace]
  refine ⟨76045705060951866555915923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202788546829204977482442461 76045705060951866555915923)
  ·
    refine ⟨114068557591427799833873885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76045705060951866555915923 114068557591427799833873885)
    ·
      refine ⟨42775709096785424937702707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114068557591427799833873885 42775709096785424937702707)
      ·
        refine ⟨64163563645178137406554061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42775709096785424937702707 64163563645178137406554061)
        ·
          refine ⟨24061336366941801527457773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64163563645178137406554061 24061336366941801527457773)
          ·
            refine ⟨9023001137603175572796665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24061336366941801527457773 9023001137603175572796665)
            ·
              refine ⟨6767250853202381679597499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023001137603175572796665 6767250853202381679597499)
              ·
                refine ⟨10150876279803572519396249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767250853202381679597499 10150876279803572519396249)
                ·
                  refine ⟨7613157209852679389547187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10150876279803572519396249 7613157209852679389547187)
                  ·
                    refine ⟨11419735814779019084320781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613157209852679389547187 11419735814779019084320781)
                    ·
                      refine ⟨4282400930542132156620293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419735814779019084320781 4282400930542132156620293)
                      ·
                        rfl

theorem cell23_8339946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_8339946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339946 prefixEnd_8339946 := by exact prefixLift 8339946
  have htrace : WordTrace (prefixWord ++ tailWord_8339946) baseStart_8339946 baseEnd_8339946 := by
    simpa [prefixWord, tailWord_8339946, baseEnd_8339946] using wordTrace_append hprefix tailTrace_8339946
  have hstable : (prefixWord ++ tailWord_8339946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339946).length < 2 ^ (prefixWord ++ tailWord_8339946).sum := by decide
  have hdescent : baseEnd_8339946 < baseStart_8339946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339948 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_8339948 : Nat := 118140960795 + 8339948 * 2 ^ 59
def prefixEnd_8339948 : Nat := 4983230072969 + 3 ^ 40 * 8339948 * 2
def baseEnd_8339948 : Nat := 4282401957503441148795283

theorem tailTrace_8339948 : CollatzResearch.WordTrace tailWord_8339948 prefixEnd_8339948 4282401957503441148795283 := by
  unfold tailWord_8339948
  simp only [CollatzResearch.WordTrace]
  refine ⟨152091446594900110282618249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202788595459866813710157665 152091446594900110282618249)
  ·
    refine ⟨114068584946175082711963687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152091446594900110282618249 114068584946175082711963687)
    ·
      refine ⟨171102877419262624067945531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114068584946175082711963687 171102877419262624067945531)
      ·
        refine ⟨256654316128893936101918297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171102877419262624067945531 256654316128893936101918297)
        ·
          refine ⟨192490737096670452076438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256654316128893936101918297 192490737096670452076438723)
          ·
            refine ⟨288736105645005678114658085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192490737096670452076438723 288736105645005678114658085)
            ·
              refine ⟨54138019808438564646498391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288736105645005678114658085 54138019808438564646498391)
              ·
                refine ⟨81207029712657846969747587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54138019808438564646498391 81207029712657846969747587)
                ·
                  refine ⟨121810544568986770454621381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81207029712657846969747587 121810544568986770454621381)
                  ·
                    refine ⟨22839477106685019460241509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121810544568986770454621381 22839477106685019460241509)
                    ·
                      refine ⟨4282401957503441148795283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22839477106685019460241509 4282401957503441148795283)
                      ·
                        rfl

theorem cell23_8339948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_8339948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339948 prefixEnd_8339948 := by exact prefixLift 8339948
  have htrace : WordTrace (prefixWord ++ tailWord_8339948) baseStart_8339948 baseEnd_8339948 := by
    simpa [prefixWord, tailWord_8339948, baseEnd_8339948] using wordTrace_append hprefix tailTrace_8339948
  have hstable : (prefixWord ++ tailWord_8339948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339948).length < 2 ^ (prefixWord ++ tailWord_8339948).sum := by decide
  have hdescent : baseEnd_8339948 < baseStart_8339948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8339992 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 5]
def baseStart_8339992 : Nat := 118140960795 + 8339992 * 2 ^ 59
def prefixEnd_8339992 : Nat := 4983230072969 + 3 ^ 40 * 8339992 * 2
def baseEnd_8339992 : Nat := 475824950072470997405009

theorem tailTrace_8339992 : CollatzResearch.WordTrace tailWord_8339992 prefixEnd_8339992 475824950072470997405009 := by
  unfold tailWord_8339992
  simp only [CollatzResearch.WordTrace]
  refine ⟨152092249000820408039919115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202789665334427210719892153 152092249000820408039919115)
  ·
    refine ⟨228138373501230612059878673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152092249000820408039919115 228138373501230612059878673)
    ·
      refine ⟨171103780125922959044909005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228138373501230612059878673 171103780125922959044909005)
      ·
        refine ⟨64163917547221109641840877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171103780125922959044909005 64163917547221109641840877)
        ·
          refine ⟨24061469080207916115690329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64163917547221109641840877 24061469080207916115690329)
          ·
            refine ⟨18046101810155937086767747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24061469080207916115690329 18046101810155937086767747)
            ·
              refine ⟨27069152715233905630151621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18046101810155937086767747 27069152715233905630151621)
              ·
                refine ⟨5075466134106357305653429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27069152715233905630151621 5075466134106357305653429)
                ·
                  refine ⟨475824950072470997405009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075466134106357305653429 475824950072470997405009)
                  ·
                    rfl

theorem cell23_8339992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 5].length) (baseStart_8339992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8339992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8339992 prefixEnd_8339992 := by exact prefixLift 8339992
  have htrace : WordTrace (prefixWord ++ tailWord_8339992) baseStart_8339992 baseEnd_8339992 := by
    simpa [prefixWord, tailWord_8339992, baseEnd_8339992] using wordTrace_append hprefix tailTrace_8339992
  have hstable : (prefixWord ++ tailWord_8339992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8339992).length < 2 ^ (prefixWord ++ tailWord_8339992).sum := by decide
  have hdescent : baseEnd_8339992 < baseStart_8339992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8339992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340022 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_8340022 : Nat := 118140960795 + 8340022 * 2 ^ 59
def prefixEnd_8340022 : Nat := 4983230072969 + 3 ^ 40 * 8340022 * 2
def baseEnd_8340022 : Nat := 1427479985023957953089981

theorem tailTrace_8340022 : CollatzResearch.WordTrace tailWord_8340022 prefixEnd_8340022 1427479985023957953089981 := by
  unfold tailWord_8340022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19011599511970758200214395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202790394794354754135620213 19011599511970758200214395)
  ·
    refine ⟨28517399267956137300321593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19011599511970758200214395 28517399267956137300321593)
    ·
      refine ⟨21388049450967102975241195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28517399267956137300321593 21388049450967102975241195)
      ·
        refine ⟨32082074176450654462861793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21388049450967102975241195 32082074176450654462861793)
        ·
          refine ⟨24061555632337990847146345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32082074176450654462861793 24061555632337990847146345)
          ·
            refine ⟨18046166724253493135359759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24061555632337990847146345 18046166724253493135359759)
            ·
              refine ⟨27069250086380239703039639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18046166724253493135359759 27069250086380239703039639)
              ·
                refine ⟨40603875129570359554559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27069250086380239703039639 40603875129570359554559459)
                ·
                  refine ⟨60905812694355539331839189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40603875129570359554559459 60905812694355539331839189)
                  ·
                    refine ⟨1427479985023957953089981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60905812694355539331839189 1427479985023957953089981)
                    ·
                      rfl

theorem cell23_8340022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_8340022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340022 prefixEnd_8340022 := by exact prefixLift 8340022
  have htrace : WordTrace (prefixWord ++ tailWord_8340022) baseStart_8340022 baseEnd_8340022 := by
    simpa [prefixWord, tailWord_8340022, baseEnd_8340022] using wordTrace_append hprefix tailTrace_8340022
  have hstable : (prefixWord ++ tailWord_8340022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340022).length < 2 ^ (prefixWord ++ tailWord_8340022).sum := by decide
  have hdescent : baseEnd_8340022 < baseStart_8340022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340025 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_8340025 : Nat := 118140960795 + 8340025 * 2 ^ 59
def prefixEnd_8340025 : Nat := 4983230072969 + 3 ^ 40 * 8340025 * 2
def baseEnd_8340025 : Nat := 4282441495513837347532429

theorem tailTrace_8340025 : CollatzResearch.WordTrace tailWord_8340025 prefixEnd_8340025 4282441495513837347532429 := by
  unfold tailWord_8340025
  simp only [CollatzResearch.WordTrace]
  refine ⟨304185701610521262715789529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202790467740347508477193019 304185701610521262715789529)
  ·
    refine ⟨228139276207890947036842147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304185701610521262715789529 228139276207890947036842147)
    ·
      refine ⟨342208914311836420555263221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228139276207890947036842147 342208914311836420555263221)
      ·
        refine ⟨32082085716734664427055927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342208914311836420555263221 32082085716734664427055927)
        ·
          refine ⟨48123128575101996640583891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32082085716734664427055927 48123128575101996640583891)
          ·
            refine ⟨72184692862652994960875837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48123128575101996640583891 72184692862652994960875837)
            ·
              refine ⟨27069259823494873110328439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72184692862652994960875837 27069259823494873110328439)
              ·
                refine ⟨40603889735242309665492659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27069259823494873110328439 40603889735242309665492659)
                ·
                  refine ⟨60905834602863464498238989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40603889735242309665492659 60905834602863464498238989)
                  ·
                    refine ⟨22839687976073799186839621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60905834602863464498238989 22839687976073799186839621)
                    ·
                      refine ⟨4282441495513837347532429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22839687976073799186839621 4282441495513837347532429)
                      ·
                        rfl

theorem cell23_8340025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_8340025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340025 prefixEnd_8340025 := by exact prefixLift 8340025
  have htrace : WordTrace (prefixWord ++ tailWord_8340025) baseStart_8340025 baseEnd_8340025 := by
    simpa [prefixWord, tailWord_8340025, baseEnd_8340025] using wordTrace_append hprefix tailTrace_8340025
  have hstable : (prefixWord ++ tailWord_8340025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340025).length < 2 ^ (prefixWord ++ tailWord_8340025).sum := by decide
  have hdescent : baseEnd_8340025 < baseStart_8340025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340042 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_8340042 : Nat := 118140960795 + 8340042 * 2 ^ 59
def prefixEnd_8340042 : Nat := 4983230072969 + 3 ^ 40 * 8340042 * 2
def baseEnd_8340042 : Nat := 4282450224684963781019851

theorem tailTrace_8340042 : CollatzResearch.WordTrace tailWord_8340042 prefixEnd_8340042 4282450224684963781019851 := by
  unfold tailWord_8340042
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046580412864918654789595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202790881100973116412772253 76046580412864918654789595)
  ·
    refine ⟨114069870619297377982184393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76046580412864918654789595 114069870619297377982184393)
    ·
      refine ⟨85552402964473033486638295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114069870619297377982184393 85552402964473033486638295)
      ·
        refine ⟨128328604446709550229957443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85552402964473033486638295 128328604446709550229957443)
        ·
          refine ⟨192492906670064325344936165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128328604446709550229957443 192492906670064325344936165)
          ·
            refine ⟨36092420000637061002175531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192492906670064325344936165 36092420000637061002175531)
            ·
              refine ⟨54138630000955591503263297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36092420000637061002175531 54138630000955591503263297)
              ·
                refine ⟨40603972500716693627447473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54138630000955591503263297 40603972500716693627447473)
                ·
                  refine ⟨30452979375537520220585605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40603972500716693627447473 30452979375537520220585605)
                  ·
                    refine ⟨5709933632913285041359801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30452979375537520220585605 5709933632913285041359801)
                    ·
                      refine ⟨4282450224684963781019851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5709933632913285041359801 4282450224684963781019851)
                      ·
                        rfl

theorem cell23_8340042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_8340042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340042 prefixEnd_8340042 := by exact prefixLift 8340042
  have htrace : WordTrace (prefixWord ++ tailWord_8340042) baseStart_8340042 baseEnd_8340042 := by
    simpa [prefixWord, tailWord_8340042, baseEnd_8340042] using wordTrace_append hprefix tailTrace_8340042
  have hstable : (prefixWord ++ tailWord_8340042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340042).length < 2 ^ (prefixWord ++ tailWord_8340042).sum := by decide
  have hdescent : baseEnd_8340042 < baseStart_8340042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340052 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_8340052 : Nat := 118140960795 + 8340052 * 2 ^ 59
def prefixEnd_8340052 : Nat := 4983230072969 + 3 ^ 40 * 8340052 * 2
def baseEnd_8340052 : Nat := 1427485119830502913964935

theorem tailTrace_8340052 : CollatzResearch.WordTrace tailWord_8340052 prefixEnd_8340052 1427485119830502913964935 := by
  unfold tailWord_8340052
  simp only [CollatzResearch.WordTrace]
  refine ⟨152093343190711723163511205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202791124254282297551348273 152093343190711723163511205)
  ·
    refine ⟨28517501848258448093158351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152093343190711723163511205 28517501848258448093158351)
    ·
      refine ⟨42776252772387672139737527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28517501848258448093158351 42776252772387672139737527)
      ·
        refine ⟨64164379158581508209606291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42776252772387672139737527 64164379158581508209606291)
        ·
          refine ⟨96246568737872262314409437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64164379158581508209606291 96246568737872262314409437)
          ·
            refine ⟨36092463276702098367903539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96246568737872262314409437 36092463276702098367903539)
            ·
              refine ⟨54138694915053147551855309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36092463276702098367903539 54138694915053147551855309)
              ·
                refine ⟨20302010593144930331945741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54138694915053147551855309 20302010593144930331945741)
                ·
                  refine ⟨7613253972429348874479653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20302010593144930331945741 7613253972429348874479653)
                  ·
                    refine ⟨1427485119830502913964935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613253972429348874479653 1427485119830502913964935)
                    ·
                      rfl

theorem cell23_8340052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_8340052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340052 prefixEnd_8340052 := by exact prefixLift 8340052
  have htrace : WordTrace (prefixWord ++ tailWord_8340052) baseStart_8340052 baseEnd_8340052 := by
    simpa [prefixWord, tailWord_8340052, baseEnd_8340052] using wordTrace_append hprefix tailTrace_8340052
  have hstable : (prefixWord ++ tailWord_8340052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340052).length < 2 ^ (prefixWord ++ tailWord_8340052).sum := by decide
  have hdescent : baseEnd_8340052 < baseStart_8340052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340092 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_8340092 : Nat := 118140960795 + 8340092 * 2 ^ 59
def prefixEnd_8340092 : Nat := 4983230072969 + 3 ^ 40 * 8340092 * 2
def baseEnd_8340092 : Nat := 4282475898717688585394621

theorem tailTrace_8340092 : CollatzResearch.WordTrace tailWord_8340092 prefixEnd_8340092 4282475898717688585394621 := by
  unfold tailWord_8340092
  simp only [CollatzResearch.WordTrace]
  refine ⟨152094072650639266579239265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202792096867519022105652353 152094072650639266579239265)
  ·
    refine ⟨114070554487979449934429449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152094072650639266579239265 114070554487979449934429449)
    ·
      refine ⟨85552915865984587450822087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114070554487979449934429449 85552915865984587450822087)
      ·
        refine ⟨128329373798976881176233131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85552915865984587450822087 128329373798976881176233131)
        ·
          refine ⟨192494060698465321764349697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128329373798976881176233131 192494060698465321764349697)
          ·
            refine ⟨144370545523848991323262273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192494060698465321764349697 144370545523848991323262273)
            ·
              refine ⟨108277909142886743492446705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144370545523848991323262273 108277909142886743492446705)
              ·
                refine ⟨81208431857165057619335029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108277909142886743492446705 81208431857165057619335029)
                ·
                  refine ⟨7613290486609224151812659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81208431857165057619335029 7613290486609224151812659)
                  ·
                    refine ⟨11419935729913836227718989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613290486609224151812659 11419935729913836227718989)
                    ·
                      refine ⟨4282475898717688585394621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11419935729913836227718989 4282475898717688585394621)
                      ·
                        rfl

theorem cell23_8340092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_8340092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340092 prefixEnd_8340092 := by exact prefixLift 8340092
  have htrace : WordTrace (prefixWord ++ tailWord_8340092) baseStart_8340092 baseEnd_8340092 := by
    simpa [prefixWord, tailWord_8340092, baseEnd_8340092] using wordTrace_append hprefix tailTrace_8340092
  have hstable : (prefixWord ++ tailWord_8340092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340092).length < 2 ^ (prefixWord ++ tailWord_8340092).sum := by decide
  have hdescent : baseEnd_8340092 < baseStart_8340092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340115 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4]
def baseStart_8340115 : Nat := 118140960795 + 8340115 * 2 ^ 59
def prefixEnd_8340115 : Nat := 4983230072969 + 3 ^ 40 * 8340115 * 2
def baseEnd_8340115 : Nat := 4282487708772741995407015

theorem tailTrace_8340115 : CollatzResearch.WordTrace tailWord_8340115 prefixEnd_8340115 4282487708772741995407015 := by
  unfold tailWord_8340115
  simp only [CollatzResearch.WordTrace]
  refine ⟨304188984180195208086565799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202792656120130138724377199 304188984180195208086565799)
  ·
    refine ⟨456283476270292812129848699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304188984180195208086565799 456283476270292812129848699)
    ·
      refine ⟨684425214405439218194773049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456283476270292812129848699 684425214405439218194773049)
      ·
        refine ⟨513318910804079413646079787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684425214405439218194773049 513318910804079413646079787)
        ·
          refine ⟨769978366206119120469119681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513318910804079413646079787 769978366206119120469119681)
          ·
            refine ⟨577483774654589340351839761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769978366206119120469119681 577483774654589340351839761)
            ·
              refine ⟨433112830990942005263879821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577483774654589340351839761 433112830990942005263879821)
              ·
                refine ⟨162417311621603251973954933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433112830990942005263879821 162417311621603251973954933)
                ·
                  refine ⟨15226622964525304872558275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162417311621603251973954933 15226622964525304872558275)
                  ·
                    refine ⟨22839934446787957308837413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15226622964525304872558275 22839934446787957308837413)
                    ·
                      refine ⟨4282487708772741995407015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22839934446787957308837413 4282487708772741995407015)
                      ·
                        rfl

theorem cell23_8340115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_8340115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340115 prefixEnd_8340115 := by exact prefixLift 8340115
  have htrace : WordTrace (prefixWord ++ tailWord_8340115) baseStart_8340115 baseEnd_8340115 := by
    simpa [prefixWord, tailWord_8340115, baseEnd_8340115] using wordTrace_append hprefix tailTrace_8340115
  have hstable : (prefixWord ++ tailWord_8340115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340115).length < 2 ^ (prefixWord ++ tailWord_8340115).sum := by decide
  have hdescent : baseEnd_8340115 < baseStart_8340115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340116 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 6]
def baseStart_8340116 : Nat := 118140960795 + 8340116 * 2 ^ 59
def prefixEnd_8340116 : Nat := 4983230072969 + 3 ^ 40 * 8340116 * 2
def baseEnd_8340116 : Nat := 475832024694821832388279

theorem tailTrace_8340116 : CollatzResearch.WordTrace tailWord_8340116 prefixEnd_8340116 475832024694821832388279 := by
  unfold tailWord_8340116
  simp only [CollatzResearch.WordTrace]
  refine ⟨152094510326595792628676101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202792680435461056838234801 152094510326595792628676101)
  ·
    refine ⟨28517720686236711117876769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152094510326595792628676101 28517720686236711117876769)
    ·
      refine ⟨21388290514677533338407577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28517720686236711117876769 21388290514677533338407577)
      ·
        refine ⟨16041217886008150003805683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21388290514677533338407577 16041217886008150003805683)
        ·
          refine ⟨24061826829012225005708525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041217886008150003805683 24061826829012225005708525)
          ·
            refine ⟨9023185060879584377140697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24061826829012225005708525 9023185060879584377140697)
            ·
              refine ⟨6767388795659688282855523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023185060879584377140697 6767388795659688282855523)
              ·
                refine ⟨10151083193489532424283285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767388795659688282855523 10151083193489532424283285)
                ·
                  refine ⟨475832024694821832388279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10151083193489532424283285 475832024694821832388279)
                  ·
                    rfl

theorem cell23_8340116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_8340116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340116 prefixEnd_8340116 := by exact prefixLift 8340116
  have htrace : WordTrace (prefixWord ++ tailWord_8340116) baseStart_8340116 baseEnd_8340116 := by
    simpa [prefixWord, tailWord_8340116, baseEnd_8340116] using wordTrace_append hprefix tailTrace_8340116
  have hstable : (prefixWord ++ tailWord_8340116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340116).length < 2 ^ (prefixWord ++ tailWord_8340116).sum := by decide
  have hdescent : baseEnd_8340116 < baseStart_8340116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340132 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_8340132 : Nat := 118140960795 + 8340132 * 2 ^ 59
def prefixEnd_8340132 : Nat := 4983230072969 + 3 ^ 40 * 8340132 * 2
def baseEnd_8340132 : Nat := 4282496437943868428894437

theorem tailTrace_8340132 : CollatzResearch.WordTrace tailWord_8340132 prefixEnd_8340132 4282496437943868428894437 := by
  unfold tailWord_8340132
  simp only [CollatzResearch.WordTrace]
  refine ⟨152094802110566809994967325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202793069480755746659956433 152094802110566809994967325)
  ·
    refine ⟨57035550791462553748112747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152094802110566809994967325 57035550791462553748112747)
    ·
      refine ⟨85553326187193830622169121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57035550791462553748112747 85553326187193830622169121)
      ·
        refine ⟨64164994640395372966626841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85553326187193830622169121 64164994640395372966626841)
        ·
          refine ⟨48123745980296529724970131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64164994640395372966626841 48123745980296529724970131)
          ·
            refine ⟨72185618970444794587455197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48123745980296529724970131 72185618970444794587455197)
            ·
              refine ⟨27069607113916797970295699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72185618970444794587455197 27069607113916797970295699)
              ·
                refine ⟨40604410670875196955443549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27069607113916797970295699 40604410670875196955443549)
                ·
                  refine ⟨15226654001578198858291331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40604410670875196955443549 15226654001578198858291331)
                  ·
                    refine ⟨22839981002367298287436997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15226654001578198858291331 22839981002367298287436997)
                    ·
                      refine ⟨4282496437943868428894437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22839981002367298287436997 4282496437943868428894437)
                      ·
                        rfl

theorem cell23_8340132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_8340132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340132 prefixEnd_8340132 := by exact prefixLift 8340132
  have htrace : WordTrace (prefixWord ++ tailWord_8340132) baseStart_8340132 baseEnd_8340132 := by
    simpa [prefixWord, tailWord_8340132, baseEnd_8340132] using wordTrace_append hprefix tailTrace_8340132
  have hstable : (prefixWord ++ tailWord_8340132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340132).length < 2 ^ (prefixWord ++ tailWord_8340132).sum := by decide
  have hdescent : baseEnd_8340132 < baseStart_8340132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340159 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 2, 4]
def baseStart_8340159 : Nat := 118140960795 + 8340159 * 2 ^ 59
def prefixEnd_8340159 : Nat := 4983230072969 + 3 ^ 40 * 8340159 * 2
def baseEnd_8340159 : Nat := 1427503433973846607752271

theorem tailTrace_8340159 : CollatzResearch.WordTrace tailWord_8340159 prefixEnd_8340159 1427503433973846607752271 := by
  unfold tailWord_8340159
  simp only [CollatzResearch.WordTrace]
  refine ⟨304190588992035803601167531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202793725994690535734111687 304190588992035803601167531)
  ·
    refine ⟨456285883488053705401751297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304190588992035803601167531 456285883488053705401751297)
    ·
      refine ⟨342214412616040279051313473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456285883488053705401751297 342214412616040279051313473)
      ·
        refine ⟨256660809462030209288485105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342214412616040279051313473 256660809462030209288485105)
        ·
          refine ⟨192495607096522656966363829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256660809462030209288485105 192495607096522656966363829)
          ·
            refine ⟨18046463165298999090596609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192495607096522656966363829 18046463165298999090596609)
            ·
              refine ⟨13534847373974249317947457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046463165298999090596609 13534847373974249317947457)
              ·
                refine ⟨10151135530480686988460593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13534847373974249317947457 10151135530480686988460593)
                ·
                  refine ⟨7613351647860515241345445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151135530480686988460593 7613351647860515241345445)
                  ·
                    refine ⟨1427503433973846607752271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613351647860515241345445 1427503433973846607752271)
                    ·
                      rfl

theorem cell23_8340159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_8340159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340159 prefixEnd_8340159 := by exact prefixLift 8340159
  have htrace : WordTrace (prefixWord ++ tailWord_8340159) baseStart_8340159 baseEnd_8340159 := by
    simpa [prefixWord, tailWord_8340159, baseEnd_8340159] using wordTrace_append hprefix tailTrace_8340159
  have hstable : (prefixWord ++ tailWord_8340159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340159).length < 2 ^ (prefixWord ++ tailWord_8340159).sum := by decide
  have hdescent : baseEnd_8340159 < baseStart_8340159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340172 : List Nat := [2, 2, 1, 5, 1, 1, 3, 8]
def baseStart_8340172 : Nat := 118140960795 + 8340172 * 2 ^ 59
def prefixEnd_8340172 : Nat := 4983230072969 + 3 ^ 40 * 8340172 * 2
def baseEnd_8340172 : Nat := 158611739895186973051639

theorem tailTrace_8340172 : CollatzResearch.WordTrace tailWord_8340172 prefixEnd_8340172 158611739895186973051639 := by
  unfold tailWord_8340172
  simp only [CollatzResearch.WordTrace]
  refine ⟨152095531570494353410695385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202794042093992471214260513 152095531570494353410695385)
  ·
    refine ⟨114071648677870765058021539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152095531570494353410695385 114071648677870765058021539)
    ·
      refine ⟨171107473016806147587032309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114071648677870765058021539 171107473016806147587032309)
      ·
        refine ⟨16041325595325576336284279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171107473016806147587032309 16041325595325576336284279)
        ·
          refine ⟨24061988392988364504426419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041325595325576336284279 24061988392988364504426419)
          ·
            refine ⟨36092982589482546756639629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061988392988364504426419 36092982589482546756639629)
            ·
              refine ⟨13534868471055955033739861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36092982589482546756639629 13534868471055955033739861)
              ·
                refine ⟨158611739895186973051639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13534868471055955033739861 158611739895186973051639)
                ·
                  rfl

theorem cell23_8340172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 8].length) (baseStart_8340172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340172 prefixEnd_8340172 := by exact prefixLift 8340172
  have htrace : WordTrace (prefixWord ++ tailWord_8340172) baseStart_8340172 baseEnd_8340172 := by
    simpa [prefixWord, tailWord_8340172, baseEnd_8340172] using wordTrace_append hprefix tailTrace_8340172
  have hstable : (prefixWord ++ tailWord_8340172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340172).length < 2 ^ (prefixWord ++ tailWord_8340172).sum := by decide
  have hdescent : baseEnd_8340172 < baseStart_8340172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340185 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_8340185 : Nat := 118140960795 + 8340185 * 2 ^ 59
def prefixEnd_8340185 : Nat := 4983230072969 + 3 ^ 40 * 8340185 * 2
def baseEnd_8340185 : Nat := 1427507884139518907177231

theorem tailTrace_8340185 : CollatzResearch.WordTrace tailWord_8340185 prefixEnd_8340185 1427507884139518907177231 := by
  unfold tailWord_8340185
  simp only [CollatzResearch.WordTrace]
  refine ⟨304191537289941610041614009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202794358193294406694409339 304191537289941610041614009)
  ·
    refine ⟨228143652967456207531210507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304191537289941610041614009 228143652967456207531210507)
    ·
      refine ⟨342215479451184311296815761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228143652967456207531210507 342215479451184311296815761)
      ·
        refine ⟨256661609588388233472611821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342215479451184311296815761 256661609588388233472611821)
        ·
          refine ⟨96248103595645587552229433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256661609588388233472611821 96248103595645587552229433)
          ·
            refine ⟨72186077696734190664172075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96248103595645587552229433 72186077696734190664172075)
            ·
              refine ⟨108279116545101285996258113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72186077696734190664172075 108279116545101285996258113)
              ·
                refine ⟨81209337408825964497193585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108279116545101285996258113 81209337408825964497193585)
                ·
                  refine ⟨60907003056619473372895189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81209337408825964497193585 60907003056619473372895189)
                  ·
                    refine ⟨1427507884139518907177231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60907003056619473372895189 1427507884139518907177231)
                    ·
                      rfl

theorem cell23_8340185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_8340185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340185 prefixEnd_8340185 := by exact prefixLift 8340185
  have htrace : WordTrace (prefixWord ++ tailWord_8340185) baseStart_8340185 baseEnd_8340185 := by
    simpa [prefixWord, tailWord_8340185, baseEnd_8340185] using wordTrace_append hprefix tailTrace_8340185
  have hstable : (prefixWord ++ tailWord_8340185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340185).length < 2 ^ (prefixWord ++ tailWord_8340185).sum := by decide
  have hdescent : baseEnd_8340185 < baseStart_8340185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340200 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_8340200 : Nat := 118140960795 + 8340200 * 2 ^ 59
def prefixEnd_8340200 : Nat := 4983230072969 + 3 ^ 40 * 8340200 * 2
def baseEnd_8340200 : Nat := 4282531354628374162844125

theorem tailTrace_8340200 : CollatzResearch.WordTrace tailWord_8340200 prefixEnd_8340200 4282531354628374162844125 := by
  unfold tailWord_8340200
  simp only [CollatzResearch.WordTrace]
  refine ⟨152096042192443633801705027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202794722923258178402273369 152096042192443633801705027)
  ·
    refine ⟨228144063288665450702557541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152096042192443633801705027 228144063288665450702557541)
    ·
      refine ⟨42777011866624772006729539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228144063288665450702557541 42777011866624772006729539)
      ·
        refine ⟨64165517799937158010094309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42777011866624772006729539 64165517799937158010094309)
        ·
          refine ⟨12031034587488217126892683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64165517799937158010094309 12031034587488217126892683)
          ·
            refine ⟨18046551881232325690339025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031034587488217126892683 18046551881232325690339025)
            ·
              refine ⟨13534913910924244267754269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046551881232325690339025 13534913910924244267754269)
              ·
                refine ⟨5075592716596591600407851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13534913910924244267754269 5075592716596591600407851)
                ·
                  refine ⟨7613389074894887400611777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075592716596591600407851 7613389074894887400611777)
                  ·
                    refine ⟨5710041806171165550458833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613389074894887400611777 5710041806171165550458833)
                    ·
                      refine ⟨4282531354628374162844125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710041806171165550458833 4282531354628374162844125)
                      ·
                        rfl

theorem cell23_8340200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_8340200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340200 prefixEnd_8340200 := by exact prefixLift 8340200
  have htrace : WordTrace (prefixWord ++ tailWord_8340200) baseStart_8340200 baseEnd_8340200 := by
    simpa [prefixWord, tailWord_8340200, baseEnd_8340200] using wordTrace_append hprefix tailTrace_8340200
  have hstable : (prefixWord ++ tailWord_8340200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340200).length < 2 ^ (prefixWord ++ tailWord_8340200).sum := by decide
  have hdescent : baseEnd_8340200 < baseStart_8340200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340232 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_8340232 : Nat := 118140960795 + 8340232 * 2 ^ 59
def prefixEnd_8340232 : Nat := 4983230072969 + 3 ^ 40 * 8340232 * 2
def baseEnd_8340232 : Nat := 1427515928669772679214659

theorem tailTrace_8340232 : CollatzResearch.WordTrace tailWord_8340232 prefixEnd_8340232 1427515928669772679214659 := by
  unfold tailWord_8340232
  simp only [CollatzResearch.WordTrace]
  refine ⟨152096625760385668534287475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202795501013847558045716633 152096625760385668534287475)
  ·
    refine ⟨228144938640578502801431213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152096625760385668534287475 228144938640578502801431213)
    ·
      refine ⟨85554351990216938550536705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228144938640578502801431213 85554351990216938550536705)
      ·
        refine ⟨64165763992662703912902529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85554351990216938550536705 64165763992662703912902529)
        ·
          refine ⟨48124322994497027934676897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64165763992662703912902529 48124322994497027934676897)
          ·
            refine ⟨36093242245872770951007673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48124322994497027934676897 36093242245872770951007673)
            ·
              refine ⟨27069931684404578213255755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36093242245872770951007673 27069931684404578213255755)
              ·
                refine ⟨40604897526606867319883633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27069931684404578213255755 40604897526606867319883633)
                ·
                  refine ⟨30453673144955150489912725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40604897526606867319883633 30453673144955150489912725)
                  ·
                    refine ⟨1427515928669772679214659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30453673144955150489912725 1427515928669772679214659)
                    ·
                      rfl

theorem cell23_8340232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_8340232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340232 prefixEnd_8340232 := by exact prefixLift 8340232
  have htrace : WordTrace (prefixWord ++ tailWord_8340232) baseStart_8340232 baseEnd_8340232 := by
    simpa [prefixWord, tailWord_8340232, baseEnd_8340232] using wordTrace_append hprefix tailTrace_8340232
  have hstable : (prefixWord ++ tailWord_8340232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340232).length < 2 ^ (prefixWord ++ tailWord_8340232).sum := by decide
  have hdescent : baseEnd_8340232 < baseStart_8340232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
