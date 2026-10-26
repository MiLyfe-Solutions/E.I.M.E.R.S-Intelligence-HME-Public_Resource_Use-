import V185TrunkScan23Chunk1044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6186694 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6186694 : Nat := 118140960795 + 6186694 * 2 ^ 59
def prefixEnd_6186694 : Nat := 4983230072969 + 3 ^ 40 * 6186694 * 2
def baseEnd_6186694 : Nat := 1058915894762374254990973

theorem tailTrace_6186694 : CollatzResearch.WordTrace tailWord_6186694 prefixEnd_6186694 1058915894762374254990973 := by
  unfold tailWord_6186694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051477120270991126869723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150431511899114477373220757 7051477120270991126869723)
  ·
    refine ⟨10577215680406486690304585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051477120270991126869723 10577215680406486690304585)
    ·
      refine ⟨7932911760304865017728439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10577215680406486690304585 7932911760304865017728439)
      ·
        refine ⟨11899367640457297526592659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932911760304865017728439 11899367640457297526592659)
        ·
          refine ⟨17849051460685946289888989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899367640457297526592659 17849051460685946289888989)
          ·
            refine ⟨6693394297757229858708371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17849051460685946289888989 6693394297757229858708371)
            ·
              refine ⟨10040091446635844788062557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693394297757229858708371 10040091446635844788062557)
              ·
                refine ⟨3765034292488441795523459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10040091446635844788062557 3765034292488441795523459)
                ·
                  refine ⟨5647551438732662693285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765034292488441795523459 5647551438732662693285189)
                  ·
                    refine ⟨1058915894762374254990973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5647551438732662693285189 1058915894762374254990973)
                    ·
                      rfl

theorem cell23_6186694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6186694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186694 prefixEnd_6186694 := by exact prefixLift 6186694
  have htrace : WordTrace (prefixWord ++ tailWord_6186694) baseStart_6186694 baseEnd_6186694 := by
    simpa [prefixWord, tailWord_6186694, baseEnd_6186694] using wordTrace_append hprefix tailTrace_6186694
  have hstable : (prefixWord ++ tailWord_6186694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186694).length < 2 ^ (prefixWord ++ tailWord_6186694).sum := by decide
  have hdescent : baseEnd_6186694 < baseStart_6186694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186717 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6186717 : Nat := 118140960795 + 6186717 * 2 ^ 59
def prefixEnd_6186717 : Nat := 4983230072969 + 3 ^ 40 * 6186717 * 2
def baseEnd_6186717 : Nat := 3176759494342176174985313

theorem tailTrace_6186717 : CollatzResearch.WordTrace tailWord_6186717 prefixEnd_6186717 3176759494342176174985313 := by
  unfold tailWord_6186717
  simp only [CollatzResearch.WordTrace]
  refine ⟨225648106727588390987918405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150432071151725593991945603 225648106727588390987918405)
  ·
    refine ⟨42309020011422823310234701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225648106727588390987918405 42309020011422823310234701)
    ·
      refine ⟨15865882504283558741338013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42309020011422823310234701 15865882504283558741338013)
      ·
        refine ⟨5949705939106334528001755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15865882504283558741338013 5949705939106334528001755)
        ·
          refine ⟨8924558908659501792002633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949705939106334528001755 8924558908659501792002633)
          ·
            refine ⟨6693419181494626344001975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8924558908659501792002633 6693419181494626344001975)
            ·
              refine ⟨10040128772241939516002963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693419181494626344001975 10040128772241939516002963)
              ·
                refine ⟨15060193158362909274004445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10040128772241939516002963 15060193158362909274004445)
                ·
                  refine ⟨5647572434386090977751667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15060193158362909274004445 5647572434386090977751667)
                  ·
                    refine ⟨8471358651579136466627501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647572434386090977751667 8471358651579136466627501)
                    ·
                      refine ⟨3176759494342176174985313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471358651579136466627501 3176759494342176174985313)
                      ·
                        rfl

theorem cell23_6186717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6186717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186717 prefixEnd_6186717 := by exact prefixLift 6186717
  have htrace : WordTrace (prefixWord ++ tailWord_6186717) baseStart_6186717 baseEnd_6186717 := by
    simpa [prefixWord, tailWord_6186717, baseEnd_6186717] using wordTrace_append hprefix tailTrace_6186717
  have hstable : (prefixWord ++ tailWord_6186717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186717).length < 2 ^ (prefixWord ++ tailWord_6186717).sum := by decide
  have hdescent : baseEnd_6186717 < baseStart_6186717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186733 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6186733 : Nat := 118140960795 + 6186733 * 2 ^ 59
def prefixEnd_6186733 : Nat := 4983230072969 + 3 ^ 40 * 6186733 * 2
def baseEnd_6186733 : Nat := 1058922570010882704128413

theorem tailTrace_6186733 : CollatzResearch.WordTrace tailWord_6186733 prefixEnd_6186733 1058922570010882704128413 := by
  unfold tailWord_6186733
  simp only [CollatzResearch.WordTrace]
  refine ⟨225648690295530425720500853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150432460197020283813667235 225648690295530425720500853)
  ·
    refine ⟨21154564715205977411296955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225648690295530425720500853 21154564715205977411296955)
    ·
      refine ⟨31731847072808966116945433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154564715205977411296955 31731847072808966116945433)
      ·
        refine ⟨23798885304606724587709075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31731847072808966116945433 23798885304606724587709075)
        ·
          refine ⟨35698327956910086881563613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23798885304606724587709075 35698327956910086881563613)
          ·
            refine ⟨13386872983841282580586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35698327956910086881563613 13386872983841282580586355)
            ·
              refine ⟨20080309475761923870879533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386872983841282580586355 20080309475761923870879533)
              ·
                refine ⟨7530116053410721451579825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20080309475761923870879533 7530116053410721451579825)
                ·
                  refine ⟨5647587040058041088684869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530116053410721451579825 5647587040058041088684869)
                  ·
                    refine ⟨1058922570010882704128413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5647587040058041088684869 1058922570010882704128413)
                    ·
                      rfl

theorem cell23_6186733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6186733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186733 prefixEnd_6186733 := by exact prefixLift 6186733
  have htrace : WordTrace (prefixWord ++ tailWord_6186733) baseStart_6186733 baseEnd_6186733 := by
    simpa [prefixWord, tailWord_6186733, baseEnd_6186733] using wordTrace_append hprefix tailTrace_6186733
  have hstable : (prefixWord ++ tailWord_6186733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186733).length < 2 ^ (prefixWord ++ tailWord_6186733).sum := by decide
  have hdescent : baseEnd_6186733 < baseStart_6186733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186740 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6186740 : Nat := 118140960795 + 6186740 * 2 ^ 59
def prefixEnd_6186740 : Nat := 4983230072969 + 3 ^ 40 * 6186740 * 2
def baseEnd_6186740 : Nat := 3176771304397229584997707

theorem tailTrace_6186740 : CollatzResearch.WordTrace tailWord_6186740 prefixEnd_6186740 3176771304397229584997707 := by
  unfold tailWord_6186740
  simp only [CollatzResearch.WordTrace]
  refine ⟨112824472803252532958002837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150432630404336710610670449 112824472803252532958002837)
  ·
    refine ⟨5288647162652462482406383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112824472803252532958002837 5288647162652462482406383)
    ·
      refine ⟨7932970743978693723609575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288647162652462482406383 7932970743978693723609575)
      ·
        refine ⟨11899456115968040585414363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932970743978693723609575 11899456115968040585414363)
        ·
          refine ⟨17849184173952060878121545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899456115968040585414363 17849184173952060878121545)
          ·
            refine ⟨13386888130464045658591159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17849184173952060878121545 13386888130464045658591159)
            ·
              refine ⟨20080332195696068487886739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386888130464045658591159 20080332195696068487886739)
              ·
                refine ⟨30120498293544102731830109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20080332195696068487886739 30120498293544102731830109)
                ·
                  refine ⟨11295186860079038524436291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30120498293544102731830109 11295186860079038524436291)
                  ·
                    refine ⟨16942780290118557786654437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11295186860079038524436291 16942780290118557786654437)
                    ·
                      refine ⟨3176771304397229584997707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16942780290118557786654437 3176771304397229584997707)
                      ·
                        rfl

theorem cell23_6186740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6186740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186740 prefixEnd_6186740 := by exact prefixLift 6186740
  have htrace : WordTrace (prefixWord ++ tailWord_6186740) baseStart_6186740 baseEnd_6186740 := by
    simpa [prefixWord, tailWord_6186740, baseEnd_6186740] using wordTrace_append hprefix tailTrace_6186740
  have hstable : (prefixWord ++ tailWord_6186740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186740).length < 2 ^ (prefixWord ++ tailWord_6186740).sum := by decide
  have hdescent : baseEnd_6186740 < baseStart_6186740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186756 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6186756 : Nat := 118140960795 + 6186756 * 2 ^ 59
def prefixEnd_6186756 : Nat := 4983230072969 + 3 ^ 40 * 6186756 * 2
def baseEnd_6186756 : Nat := 3176779520087701522397633

theorem tailTrace_6186756 : CollatzResearch.WordTrace tailWord_6186756 prefixEnd_6186756 3176779520087701522397633 := by
  unfold tailWord_6186756
  simp only [CollatzResearch.WordTrace]
  refine ⟨112824764587223550324294061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150433019449631400432392081 112824764587223550324294061)
  ·
    refine ⟨42309286720208831371610273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112824764587223550324294061 42309286720208831371610273)
    ·
      refine ⟨31731965040156623528707705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42309286720208831371610273 31731965040156623528707705)
      ·
        refine ⟨23798973780117467646530779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31731965040156623528707705 23798973780117467646530779)
        ·
          refine ⟨35698460670176201469796169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23798973780117467646530779 35698460670176201469796169)
          ·
            refine ⟨26773845502632151102347127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35698460670176201469796169 26773845502632151102347127)
            ·
              refine ⟨40160768253948226653520691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773845502632151102347127 40160768253948226653520691)
              ·
                refine ⟨60241152380922339980281037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40160768253948226653520691 60241152380922339980281037)
                ·
                  refine ⟨22590432142845877492605389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60241152380922339980281037 22590432142845877492605389)
                  ·
                    refine ⟨8471412053567204059727021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22590432142845877492605389 8471412053567204059727021)
                    ·
                      refine ⟨3176779520087701522397633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471412053567204059727021 3176779520087701522397633)
                      ·
                        rfl

theorem cell23_6186756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6186756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186756 prefixEnd_6186756 := by exact prefixLift 6186756
  have htrace : WordTrace (prefixWord ++ tailWord_6186756) baseStart_6186756 baseEnd_6186756 := by
    simpa [prefixWord, tailWord_6186756, baseEnd_6186756] using wordTrace_append hprefix tailTrace_6186756
  have hstable : (prefixWord ++ tailWord_6186756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186756).length < 2 ^ (prefixWord ++ tailWord_6186756).sum := by decide
  have hdescent : baseEnd_6186756 < baseStart_6186756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186773 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_6186773 : Nat := 118140960795 + 6186773 * 2 ^ 59
def prefixEnd_6186773 : Nat := 4983230072969 + 3 ^ 40 * 6186773 * 2
def baseEnd_6186773 : Nat := 3176788249258827955885055

theorem tailTrace_6186773 : CollatzResearch.WordTrace tailWord_6186773 prefixEnd_6186773 3176788249258827955885055 := by
  unfold tailWord_6186773
  simp only [CollatzResearch.WordTrace]
  refine ⟨225650149215385512551956973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150433432810257008367971315 225650149215385512551956973)
  ·
    refine ⟨84618805955769567206983865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225650149215385512551956973 84618805955769567206983865)
    ·
      refine ⟨63464104466827175405237899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84618805955769567206983865 63464104466827175405237899)
      ·
        refine ⟨95196156700240763107856849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63464104466827175405237899 95196156700240763107856849)
        ·
          refine ⟨71397117525180572330892637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95196156700240763107856849 71397117525180572330892637)
          ·
            refine ⟨26773919071942714624084739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71397117525180572330892637 26773919071942714624084739)
            ·
              refine ⟨40160878607914071936127109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773919071942714624084739 40160878607914071936127109)
              ·
                refine ⟨7530164738983888488023833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40160878607914071936127109 7530164738983888488023833)
                ·
                  refine ⟨5647623554237916366017875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530164738983888488023833 5647623554237916366017875)
                  ·
                    refine ⟨8471435331356874549026813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647623554237916366017875 8471435331356874549026813)
                    ·
                      refine ⟨3176788249258827955885055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471435331356874549026813 3176788249258827955885055)
                      ·
                        rfl

theorem cell23_6186773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_6186773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186773 prefixEnd_6186773 := by exact prefixLift 6186773
  have htrace : WordTrace (prefixWord ++ tailWord_6186773) baseStart_6186773 baseEnd_6186773 := by
    simpa [prefixWord, tailWord_6186773, baseEnd_6186773] using wordTrace_append hprefix tailTrace_6186773
  have hstable : (prefixWord ++ tailWord_6186773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186773).length < 2 ^ (prefixWord ++ tailWord_6186773).sum := by decide
  have hdescent : baseEnd_6186773 < baseStart_6186773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186789 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_6186789 : Nat := 118140960795 + 6186789 * 2 ^ 59
def prefixEnd_6186789 : Nat := 4983230072969 + 3 ^ 40 * 6186789 * 2
def baseEnd_6186789 : Nat := 1058932154983099964428327

theorem tailTrace_6186789 : CollatzResearch.WordTrace tailWord_6186789 prefixEnd_6186789 1058932154983099964428327 := by
  unfold tailWord_6186789
  simp only [CollatzResearch.WordTrace]
  refine ⟨225650732783327547284539421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150433821855551698189692947 225650732783327547284539421)
  ·
    refine ⟨84619024793747830231702283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225650732783327547284539421 84619024793747830231702283)
    ·
      refine ⟨126928537190621745347553425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84619024793747830231702283 126928537190621745347553425)
      ·
        refine ⟨95196402892966309010665069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126928537190621745347553425 95196402892966309010665069)
        ·
          refine ⟨35698651084862365878999401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95196402892966309010665069 35698651084862365878999401)
          ·
            refine ⟨26773988313646774409249551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35698651084862365878999401 26773988313646774409249551)
            ·
              refine ⟨40160982470470161613874327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773988313646774409249551 40160982470470161613874327)
              ·
                refine ⟨60241473705705242420811491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40160982470470161613874327 60241473705705242420811491)
                ·
                  refine ⟨90362210558557863631217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60241473705705242420811491 90362210558557863631217237)
                  ·
                    refine ⟨1058932154983099964428327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90362210558557863631217237 1058932154983099964428327)
                    ·
                      rfl

theorem cell23_6186789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_6186789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186789 prefixEnd_6186789 := by exact prefixLift 6186789
  have htrace : WordTrace (prefixWord ++ tailWord_6186789) baseStart_6186789 baseEnd_6186789 := by
    simpa [prefixWord, tailWord_6186789, baseEnd_6186789] using wordTrace_append hprefix tailTrace_6186789
  have hstable : (prefixWord ++ tailWord_6186789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186789).length < 2 ^ (prefixWord ++ tailWord_6186789).sum := by decide
  have hdescent : baseEnd_6186789 < baseStart_6186789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186836 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 7]
def baseStart_6186836 : Nat := 118140960795 + 6186836 * 2 ^ 59
def prefixEnd_6186836 : Nat := 4983230072969 + 3 ^ 40 * 6186836 * 2
def baseEnd_6186836 : Nat := 352980066504451245488585

theorem tailTrace_6186836 : CollatzResearch.WordTrace tailWord_6186836 prefixEnd_6186836 352980066504451245488585 := by
  unfold tailWord_6186836
  simp only [CollatzResearch.WordTrace]
  refine ⟨112826223507078637155750181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150434964676104849541000241 112826223507078637155750181)
  ·
    refine ⟨21154916907577244466703159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112826223507078637155750181 21154916907577244466703159)
    ·
      refine ⟨31732375361365866700054739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154916907577244466703159 31732375361365866700054739)
      ·
        refine ⟨47598563042048800050082109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31732375361365866700054739 47598563042048800050082109)
        ·
          refine ⟨17849461140768300018780791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47598563042048800050082109 17849461140768300018780791)
          ·
            refine ⟨26774191711152450028171187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849461140768300018780791 26774191711152450028171187)
            ·
              refine ⟨40161287566728675042256781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26774191711152450028171187 40161287566728675042256781)
              ·
                refine ⟨15060482837523253140846293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40161287566728675042256781 15060482837523253140846293)
                ·
                  refine ⟨352980066504451245488585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15060482837523253140846293 352980066504451245488585)
                  ·
                    rfl

theorem cell23_6186836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_6186836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186836 prefixEnd_6186836 := by exact prefixLift 6186836
  have htrace : WordTrace (prefixWord ++ tailWord_6186836) baseStart_6186836 baseEnd_6186836 := by
    simpa [prefixWord, tailWord_6186836, baseEnd_6186836] using wordTrace_append hprefix tailTrace_6186836
  have hstable : (prefixWord ++ tailWord_6186836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186836).length < 2 ^ (prefixWord ++ tailWord_6186836).sum := by decide
  have hdescent : baseEnd_6186836 < baseStart_6186836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186847 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 2, 2, 2]
def baseStart_6186847 : Nat := 118140960795 + 6186847 * 2 ^ 59
def prefixEnd_6186847 : Nat := 4983230072969 + 3 ^ 40 * 6186847 * 2
def baseEnd_6186847 : Nat := 3176826246827260666359715

theorem tailTrace_6186847 : CollatzResearch.WordTrace tailWord_6186847 prefixEnd_6186847 3176826246827260666359715 := by
  unfold tailWord_6186847
  simp only [CollatzResearch.WordTrace]
  refine ⟨225652848217117423190150795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150435232144744948793433863 225652848217117423190150795)
  ·
    refine ⟨338479272325676134785226193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225652848217117423190150795 338479272325676134785226193)
    ·
      refine ⟨253859454244257101088919645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338479272325676134785226193 253859454244257101088919645)
      ·
        refine ⟨95197295341596412908344867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253859454244257101088919645 95197295341596412908344867)
        ·
          refine ⟨142795943012394619362517301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95197295341596412908344867 142795943012394619362517301)
          ·
            refine ⟨13387119657411995565235997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142795943012394619362517301 13387119657411995565235997)
            ·
              refine ⟨5020169871529498336963499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13387119657411995565235997 5020169871529498336963499)
              ·
                refine ⟨7530254807294247505445249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020169871529498336963499 7530254807294247505445249)
                ·
                  refine ⟨5647691105470685629083937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530254807294247505445249 5647691105470685629083937)
                  ·
                    refine ⟨4235768329103014221812953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5647691105470685629083937 4235768329103014221812953)
                    ·
                      refine ⟨3176826246827260666359715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235768329103014221812953 3176826246827260666359715)
                      ·
                        rfl

theorem cell23_6186847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_6186847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186847 prefixEnd_6186847 := by exact prefixLift 6186847
  have htrace : WordTrace (prefixWord ++ tailWord_6186847) baseStart_6186847 baseEnd_6186847 := by
    simpa [prefixWord, tailWord_6186847, baseEnd_6186847] using wordTrace_append hprefix tailTrace_6186847
  have hstable : (prefixWord ++ tailWord_6186847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186847).length < 2 ^ (prefixWord ++ tailWord_6186847).sum := by decide
  have hdescent : baseEnd_6186847 < baseStart_6186847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186849 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6186849 : Nat := 118140960795 + 6186849 * 2 ^ 59
def prefixEnd_6186849 : Nat := 4983230072969 + 3 ^ 40 * 6186849 * 2
def baseEnd_6186849 : Nat := 1058942424596189886178235

theorem tailTrace_6186849 : CollatzResearch.WordTrace tailWord_6186849 prefixEnd_6186849 1058942424596189886178235 := by
  unfold tailWord_6186849
  simp only [CollatzResearch.WordTrace]
  refine ⟨225652921163110177531723601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150435280775406785021149067 225652921163110177531723601)
  ·
    refine ⟨169239690872332633148792701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225652921163110177531723601 169239690872332633148792701)
    ·
      refine ⟨63464884077124737430797263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169239690872332633148792701 63464884077124737430797263)
      ·
        refine ⟨95197326115687106146195895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63464884077124737430797263 95197326115687106146195895)
        ·
          refine ⟨142795989173530659219293843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95197326115687106146195895 142795989173530659219293843)
          ·
            refine ⟨214193983760295988828940765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142795989173530659219293843 214193983760295988828940765)
            ·
              refine ⟨80322743910110995810852787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214193983760295988828940765 80322743910110995810852787)
              ·
                refine ⟨120484115865166493716279181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80322743910110995810852787 120484115865166493716279181)
                ·
                  refine ⟨45181543449437435143604693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120484115865166493716279181 45181543449437435143604693)
                  ·
                    refine ⟨1058942424596189886178235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45181543449437435143604693 1058942424596189886178235)
                    ·
                      rfl

theorem cell23_6186849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6186849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186849 prefixEnd_6186849 := by exact prefixLift 6186849
  have htrace : WordTrace (prefixWord ++ tailWord_6186849) baseStart_6186849 baseEnd_6186849 := by
    simpa [prefixWord, tailWord_6186849, baseEnd_6186849] using wordTrace_append hprefix tailTrace_6186849
  have hstable : (prefixWord ++ tailWord_6186849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186849).length < 2 ^ (prefixWord ++ tailWord_6186849).sum := by decide
  have hdescent : baseEnd_6186849 < baseStart_6186849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186859 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_6186859 : Nat := 118140960795 + 6186859 * 2 ^ 59
def prefixEnd_6186859 : Nat := 4983230072969 + 3 ^ 40 * 6186859 * 2
def baseEnd_6186859 : Nat := 3176832408595114619409659

theorem tailTrace_6186859 : CollatzResearch.WordTrace tailWord_6186859 prefixEnd_6186859 3176832408595114619409659 := by
  unfold tailWord_6186859
  simp only [CollatzResearch.WordTrace]
  refine ⟨225653285893073949239587631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150435523928715966159725087 225653285893073949239587631)
  ·
    refine ⟨338479928839610923859381447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225653285893073949239587631 338479928839610923859381447)
    ·
      refine ⟨507719893259416385789072171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338479928839610923859381447 507719893259416385789072171)
      ·
        refine ⟨761579839889124578683608257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507719893259416385789072171 761579839889124578683608257)
        ·
          refine ⟨571184879916843434012706193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761579839889124578683608257 571184879916843434012706193)
          ·
            refine ⟨428388659937632575509529645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571184879916843434012706193 428388659937632575509529645)
            ·
              refine ⟨160645747476612215816073617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428388659937632575509529645 160645747476612215816073617)
              ·
                refine ⟨120484310607459161862055213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160645747476612215816073617 120484310607459161862055213)
                ·
                  refine ⟨45181616477797185698270705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120484310607459161862055213 45181616477797185698270705)
                  ·
                    refine ⟨33886212358347889273703029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45181616477797185698270705 33886212358347889273703029)
                    ·
                      refine ⟨3176832408595114619409659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33886212358347889273703029 3176832408595114619409659)
                      ·
                        rfl

theorem cell23_6186859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_6186859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186859 prefixEnd_6186859 := by exact prefixLift 6186859
  have htrace : WordTrace (prefixWord ++ tailWord_6186859) baseStart_6186859 baseEnd_6186859 := by
    simpa [prefixWord, tailWord_6186859, baseEnd_6186859] using wordTrace_append hprefix tailTrace_6186859
  have hstable : (prefixWord ++ tailWord_6186859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186859).length < 2 ^ (prefixWord ++ tailWord_6186859).sum := by decide
  have hdescent : baseEnd_6186859 < baseStart_6186859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186866 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_6186866 : Nat := 118140960795 + 6186866 * 2 ^ 59
def prefixEnd_6186866 : Nat := 4983230072969 + 3 ^ 40 * 6186866 * 2
def baseEnd_6186866 : Nat := 1058945334319898697340709

theorem tailTrace_6186866 : CollatzResearch.WordTrace tailWord_6186866 prefixEnd_6186866 1058945334319898697340709 := by
  unfold tailWord_6186866
  simp only [CollatzResearch.WordTrace]
  refine ⟨56413385301012147358773113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150435694136032392956728301 56413385301012147358773113)
  ·
    refine ⟨42310038975759110519079835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56413385301012147358773113 42310038975759110519079835)
    ·
      refine ⟨63465058463638665778619753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42310038975759110519079835 63465058463638665778619753)
      ·
        refine ⟨47598793847728999333964815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63465058463638665778619753 47598793847728999333964815)
        ·
          refine ⟨71398190771593499000947223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47598793847728999333964815 71398190771593499000947223)
          ·
            refine ⟨107097286157390248501420835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71398190771593499000947223 107097286157390248501420835)
            ·
              refine ⟨160645929236085372752131253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107097286157390248501420835 160645929236085372752131253)
              ·
                refine ⟨15060555865883003695512305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160645929236085372752131253 15060555865883003695512305)
                ·
                  refine ⟨11295416899412252771634229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15060555865883003695512305 11295416899412252771634229)
                  ·
                    refine ⟨1058945334319898697340709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11295416899412252771634229 1058945334319898697340709)
                    ·
                      rfl

theorem cell23_6186866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_6186866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186866 prefixEnd_6186866 := by exact prefixLift 6186866
  have htrace : WordTrace (prefixWord ++ tailWord_6186866) baseStart_6186866 baseEnd_6186866 := by
    simpa [prefixWord, tailWord_6186866, baseEnd_6186866] using wordTrace_append hprefix tailTrace_6186866
  have hstable : (prefixWord ++ tailWord_6186866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186866).length < 2 ^ (prefixWord ++ tailWord_6186866).sum := by decide
  have hdescent : baseEnd_6186866 < baseStart_6186866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_6186899 : Nat := 118140960795 + 6186899 * 2 ^ 59
def prefixEnd_6186899 : Nat := 4983230072969 + 3 ^ 40 * 6186899 * 2
def baseEnd_6186899 : Nat := 3176852947821294462909475

theorem tailTrace_6186899 : CollatzResearch.WordTrace tailWord_6186899 prefixEnd_6186899 3176852947821294462909475 := by
  unfold tailWord_6186899
  simp only [CollatzResearch.WordTrace]
  refine ⟨225654744812929036071043751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150436496541952690714029167 225654744812929036071043751)
  ·
    refine ⟨338482117219393554106565627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225654744812929036071043751 338482117219393554106565627)
    ·
      refine ⟨507723175829090331159848441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338482117219393554106565627 507723175829090331159848441)
      ·
        refine ⟨380792381871817748369886331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507723175829090331159848441 380792381871817748369886331)
        ·
          refine ⟨571188572807726622554829497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380792381871817748369886331 571188572807726622554829497)
          ·
            refine ⟨428391429605794966916122123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571188572807726622554829497 428391429605794966916122123)
            ·
              refine ⟨642587144408692450374183185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428391429605794966916122123 642587144408692450374183185)
              ·
                refine ⟨481940358306519337780637389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642587144408692450374183185 481940358306519337780637389)
                ·
                  refine ⟨180727634364944751667739021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481940358306519337780637389 180727634364944751667739021)
                  ·
                    refine ⟨67772862886854281875402133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180727634364944751667739021 67772862886854281875402133)
                    ·
                      refine ⟨3176852947821294462909475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67772862886854281875402133 3176852947821294462909475)
                      ·
                        rfl

theorem cell23_6186899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_6186899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186899 prefixEnd_6186899 := by exact prefixLift 6186899
  have htrace : WordTrace (prefixWord ++ tailWord_6186899) baseStart_6186899 baseEnd_6186899 := by
    simpa [prefixWord, tailWord_6186899, baseEnd_6186899] using wordTrace_append hprefix tailTrace_6186899
  have hstable : (prefixWord ++ tailWord_6186899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186899).length < 2 ^ (prefixWord ++ tailWord_6186899).sum := by decide
  have hdescent : baseEnd_6186899 < baseStart_6186899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186990 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6186990 : Nat := 118140960795 + 6186990 * 2 ^ 59
def prefixEnd_6186990 : Nat := 4983230072969 + 3 ^ 40 * 6186990 * 2
def baseEnd_6186990 : Nat := 1058966558186951202290519

theorem tailTrace_6186990 : CollatzResearch.WordTrace tailWord_6186990 prefixEnd_6186990 1058966558186951202290519 := by
  unfold tailWord_6186990
  simp only [CollatzResearch.WordTrace]
  refine ⟨28207257981949919826575803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150438709237066239075070949 28207257981949919826575803)
  ·
    refine ⟨42310886972924879739863705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28207257981949919826575803 42310886972924879739863705)
    ·
      refine ⟨31733165229693659804897779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42310886972924879739863705 31733165229693659804897779)
      ·
        refine ⟨47599747844540489707346669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31733165229693659804897779 47599747844540489707346669)
        ·
          refine ⟨17849905441702683640255001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47599747844540489707346669 17849905441702683640255001)
          ·
            refine ⟨13387429081277012730191251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17849905441702683640255001 13387429081277012730191251)
            ·
              refine ⟨20081143621915519095286877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13387429081277012730191251 20081143621915519095286877)
              ·
                refine ⟨7530428858218319660732579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20081143621915519095286877 7530428858218319660732579)
                ·
                  refine ⟨11295643287327479491098869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7530428858218319660732579 11295643287327479491098869)
                  ·
                    refine ⟨1058966558186951202290519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11295643287327479491098869 1058966558186951202290519)
                    ·
                      rfl

theorem cell23_6186990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6186990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186990 prefixEnd_6186990 := by exact prefixLift 6186990
  have htrace : WordTrace (prefixWord ++ tailWord_6186990) baseStart_6186990 baseEnd_6186990 := by
    simpa [prefixWord, tailWord_6186990, baseEnd_6186990] using wordTrace_append hprefix tailTrace_6186990
  have hstable : (prefixWord ++ tailWord_6186990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186990).length < 2 ^ (prefixWord ++ tailWord_6186990).sum := by decide
  have hdescent : baseEnd_6186990 < baseStart_6186990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187013 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_6187013 : Nat := 118140960795 + 6187013 * 2 ^ 59
def prefixEnd_6187013 : Nat := 4983230072969 + 3 ^ 40 * 6187013 * 2
def baseEnd_6187013 : Nat := 3176911484615907016883951

theorem tailTrace_6187013 : CollatzResearch.WordTrace tailWord_6187013 prefixEnd_6187013 3176911484615907016883951 := by
  unfold tailWord_6187013
  simp only [CollatzResearch.WordTrace]
  refine ⟨225658902734516033540693693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150439268489677355693795795 225658902734516033540693693)
  ·
    refine ⟨84622088525443512577760135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225658902734516033540693693 84622088525443512577760135)
    ·
      refine ⟨126933132788165268866640203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84622088525443512577760135 126933132788165268866640203)
      ·
        refine ⟨190399699182247903299960305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126933132788165268866640203 190399699182247903299960305)
        ·
          refine ⟨142799774386685927474970229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190399699182247903299960305 142799774386685927474970229)
          ·
            refine ⟨13387478848751805700778459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142799774386685927474970229 13387478848751805700778459)
            ·
              refine ⟨20081218273127708551167689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13387478848751805700778459 20081218273127708551167689)
              ·
                refine ⟨15060913704845781413375767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20081218273127708551167689 15060913704845781413375767)
                ·
                  refine ⟨22591370557268672120063651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15060913704845781413375767 22591370557268672120063651)
                  ·
                    refine ⟨33887055835903008180095477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22591370557268672120063651 33887055835903008180095477)
                    ·
                      refine ⟨3176911484615907016883951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33887055835903008180095477 3176911484615907016883951)
                      ·
                        rfl

theorem cell23_6187013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_6187013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187013 prefixEnd_6187013 := by exact prefixLift 6187013
  have htrace : WordTrace (prefixWord ++ tailWord_6187013) baseStart_6187013 baseEnd_6187013 := by
    simpa [prefixWord, tailWord_6187013, baseEnd_6187013] using wordTrace_append hprefix tailTrace_6187013
  have hstable : (prefixWord ++ tailWord_6187013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187013).length < 2 ^ (prefixWord ++ tailWord_6187013).sum := by decide
  have hdescent : baseEnd_6187013 < baseStart_6187013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187016 : List Nat := [2, 1, 3, 2, 1, 2, 2, 10]
def baseStart_6187016 : Nat := 118140960795 + 6187016 * 2 ^ 59
def prefixEnd_6187016 : Nat := 4983230072969 + 3 ^ 40 * 6187016 * 2
def baseEnd_6187016 : Nat := 117663445372513722412831

theorem tailTrace_6187016 : CollatzResearch.WordTrace tailWord_6187016 prefixEnd_6187016 117663445372513722412831 := by
  unfold tailWord_6187016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112829506076752582526526451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150439341435670110035368601 112829506076752582526526451)
  ·
    refine ⟨169244259115128873789789677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112829506076752582526526451 169244259115128873789789677)
    ·
      refine ⟨63466597168173327671171129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169244259115128873789789677 63466597168173327671171129)
      ·
        refine ⟨47599947876129995753378347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63466597168173327671171129 47599947876129995753378347)
        ·
          refine ⟨71399921814194993630067521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47599947876129995753378347 71399921814194993630067521)
          ·
            refine ⟨53549941360646245222550641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71399921814194993630067521 53549941360646245222550641)
            ·
              refine ⟨40162456020484683916912981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53549941360646245222550641 40162456020484683916912981)
              ·
                refine ⟨117663445372513722412831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40162456020484683916912981 117663445372513722412831)
                ·
                  rfl

theorem cell23_6187016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 10].length) (baseStart_6187016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187016 prefixEnd_6187016 := by exact prefixLift 6187016
  have htrace : WordTrace (prefixWord ++ tailWord_6187016) baseStart_6187016 baseEnd_6187016 := by
    simpa [prefixWord, tailWord_6187016, baseEnd_6187016] using wordTrace_append hprefix tailTrace_6187016
  have hstable : (prefixWord ++ tailWord_6187016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187016).length < 2 ^ (prefixWord ++ tailWord_6187016).sum := by decide
  have hdescent : baseEnd_6187016 < baseStart_6187016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187043 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3]
def baseStart_6187043 : Nat := 118140960795 + 6187043 * 2 ^ 59
def prefixEnd_6187043 : Nat := 4983230072969 + 3 ^ 40 * 6187043 * 2
def baseEnd_6187043 : Nat := 3176926889035541899508813

theorem tailTrace_6187043 : CollatzResearch.WordTrace tailWord_6187043 prefixEnd_6187043 3176926889035541899508813 := by
  unfold tailWord_6187043
  simp only [CollatzResearch.WordTrace]
  refine ⟨225659996924407348664285783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150439997949604899109523855 225659996924407348664285783)
  ·
    refine ⟨338489995386611022996428675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225659996924407348664285783 338489995386611022996428675)
    ·
      refine ⟨507734993079916534494643013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338489995386611022996428675 507734993079916534494643013)
      ·
        refine ⟨95200311202484350217745565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 507734993079916534494643013 95200311202484350217745565)
        ·
          refine ⟨35700116700931631331654587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95200311202484350217745565 35700116700931631331654587)
          ·
            refine ⟨53550175051397446997481881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35700116700931631331654587 53550175051397446997481881)
            ·
              refine ⟨40162631288548085248111411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53550175051397446997481881 40162631288548085248111411)
              ·
                refine ⟨60243946932822127872167117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40162631288548085248111411 60243946932822127872167117)
                ·
                  refine ⟨22591480099808297952062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60243946932822127872167117 22591480099808297952062669)
                  ·
                    refine ⟨8471805037428111732023501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22591480099808297952062669 8471805037428111732023501)
                    ·
                      refine ⟨3176926889035541899508813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471805037428111732023501 3176926889035541899508813)
                      ·
                        rfl

theorem cell23_6187043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_6187043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187043 prefixEnd_6187043 := by exact prefixLift 6187043
  have htrace : WordTrace (prefixWord ++ tailWord_6187043) baseStart_6187043 baseEnd_6187043 := by
    simpa [prefixWord, tailWord_6187043, baseEnd_6187043] using wordTrace_append hprefix tailTrace_6187043
  have hstable : (prefixWord ++ tailWord_6187043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187043).length < 2 ^ (prefixWord ++ tailWord_6187043).sum := by decide
  have hdescent : baseEnd_6187043 < baseStart_6187043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187047 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6187047 : Nat := 118140960795 + 6187047 * 2 ^ 59
def prefixEnd_6187047 : Nat := 4983230072969 + 3 ^ 40 * 6187047 * 2
def baseEnd_6187047 : Nat := 3176928942958159883858795

theorem tailTrace_6187047 : CollatzResearch.WordTrace tailWord_6187047 prefixEnd_6187047 3176928942958159883858795 := by
  unfold tailWord_6187047
  simp only [CollatzResearch.WordTrace]
  refine ⟨225660142816392857347431395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150440095210928571564954263 225660142816392857347431395)
  ·
    refine ⟨338490214224589286021147093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225660142816392857347431395 338490214224589286021147093)
    ·
      refine ⟨7933364395888811391120635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 338490214224589286021147093 7933364395888811391120635)
      ·
        refine ⟨11900046593833217086680953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933364395888811391120635 11900046593833217086680953)
        ·
          refine ⟨8925034945374912815010715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11900046593833217086680953 8925034945374912815010715)
          ·
            refine ⟨13387552418062369222516073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925034945374912815010715 13387552418062369222516073)
            ·
              refine ⟨10040664313546776916887055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13387552418062369222516073 10040664313546776916887055)
              ·
                refine ⟨15060996470320165375330583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10040664313546776916887055 15060996470320165375330583)
                ·
                  refine ⟨22591494705480248062995875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15060996470320165375330583 22591494705480248062995875)
                  ·
                    refine ⟨33887242058220372094493813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22591494705480248062995875 33887242058220372094493813)
                    ·
                      refine ⟨3176928942958159883858795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33887242058220372094493813 3176928942958159883858795)
                      ·
                        rfl

theorem cell23_6187047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6187047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187047 prefixEnd_6187047 := by exact prefixLift 6187047
  have htrace : WordTrace (prefixWord ++ tailWord_6187047) baseStart_6187047 baseEnd_6187047 := by
    simpa [prefixWord, tailWord_6187047, baseEnd_6187047] using wordTrace_append hprefix tailTrace_6187047
  have hstable : (prefixWord ++ tailWord_6187047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187047).length < 2 ^ (prefixWord ++ tailWord_6187047).sum := by decide
  have hdescent : baseEnd_6187047 < baseStart_6187047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187094 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6187094 : Nat := 118140960795 + 6187094 * 2 ^ 59
def prefixEnd_6187094 : Nat := 4983230072969 + 3 ^ 40 * 6187094 * 2
def baseEnd_6187094 : Nat := 3176953076548921199971079

theorem tailTrace_6187094 : CollatzResearch.WordTrace tailWord_6187094 prefixEnd_6187094 3176953076548921199971079 := by
  unfold tailWord_6187094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103866065451411523399521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150441238031481722916261557 14103866065451411523399521)
  ·
    refine ⟨10577899549088558642549641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14103866065451411523399521 10577899549088558642549641)
    ·
      refine ⟨7933424661816418981912231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10577899549088558642549641 7933424661816418981912231)
      ·
        refine ⟨11900136992724628472868347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933424661816418981912231 11900136992724628472868347)
        ·
          refine ⟨17850205489086942709302521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11900136992724628472868347 17850205489086942709302521)
          ·
            refine ⟨13387654116815207031976891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17850205489086942709302521 13387654116815207031976891)
            ·
              refine ⟨20081481175222810547965337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13387654116815207031976891 20081481175222810547965337)
              ·
                refine ⟨15061110881417107910974003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20081481175222810547965337 15061110881417107910974003)
                ·
                  refine ⟨22591666322125661866461005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15061110881417107910974003 22591666322125661866461005)
                  ·
                    refine ⟨8471874870797123199922877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22591666322125661866461005 8471874870797123199922877)
                    ·
                      refine ⟨3176953076548921199971079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471874870797123199922877 3176953076548921199971079)
                      ·
                        rfl

theorem cell23_6187094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6187094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187094 prefixEnd_6187094 := by exact prefixLift 6187094
  have htrace : WordTrace (prefixWord ++ tailWord_6187094) baseStart_6187094 baseEnd_6187094 := by
    simpa [prefixWord, tailWord_6187094, baseEnd_6187094] using wordTrace_append hprefix tailTrace_6187094
  have hstable : (prefixWord ++ tailWord_6187094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187094).length < 2 ^ (prefixWord ++ tailWord_6187094).sum := by decide
  have hdescent : baseEnd_6187094 < baseStart_6187094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187104 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2]
def baseStart_6187104 : Nat := 118140960795 + 6187104 * 2 ^ 59
def prefixEnd_6187104 : Nat := 4983230072969 + 3 ^ 40 * 6187104 * 2
def baseEnd_6187104 : Nat := 3176958211355466160846033

theorem tailTrace_6187104 : CollatzResearch.WordTrace tailWord_6187104 prefixEnd_6187104 3176958211355466160846033 := by
  unfold tailWord_6187104
  simp only [CollatzResearch.WordTrace]
  refine ⟨112831110888593178041128183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150441481184790904054837577 112831110888593178041128183)
  ·
    refine ⟨169246666332889767061692275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112831110888593178041128183 169246666332889767061692275)
    ·
      refine ⟨253869999499334650592538413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169246666332889767061692275 253869999499334650592538413)
      ·
        refine ⟨95201249812250493972201905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253869999499334650592538413 95201249812250493972201905)
        ·
          refine ⟨71400937359187870479151429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95201249812250493972201905 71400937359187870479151429)
          ·
            refine ⟨13387675754847725714840893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71400937359187870479151429 13387675754847725714840893)
            ·
              refine ⟨5020378408067897143065335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13387675754847725714840893 5020378408067897143065335)
              ·
                refine ⟨7530567612101845714598003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020378408067897143065335 7530567612101845714598003)
                ·
                  refine ⟨11295851418152768571897005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7530567612101845714598003 11295851418152768571897005)
                  ·
                    refine ⟨4235944281807288214461377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11295851418152768571897005 4235944281807288214461377)
                    ·
                      refine ⟨3176958211355466160846033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235944281807288214461377 3176958211355466160846033)
                      ·
                        rfl

theorem cell23_6187104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_6187104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187104 prefixEnd_6187104 := by exact prefixLift 6187104
  have htrace : WordTrace (prefixWord ++ tailWord_6187104) baseStart_6187104 baseEnd_6187104 := by
    simpa [prefixWord, tailWord_6187104, baseEnd_6187104] using wordTrace_append hprefix tailTrace_6187104
  have hstable : (prefixWord ++ tailWord_6187104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187104).length < 2 ^ (prefixWord ++ tailWord_6187104).sum := by decide
  have hdescent : baseEnd_6187104 < baseStart_6187104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187113 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_6187113 : Nat := 118140960795 + 6187113 * 2 ^ 59
def prefixEnd_6187113 : Nat := 4983230072969 + 3 ^ 40 * 6187113 * 2
def baseEnd_6187113 : Nat := 3176962832681356625633491

theorem tailTrace_6187113 : CollatzResearch.WordTrace tailWord_6187113 prefixEnd_6187113 3176962832681356625633491 := by
  unfold tailWord_6187113
  simp only [CollatzResearch.WordTrace]
  refine ⟨225662550034153750619333993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150441700022769167079555995 225662550034153750619333993)
  ·
    refine ⟨169246912525615312964500495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225662550034153750619333993 169246912525615312964500495)
    ·
      refine ⟨253870368788422969446750743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169246912525615312964500495 253870368788422969446750743)
      ·
        refine ⟨380805553182634454170126115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253870368788422969446750743 380805553182634454170126115)
        ·
          refine ⟨571208329773951681255189173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380805553182634454170126115 571208329773951681255189173)
          ·
            refine ⟨53550780916307970117673985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 571208329773951681255189173 53550780916307970117673985)
            ·
              refine ⟨40163085687230977588255489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53550780916307970117673985 40163085687230977588255489)
              ·
                refine ⟨30122314265423233191191617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40163085687230977588255489 30122314265423233191191617)
                ·
                  refine ⟨22591735699067424893393713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30122314265423233191191617 22591735699067424893393713)
                  ·
                    refine ⟨16943801774300568670045285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22591735699067424893393713 16943801774300568670045285)
                    ·
                      refine ⟨3176962832681356625633491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16943801774300568670045285 3176962832681356625633491)
                      ·
                        rfl

theorem cell23_6187113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_6187113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187113 prefixEnd_6187113 := by exact prefixLift 6187113
  have htrace : WordTrace (prefixWord ++ tailWord_6187113) baseStart_6187113 baseEnd_6187113 := by
    simpa [prefixWord, tailWord_6187113, baseEnd_6187113] using wordTrace_append hprefix tailTrace_6187113
  have hstable : (prefixWord ++ tailWord_6187113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187113).length < 2 ^ (prefixWord ++ tailWord_6187113).sum := by decide
  have hdescent : baseEnd_6187113 < baseStart_6187113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187210 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_6187210 : Nat := 118140960795 + 6187210 * 2 ^ 59
def prefixEnd_6187210 : Nat := 4983230072969 + 3 ^ 40 * 6187210 * 2
def baseEnd_6187210 : Nat := 3177012640304842746120545

theorem tailTrace_6187210 : CollatzResearch.WordTrace tailWord_6187210 prefixEnd_6187210 3177012640304842746120545 := by
  unfold tailWord_6187210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56416521978700584046403771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150444058609868224123743389 56416521978700584046403771)
  ·
    refine ⟨84624782968050876069605657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56416521978700584046403771 84624782968050876069605657)
    ·
      refine ⟨63468587226038157052204243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84624782968050876069605657 63468587226038157052204243)
      ·
        refine ⟨95202880839057235578306365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63468587226038157052204243 95202880839057235578306365)
        ·
          refine ⟨35701080314646463341864887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95202880839057235578306365 35701080314646463341864887)
          ·
            refine ⟨53551620471969695012797331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35701080314646463341864887 53551620471969695012797331)
            ·
              refine ⟨80327430707954542519195997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53551620471969695012797331 80327430707954542519195997)
              ·
                refine ⟨30122786515482953444698499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80327430707954542519195997 30122786515482953444698499)
                ·
                  refine ⟨45184179773224430167047749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30122786515482953444698499 45184179773224430167047749)
                  ·
                    refine ⟨8472033707479580656321453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45184179773224430167047749 8472033707479580656321453)
                    ·
                      refine ⟨3177012640304842746120545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472033707479580656321453 3177012640304842746120545)
                      ·
                        rfl

theorem cell23_6187210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_6187210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187210 prefixEnd_6187210 := by exact prefixLift 6187210
  have htrace : WordTrace (prefixWord ++ tailWord_6187210) baseStart_6187210 baseEnd_6187210 := by
    simpa [prefixWord, tailWord_6187210, baseEnd_6187210] using wordTrace_append hprefix tailTrace_6187210
  have hstable : (prefixWord ++ tailWord_6187210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187210).length < 2 ^ (prefixWord ++ tailWord_6187210).sum := by decide
  have hdescent : baseEnd_6187210 < baseStart_6187210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187247 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 6]
def baseStart_6187247 : Nat := 118140960795 + 6187247 * 2 ^ 59
def prefixEnd_6187247 : Nat := 4983230072969 + 3 ^ 40 * 6187247 * 2
def baseEnd_6187247 : Nat := 353003515454339900150875

theorem tailTrace_6187247 : CollatzResearch.WordTrace tailWord_6187247 prefixEnd_6187247 353003515454339900150875 := by
  unfold tailWord_6187247
  simp only [CollatzResearch.WordTrace]
  refine ⟨225667437415668291504711995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150444958277112194336474663 225667437415668291504711995)
  ·
    refine ⟨338501156123502437257067993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225667437415668291504711995 338501156123502437257067993)
    ·
      refine ⟨253875867092626827942800995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338501156123502437257067993 253875867092626827942800995)
      ·
        refine ⟨380813800638940241914201493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253875867092626827942800995 380813800638940241914201493)
        ·
          refine ⟨17850646904950323839728195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380813800638940241914201493 17850646904950323839728195)
          ·
            refine ⟨26775970357425485759592293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17850646904950323839728195 26775970357425485759592293)
            ·
              refine ⟨5020494442017278579923555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26775970357425485759592293 5020494442017278579923555)
              ·
                refine ⟨7530741663025917869885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020494442017278579923555 7530741663025917869885333)
                ·
                  refine ⟨353003515454339900150875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7530741663025917869885333 353003515454339900150875)
                  ·
                    rfl

theorem cell23_6187247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 6].length) (baseStart_6187247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187247 prefixEnd_6187247 := by exact prefixLift 6187247
  have htrace : WordTrace (prefixWord ++ tailWord_6187247) baseStart_6187247 baseEnd_6187247 := by
    simpa [prefixWord, tailWord_6187247, baseEnd_6187247] using wordTrace_append hprefix tailTrace_6187247
  have hstable : (prefixWord ++ tailWord_6187247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187247).length < 2 ^ (prefixWord ++ tailWord_6187247).sum := by decide
  have hdescent : baseEnd_6187247 < baseStart_6187247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187291 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 1, 1, 3]
def baseStart_6187291 : Nat := 118140960795 + 6187291 * 2 ^ 59
def prefixEnd_6187291 : Nat := 4983230072969 + 3 ^ 40 * 6187291 * 2
def baseEnd_6187291 : Nat := 3177054232237856929207673

theorem tailTrace_6187291 : CollatzResearch.WordTrace tailWord_6187291 prefixEnd_6187291 3177054232237856929207673 := by
  unfold tailWord_6187291
  simp only [CollatzResearch.WordTrace]
  refine ⟨225669042227508887019313727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150446028151672591346209151 225669042227508887019313727)
  ·
    refine ⟨338503563341263330528970591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225669042227508887019313727 338503563341263330528970591)
    ·
      refine ⟨507755345011894995793455887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338503563341263330528970591 507755345011894995793455887)
      ·
        refine ⟨761633017517842493690183831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507755345011894995793455887 761633017517842493690183831)
        ·
          refine ⟨1142449526276763740535275747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761633017517842493690183831 1142449526276763740535275747)
          ·
            refine ⟨1713674289415145610802913621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142449526276763740535275747 1713674289415145610802913621)
            ·
              refine ⟨5020530144770934406649161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1713674289415145610802913621 5020530144770934406649161)
              ·
                refine ⟨3765397608578200804986871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020530144770934406649161 3765397608578200804986871)
                ·
                  refine ⟨5648096412867301207480307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765397608578200804986871 5648096412867301207480307)
                  ·
                    refine ⟨8472144619300951811220461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648096412867301207480307 8472144619300951811220461)
                    ·
                      refine ⟨3177054232237856929207673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472144619300951811220461 3177054232237856929207673)
                      ·
                        rfl

theorem cell23_6187291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 1, 3].length) (baseStart_6187291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187291 prefixEnd_6187291 := by exact prefixLift 6187291
  have htrace : WordTrace (prefixWord ++ tailWord_6187291) baseStart_6187291 baseEnd_6187291 := by
    simpa [prefixWord, tailWord_6187291, baseEnd_6187291] using wordTrace_append hprefix tailTrace_6187291
  have hstable : (prefixWord ++ tailWord_6187291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187291).length < 2 ^ (prefixWord ++ tailWord_6187291).sum := by decide
  have hdescent : baseEnd_6187291 < baseStart_6187291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187294 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6187294 : Nat := 118140960795 + 6187294 * 2 ^ 59
def prefixEnd_6187294 : Nat := 4983230072969 + 3 ^ 40 * 6187294 * 2
def baseEnd_6187294 : Nat := 1059018590893273472490053

theorem tailTrace_6187294 : CollatzResearch.WordTrace tailWord_6187294 prefixEnd_6187294 1059018590893273472490053 := by
  unfold tailWord_6187294
  simp only [CollatzResearch.WordTrace]
  refine ⟨28208643955812252316459117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150446101097665345687781957 28208643955812252316459117)
  ·
    refine ⟨10578241483429594618672169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28208643955812252316459117 10578241483429594618672169)
    ·
      refine ⟨7933681112572195964004127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10578241483429594618672169 7933681112572195964004127)
      ·
        refine ⟨11900521668858293946006191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933681112572195964004127 11900521668858293946006191)
        ·
          refine ⟨17850782503287440919009287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11900521668858293946006191 17850782503287440919009287)
          ·
            refine ⟨26776173754931161378513931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17850782503287440919009287 26776173754931161378513931)
            ·
              refine ⟨40164260632396742067770897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26776173754931161378513931 40164260632396742067770897)
              ·
                refine ⟨30123195474297556550828173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40164260632396742067770897 30123195474297556550828173)
                ·
                  refine ⟨11296198302861583706560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30123195474297556550828173 11296198302861583706560565)
                  ·
                    refine ⟨1059018590893273472490053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11296198302861583706560565 1059018590893273472490053)
                    ·
                      rfl

theorem cell23_6187294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6187294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187294 prefixEnd_6187294 := by exact prefixLift 6187294
  have htrace : WordTrace (prefixWord ++ tailWord_6187294) baseStart_6187294 baseEnd_6187294 := by
    simpa [prefixWord, tailWord_6187294, baseEnd_6187294] using wordTrace_append hprefix tailTrace_6187294
  have hstable : (prefixWord ++ tailWord_6187294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187294).length < 2 ^ (prefixWord ++ tailWord_6187294).sum := by decide
  have hdescent : baseEnd_6187294 < baseStart_6187294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187317 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_6187317 : Nat := 118140960795 + 6187317 * 2 ^ 59
def prefixEnd_6187317 : Nat := 4983230072969 + 3 ^ 40 * 6187317 * 2
def baseEnd_6187317 : Nat := 3177067582734873827482553

theorem tailTrace_6187317 : CollatzResearch.WordTrace tailWord_6187317 prefixEnd_6187317 3177067582734873827482553 := by
  unfold tailWord_6187317
  simp only [CollatzResearch.WordTrace]
  refine ⟨225669990525414693459760205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150446660350276462306506803 225669990525414693459760205)
  ·
    refine ⟨84626246447030510047410077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225669990525414693459760205 84626246447030510047410077)
    ·
      refine ⟨31734842417636441267778779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84626246447030510047410077 31734842417636441267778779)
      ·
        refine ⟨47602263626454661901668169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31734842417636441267778779 47602263626454661901668169)
        ·
          refine ⟨35701697719840996426251127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47602263626454661901668169 35701697719840996426251127)
          ·
            refine ⟨53552546579761494639376691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35701697719840996426251127 53552546579761494639376691)
            ·
              refine ⟨80328819869642241959065037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53552546579761494639376691 80328819869642241959065037)
              ·
                refine ⟨30123307451115840734649389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80328819869642241959065037 30123307451115840734649389)
                ·
                  refine ⟨11296240294168440275493521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30123307451115840734649389 11296240294168440275493521)
                  ·
                    refine ⟨8472180220626330206620141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11296240294168440275493521 8472180220626330206620141)
                    ·
                      refine ⟨3177067582734873827482553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472180220626330206620141 3177067582734873827482553)
                      ·
                        rfl

theorem cell23_6187317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_6187317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187317 prefixEnd_6187317 := by exact prefixLift 6187317
  have htrace : WordTrace (prefixWord ++ tailWord_6187317) baseStart_6187317 baseEnd_6187317 := by
    simpa [prefixWord, tailWord_6187317, baseEnd_6187317] using wordTrace_append hprefix tailTrace_6187317
  have hstable : (prefixWord ++ tailWord_6187317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187317).length < 2 ^ (prefixWord ++ tailWord_6187317).sum := by decide
  have hdescent : baseEnd_6187317 < baseStart_6187317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187331 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 1, 2, 2]
def baseStart_6187331 : Nat := 118140960795 + 6187331 * 2 ^ 59
def prefixEnd_6187331 : Nat := 4983230072969 + 3 ^ 40 * 6187331 * 2
def baseEnd_6187331 : Nat := 3177074771464036772707489

theorem tailTrace_6187331 : CollatzResearch.WordTrace tailWord_6187331 prefixEnd_6187331 3177074771464036772707489 := by
  unfold tailWord_6187331
  simp only [CollatzResearch.WordTrace]
  refine ⟨225670501147363973850769847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150447000764909315900513231 225670501147363973850769847)
  ·
    refine ⟨338505751721045960776154771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225670501147363973850769847 338505751721045960776154771)
    ·
      refine ⟨507758627581568941164232157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338505751721045960776154771 507758627581568941164232157)
      ·
        refine ⟨190409485343088352936587059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507758627581568941164232157 190409485343088352936587059)
        ·
          refine ⟨285614228014632529404880589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190409485343088352936587059 285614228014632529404880589)
          ·
            refine ⟨107105335505487198526830221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285614228014632529404880589 107105335505487198526830221)
            ·
              refine ⟨40164500814557699447561333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107105335505487198526830221 40164500814557699447561333)
              ·
                refine ⟨3765421951364784323208875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40164500814557699447561333 3765421951364784323208875)
                ·
                  refine ⟨5648132927047176484813313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765421951364784323208875 5648132927047176484813313)
                  ·
                    refine ⟨4236099695285382363609985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5648132927047176484813313 4236099695285382363609985)
                    ·
                      refine ⟨3177074771464036772707489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236099695285382363609985 3177074771464036772707489)
                      ·
                        rfl

theorem cell23_6187331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_6187331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187331 prefixEnd_6187331 := by exact prefixLift 6187331
  have htrace : WordTrace (prefixWord ++ tailWord_6187331) baseStart_6187331 baseEnd_6187331 := by
    simpa [prefixWord, tailWord_6187331, baseEnd_6187331] using wordTrace_append hprefix tailTrace_6187331
  have hstable : (prefixWord ++ tailWord_6187331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187331).length < 2 ^ (prefixWord ++ tailWord_6187331).sum := by decide
  have hdescent : baseEnd_6187331 < baseStart_6187331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187348 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_6187348 : Nat := 118140960795 + 6187348 * 2 ^ 59
def prefixEnd_6187348 : Nat := 4983230072969 + 3 ^ 40 * 6187348 * 2
def baseEnd_6187348 : Nat := 3177083500635163206194911

theorem tailTrace_6187348 : CollatzResearch.WordTrace tailWord_6187348 prefixEnd_6187348 3177083500635163206194911 := by
  unfold tailWord_6187348
  simp only [CollatzResearch.WordTrace]
  refine ⟨112835560594151192877069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150447414125534923836092465 112835560594151192877069349)
  ·
    refine ⟨21156667611403348664450503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112835560594151192877069349 21156667611403348664450503)
    ·
      refine ⟨31735001417105022996675755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21156667611403348664450503 31735001417105022996675755)
      ·
        refine ⟨47602502125657534495013633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31735001417105022996675755 47602502125657534495013633)
        ·
          refine ⟨35701876594243150871260225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47602502125657534495013633 35701876594243150871260225)
          ·
            refine ⟨26776407445682363153445169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35701876594243150871260225 26776407445682363153445169)
            ·
              refine ⟨20082305584261772365083877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26776407445682363153445169 20082305584261772365083877)
              ·
                refine ⟨3765432297049082318453227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20082305584261772365083877 3765432297049082318453227)
                ·
                  refine ⟨5648148445573623477679841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765432297049082318453227 5648148445573623477679841)
                  ·
                    refine ⟨4236111334180217608259881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5648148445573623477679841 4236111334180217608259881)
                    ·
                      refine ⟨3177083500635163206194911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236111334180217608259881 3177083500635163206194911)
                      ·
                        rfl

theorem cell23_6187348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_6187348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187348 prefixEnd_6187348 := by exact prefixLift 6187348
  have htrace : WordTrace (prefixWord ++ tailWord_6187348) baseStart_6187348 baseEnd_6187348 := by
    simpa [prefixWord, tailWord_6187348, baseEnd_6187348] using wordTrace_append hprefix tailTrace_6187348
  have hstable : (prefixWord ++ tailWord_6187348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187348).length < 2 ^ (prefixWord ++ tailWord_6187348).sum := by decide
  have hdescent : baseEnd_6187348 < baseStart_6187348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187425 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6187425 : Nat := 118140960795 + 6187425 * 2 ^ 59
def prefixEnd_6187425 : Nat := 4983230072969 + 3 ^ 40 * 6187425 * 2
def baseEnd_6187425 : Nat := 3177123038645559404932057

theorem tailTrace_6187425 : CollatzResearch.WordTrace tailWord_6187425 prefixEnd_6187425 3177123038645559404932057 := by
  unfold tailWord_6187425
  simp only [CollatzResearch.WordTrace]
  refine ⟨225673929609023427904691729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150449286406015618603127819 225673929609023427904691729)
  ·
    refine ⟨169255447206767570928518797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225673929609023427904691729 169255447206767570928518797)
    ·
      refine ⟨63470792702537839098194549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169255447206767570928518797 63470792702537839098194549)
      ·
        refine ⟨5950386815862922415455739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63470792702537839098194549 5950386815862922415455739)
        ·
          refine ⟨8925580223794383623183609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950386815862922415455739 8925580223794383623183609)
          ·
            refine ⟨6694185167845787717387707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8925580223794383623183609 6694185167845787717387707)
            ·
              refine ⟨10041277751768681576081561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694185167845787717387707 10041277751768681576081561)
              ·
                refine ⟨7530958313826511182061171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10041277751768681576081561 7530958313826511182061171)
                ·
                  refine ⟨11296437470739766773091757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7530958313826511182061171 11296437470739766773091757)
                  ·
                    refine ⟨4236164051527412539909409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11296437470739766773091757 4236164051527412539909409)
                    ·
                      refine ⟨3177123038645559404932057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236164051527412539909409 3177123038645559404932057)
                      ·
                        rfl

theorem cell23_6187425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6187425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187425 prefixEnd_6187425 := by exact prefixLift 6187425
  have htrace : WordTrace (prefixWord ++ tailWord_6187425) baseStart_6187425 baseEnd_6187425 := by
    simpa [prefixWord, tailWord_6187425, baseEnd_6187425] using wordTrace_append hprefix tailTrace_6187425
  have hstable : (prefixWord ++ tailWord_6187425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187425).length < 2 ^ (prefixWord ++ tailWord_6187425).sum := by decide
  have hdescent : baseEnd_6187425 < baseStart_6187425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187440 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_6187440 : Nat := 118140960795 + 6187440 * 2 ^ 59
def prefixEnd_6187440 : Nat := 4983230072969 + 3 ^ 40 * 6187440 * 2
def baseEnd_6187440 : Nat := 1059043580285125615414829

theorem tailTrace_6187440 : CollatzResearch.WordTrace tailWord_6187440 prefixEnd_6187440 1059043580285125615414829 := by
  unfold tailWord_6187440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112837238351984542733243887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150449651135979390310991849 112837238351984542733243887)
  ·
    refine ⟨169255857527976814099865831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112837238351984542733243887 169255857527976814099865831)
    ·
      refine ⟨253883786291965221149798747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169255857527976814099865831 253883786291965221149798747)
      ·
        refine ⟨380825679437947831724698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253883786291965221149798747 380825679437947831724698121)
        ·
          refine ⟨285619259578460873793523591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380825679437947831724698121 285619259578460873793523591)
          ·
            refine ⟨428428889367691310690285387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285619259578460873793523591 428428889367691310690285387)
            ·
              refine ⟨642643334051536966035428081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428428889367691310690285387 642643334051536966035428081)
              ·
                refine ⟨481982500538652724526571061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642643334051536966035428081 481982500538652724526571061)
                ·
                  refine ⟨45185859425498692924366037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481982500538652724526571061 45185859425498692924366037)
                  ·
                    refine ⟨1059043580285125615414829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45185859425498692924366037 1059043580285125615414829)
                    ·
                      rfl

theorem cell23_6187440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_6187440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187440 prefixEnd_6187440 := by exact prefixLift 6187440
  have htrace : WordTrace (prefixWord ++ tailWord_6187440) baseStart_6187440 baseEnd_6187440 := by
    simpa [prefixWord, tailWord_6187440, baseEnd_6187440] using wordTrace_append hprefix tailTrace_6187440
  have hstable : (prefixWord ++ tailWord_6187440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187440).length < 2 ^ (prefixWord ++ tailWord_6187440).sum := by decide
  have hdescent : baseEnd_6187440 < baseStart_6187440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187464 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_6187464 : Nat := 118140960795 + 6187464 * 2 ^ 59
def prefixEnd_6187464 : Nat := 4983230072969 + 3 ^ 40 * 6187464 * 2
def baseEnd_6187464 : Nat := 3177143064391084752344377

theorem tailTrace_6187464 : CollatzResearch.WordTrace tailWord_6187464 prefixEnd_6187464 3177143064391084752344377 := by
  unfold tailWord_6187464
  simp only [CollatzResearch.WordTrace]
  refine ⟨112837676027941068782680723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150450234703921425043574297 112837676027941068782680723)
  ·
    refine ⟨169256514041911603174021085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112837676027941068782680723 169256514041911603174021085)
    ·
      refine ⟨63471192765716851190257907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169256514041911603174021085 63471192765716851190257907)
      ·
        refine ⟨95206789148575276785386861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63471192765716851190257907 95206789148575276785386861)
        ·
          refine ⟨35702545930715728794520073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95206789148575276785386861 35702545930715728794520073)
          ·
            refine ⟨26776909448036796595890055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35702545930715728794520073 26776909448036796595890055)
            ·
              refine ⟨40165364172055194893835083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26776909448036796595890055 40165364172055194893835083)
              ·
                refine ⟨60248046258082792340752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40165364172055194893835083 60248046258082792340752625)
                ·
                  refine ⟨45186034693562094255564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60248046258082792340752625 45186034693562094255564469)
                  ·
                    refine ⟨4236190752521446336459169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45186034693562094255564469 4236190752521446336459169)
                    ·
                      refine ⟨3177143064391084752344377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236190752521446336459169 3177143064391084752344377)
                      ·
                        rfl

theorem cell23_6187464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_6187464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187464 prefixEnd_6187464 := by exact prefixLift 6187464
  have htrace : WordTrace (prefixWord ++ tailWord_6187464) baseStart_6187464 baseEnd_6187464 := by
    simpa [prefixWord, tailWord_6187464, baseEnd_6187464] using wordTrace_append hprefix tailTrace_6187464
  have hstable : (prefixWord ++ tailWord_6187464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187464).length < 2 ^ (prefixWord ++ tailWord_6187464).sum := by decide
  have hdescent : baseEnd_6187464 < baseStart_6187464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187491 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 2, 5]
def baseStart_6187491 : Nat := 118140960795 + 6187491 * 2 ^ 59
def prefixEnd_6187491 : Nat := 4983230072969 + 3 ^ 40 * 6187491 * 2
def baseEnd_6187491 : Nat := 1059052309456252048902251

theorem tailTrace_6187491 : CollatzResearch.WordTrace tailWord_6187491 prefixEnd_6187491 1059052309456252048902251 := by
  unfold tailWord_6187491
  simp only [CollatzResearch.WordTrace]
  refine ⟨225676336826784321176594327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150450891217856214117729551 225676336826784321176594327)
  ·
    refine ⟨338514505240176481764891491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225676336826784321176594327 338514505240176481764891491)
    ·
      refine ⟨507771757860264722647337237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338514505240176481764891491 507771757860264722647337237)
      ·
        refine ⟨23801801149699908874093933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 507771757860264722647337237 23801801149699908874093933)
        ·
          refine ⟨8925675431137465827785225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23801801149699908874093933 8925675431137465827785225)
          ·
            refine ⟨6694256573353099370838919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8925675431137465827785225 6694256573353099370838919)
            ·
              refine ⟨10041384860029649056258379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694256573353099370838919 10041384860029649056258379)
              ·
                refine ⟨15062077290044473584387569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041384860029649056258379 15062077290044473584387569)
                ·
                  refine ⟨11296557967533355188290677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15062077290044473584387569 11296557967533355188290677)
                  ·
                    refine ⟨1059052309456252048902251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11296557967533355188290677 1059052309456252048902251)
                    ·
                      rfl

theorem cell23_6187491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 5].length) (baseStart_6187491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187491 prefixEnd_6187491 := by exact prefixLift 6187491
  have htrace : WordTrace (prefixWord ++ tailWord_6187491) baseStart_6187491 baseEnd_6187491 := by
    simpa [prefixWord, tailWord_6187491, baseEnd_6187491] using wordTrace_append hprefix tailTrace_6187491
  have hstable : (prefixWord ++ tailWord_6187491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187491).length < 2 ^ (prefixWord ++ tailWord_6187491).sum := by decide
  have hdescent : baseEnd_6187491 < baseStart_6187491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187517 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 8]
def baseStart_6187517 : Nat := 118140960795 + 6187517 * 2 ^ 59
def prefixEnd_6187517 : Nat := 4983230072969 + 3 ^ 40 * 6187517 * 2
def baseEnd_6187517 : Nat := 353018919873974782775737

theorem tailTrace_6187517 : CollatzResearch.WordTrace tailWord_6187517 prefixEnd_6187517 353018919873974782775737 := by
  unfold tailWord_6187517
  simp only [CollatzResearch.WordTrace]
  refine ⟨225677285124690127617040805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150451523416460085078027203 225677285124690127617040805)
  ·
    refine ⟨42314490960879398928195151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225677285124690127617040805 42314490960879398928195151)
    ·
      refine ⟨63471736441319098392292727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42314490960879398928195151 63471736441319098392292727)
      ·
        refine ⟨95207604661978647588439091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63471736441319098392292727 95207604661978647588439091)
        ·
          refine ⟨142811406992967971382658637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95207604661978647588439091 142811406992967971382658637)
          ·
            refine ⟨53554277622362989268496989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142811406992967971382658637 53554277622362989268496989)
            ·
              refine ⟨20082854108386120975686371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53554277622362989268496989 20082854108386120975686371)
              ·
                refine ⟨30124281162579181463529557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20082854108386120975686371 30124281162579181463529557)
                ·
                  refine ⟨353018919873974782775737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30124281162579181463529557 353018919873974782775737)
                  ·
                    rfl

theorem cell23_6187517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_6187517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187517 prefixEnd_6187517 := by exact prefixLift 6187517
  have htrace : WordTrace (prefixWord ++ tailWord_6187517) baseStart_6187517 baseEnd_6187517 := by
    simpa [prefixWord, tailWord_6187517, baseEnd_6187517] using wordTrace_append hprefix tailTrace_6187517
  have hstable : (prefixWord ++ tailWord_6187517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187517).length < 2 ^ (prefixWord ++ tailWord_6187517).sum := by decide
  have hdescent : baseEnd_6187517 < baseStart_6187517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187521 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6187521 : Nat := 118140960795 + 6187521 * 2 ^ 59
def prefixEnd_6187521 : Nat := 4983230072969 + 3 ^ 40 * 6187521 * 2
def baseEnd_6187521 : Nat := 1059057444262797009777205

theorem tailTrace_6187521 : CollatzResearch.WordTrace tailWord_6187521 prefixEnd_6187521 1059057444262797009777205 := by
  unfold tailWord_6187521
  simp only [CollatzResearch.WordTrace]
  refine ⟨225677431016675636300186417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150451620677783757533457611 225677431016675636300186417)
  ·
    refine ⟨169258073262506727225139813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225677431016675636300186417 169258073262506727225139813)
    ·
      refine ⟨31735888736720011354713715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169258073262506727225139813 31735888736720011354713715)
      ·
        refine ⟨47603833105080017032070573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31735888736720011354713715 47603833105080017032070573)
        ·
          refine ⟨17851437414405006387026465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47603833105080017032070573 17851437414405006387026465)
          ·
            refine ⟨13388578060803754790269849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17851437414405006387026465 13388578060803754790269849)
            ·
              refine ⟨10041433545602816092702387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13388578060803754790269849 10041433545602816092702387)
              ·
                refine ⟨15062150318404224139053581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041433545602816092702387 15062150318404224139053581)
                ·
                  refine ⟨5648306369401584052145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15062150318404224139053581 5648306369401584052145093)
                  ·
                    refine ⟨1059057444262797009777205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5648306369401584052145093 1059057444262797009777205)
                    ·
                      rfl

theorem cell23_6187521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6187521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187521 prefixEnd_6187521 := by exact prefixLift 6187521
  have htrace : WordTrace (prefixWord ++ tailWord_6187521) baseStart_6187521 baseEnd_6187521 := by
    simpa [prefixWord, tailWord_6187521, baseEnd_6187521] using wordTrace_append hprefix tailTrace_6187521
  have hstable : (prefixWord ++ tailWord_6187521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187521).length < 2 ^ (prefixWord ++ tailWord_6187521).sum := by decide
  have hdescent : baseEnd_6187521 < baseStart_6187521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187571 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 2, 3, 2]
def baseStart_6187571 : Nat := 118140960795 + 6187571 * 2 ^ 59
def prefixEnd_6187571 : Nat := 4983230072969 + 3 ^ 40 * 6187571 * 2
def baseEnd_6187571 : Nat := 3177198006821115833706385

theorem tailTrace_6187571 : CollatzResearch.WordTrace tailWord_6187571 prefixEnd_6187571 3177198006821115833706385 := by
  unfold tailWord_6187571
  simp only [CollatzResearch.WordTrace]
  refine ⟨225679254666494494839506567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150452836444329663226337711 225679254666494494839506567)
  ·
    refine ⟨338518881999741742259259851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225679254666494494839506567 338518881999741742259259851)
    ·
      refine ⟨507778322999612613388889777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338518881999741742259259851 507778322999612613388889777)
      ·
        refine ⟨380833742249709460041667333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507778322999612613388889777 380833742249709460041667333)
        ·
          refine ⟨71406326671820523757812625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380833742249709460041667333 71406326671820523757812625)
          ·
            refine ⟨53554745003865392818359469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71406326671820523757812625 53554745003865392818359469)
            ·
              refine ⟨20083029376449522306884801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53554745003865392818359469 20083029376449522306884801)
              ·
                refine ⟨15062272032337141730163601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20083029376449522306884801 15062272032337141730163601)
                ·
                  refine ⟨11296704024252856297622701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15062272032337141730163601 11296704024252856297622701)
                  ·
                    refine ⟨4236264009094821111608513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11296704024252856297622701 4236264009094821111608513)
                    ·
                      refine ⟨3177198006821115833706385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236264009094821111608513 3177198006821115833706385)
                      ·
                        rfl

theorem cell23_6187571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3, 2].length) (baseStart_6187571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187571 prefixEnd_6187571 := by exact prefixLift 6187571
  have htrace : WordTrace (prefixWord ++ tailWord_6187571) baseStart_6187571 baseEnd_6187571 := by
    simpa [prefixWord, tailWord_6187571, baseEnd_6187571] using wordTrace_append hprefix tailTrace_6187571
  have hstable : (prefixWord ++ tailWord_6187571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187571).length < 2 ^ (prefixWord ++ tailWord_6187571).sum := by decide
  have hdescent : baseEnd_6187571 < baseStart_6187571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187572 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6187572 : Nat := 118140960795 + 6187572 * 2 ^ 59
def prefixEnd_6187572 : Nat := 4983230072969 + 3 ^ 40 * 6187572 * 2
def baseEnd_6187572 : Nat := 1059066173433923443264627

theorem tailTrace_6187572 : CollatzResearch.WordTrace tailWord_6187572 prefixEnd_6187572 1059066173433923443264627 := by
  unfold tailWord_6187572
  simp only [CollatzResearch.WordTrace]
  refine ⟨112839645569745436005146485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150452860759660581340195313 112839645569745436005146485)
  ·
    refine ⟨10578716772163634625482483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112839645569745436005146485 10578716772163634625482483)
    ·
      refine ⟨15868075158245451938223725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578716772163634625482483 15868075158245451938223725)
      ·
        refine ⟨5950528184342044476833897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15868075158245451938223725 5950528184342044476833897)
        ·
          refine ⟨4462896138256533357625423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950528184342044476833897 4462896138256533357625423)
          ·
            refine ⟨6694344207384800036438135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462896138256533357625423 6694344207384800036438135)
            ·
              refine ⟨10041516311077200054657203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694344207384800036438135 10041516311077200054657203)
              ·
                refine ⟨15062274466615800081985805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041516311077200054657203 15062274466615800081985805)
                ·
                  refine ⟨5648352924980925030744677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15062274466615800081985805 5648352924980925030744677)
                  ·
                    refine ⟨1059066173433923443264627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5648352924980925030744677 1059066173433923443264627)
                    ·
                      rfl

theorem cell23_6187572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6187572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187572 prefixEnd_6187572 := by exact prefixLift 6187572
  have htrace : WordTrace (prefixWord ++ tailWord_6187572) baseStart_6187572 baseEnd_6187572 := by
    simpa [prefixWord, tailWord_6187572, baseEnd_6187572] using wordTrace_append hprefix tailTrace_6187572
  have hstable : (prefixWord ++ tailWord_6187572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187572).length < 2 ^ (prefixWord ++ tailWord_6187572).sum := by decide
  have hdescent : baseEnd_6187572 < baseStart_6187572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187578 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_6187578 : Nat := 118140960795 + 6187578 * 2 ^ 59
def prefixEnd_6187578 : Nat := 4983230072969 + 3 ^ 40 * 6187578 * 2
def baseEnd_6187578 : Nat := 3177201601185697306318853

theorem tailTrace_6187578 : CollatzResearch.WordTrace tailWord_6187578 prefixEnd_6187578 3177201601185697306318853 := by
  unfold tailWord_6187578
  simp only [CollatzResearch.WordTrace]
  refine ⟨56419877494367283758752847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150453006651646090023340925 56419877494367283758752847)
  ·
    refine ⟨84629816241550925638129271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56419877494367283758752847 84629816241550925638129271)
    ·
      refine ⟨126944724362326388457193907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84629816241550925638129271 126944724362326388457193907)
      ·
        refine ⟨190417086543489582685790861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126944724362326388457193907 190417086543489582685790861)
        ·
          refine ⟨71406407453808593507171573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190417086543489582685790861 71406407453808593507171573)
          ·
            refine ⟨6694350698794555641297335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71406407453808593507171573 6694350698794555641297335)
            ·
              refine ⟨10041526048191833461946003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694350698794555641297335 10041526048191833461946003)
              ·
                refine ⟨15062289072287750192919005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041526048191833461946003 15062289072287750192919005)
                ·
                  refine ⟨5648358402107906322344627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15062289072287750192919005 5648358402107906322344627)
                  ·
                    refine ⟨8472537603161859483516941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648358402107906322344627 8472537603161859483516941)
                    ·
                      refine ⟨3177201601185697306318853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472537603161859483516941 3177201601185697306318853)
                      ·
                        rfl

theorem cell23_6187578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_6187578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187578 prefixEnd_6187578 := by exact prefixLift 6187578
  have htrace : WordTrace (prefixWord ++ tailWord_6187578) baseStart_6187578 baseEnd_6187578 := by
    simpa [prefixWord, tailWord_6187578, baseEnd_6187578] using wordTrace_append hprefix tailTrace_6187578
  have hstable : (prefixWord ++ tailWord_6187578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187578).length < 2 ^ (prefixWord ++ tailWord_6187578).sum := by decide
  have hdescent : baseEnd_6187578 < baseStart_6187578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187601 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_6187601 : Nat := 118140960795 + 6187601 * 2 ^ 59
def prefixEnd_6187601 : Nat := 4983230072969 + 3 ^ 40 * 6187601 * 2
def baseEnd_6187601 : Nat := 3177213411240750716331247

theorem tailTrace_6187601 : CollatzResearch.WordTrace tailWord_6187601 prefixEnd_6187601 3177213411240750716331247 := by
  unfold tailWord_6187601
  simp only [CollatzResearch.WordTrace]
  refine ⟨225680348856385809963098657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150453565904257206642065771 225680348856385809963098657)
  ·
    refine ⟨169260261642289357472323993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225680348856385809963098657 169260261642289357472323993)
    ·
      refine ⟨126945196231717018104242995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169260261642289357472323993 126945196231717018104242995)
      ·
        refine ⟨190417794347575527156364493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126945196231717018104242995 190417794347575527156364493)
        ·
          refine ⟨71406672880340822683636685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190417794347575527156364493 71406672880340822683636685)
          ·
            refine ⟨26777502330127808506363757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71406672880340822683636685 26777502330127808506363757)
            ·
              refine ⟨10041563373797928189886409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26777502330127808506363757 10041563373797928189886409)
              ·
                refine ⟨7531172530348446142414807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10041563373797928189886409 7531172530348446142414807)
                ·
                  refine ⟨11296758795522669213622211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531172530348446142414807 11296758795522669213622211)
                  ·
                    refine ⟨16945138193284003820433317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11296758795522669213622211 16945138193284003820433317)
                    ·
                      refine ⟨3177213411240750716331247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16945138193284003820433317 3177213411240750716331247)
                      ·
                        rfl

theorem cell23_6187601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_6187601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187601 prefixEnd_6187601 := by exact prefixLift 6187601
  have htrace : WordTrace (prefixWord ++ tailWord_6187601) baseStart_6187601 baseEnd_6187601 := by
    simpa [prefixWord, tailWord_6187601, baseEnd_6187601] using wordTrace_append hprefix tailTrace_6187601
  have hstable : (prefixWord ++ tailWord_6187601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187601).length < 2 ^ (prefixWord ++ tailWord_6187601).sum := by decide
  have hdescent : baseEnd_6187601 < baseStart_6187601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187607 : List Nat := [1, 1, 3, 2, 2, 2, 1, 11]
def baseStart_6187607 : Nat := 118140960795 + 6187607 * 2 ^ 59
def prefixEnd_6187607 : Nat := 4983230072969 + 3 ^ 40 * 6187607 * 2
def baseEnd_6187607 : Nat := 117674684893506581216897

theorem tailTrace_6187607 : CollatzResearch.WordTrace tailWord_6187607 prefixEnd_6187607 117674684893506581216897 := by
  unfold tailWord_6187607
  simp only [CollatzResearch.WordTrace]
  refine ⟨225680567694364072987817075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150453711796242715325211383 225680567694364072987817075)
  ·
    refine ⟨338520851541546109481725613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225680567694364072987817075 338520851541546109481725613)
    ·
      refine ⟨126945319328079791055647105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338520851541546109481725613 126945319328079791055647105)
      ·
        refine ⟨95208989496059843291735329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126945319328079791055647105 95208989496059843291735329)
        ·
          refine ⟨71406742122044882468801497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95208989496059843291735329 71406742122044882468801497)
          ·
            refine ⟨53555056591533661851601123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71406742122044882468801497 53555056591533661851601123)
            ·
              refine ⟨80332584887300492777401685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53555056591533661851601123 80332584887300492777401685)
              ·
                refine ⟨117674684893506581216897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80332584887300492777401685 117674684893506581216897)
                ·
                  rfl

theorem cell23_6187607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 11].length) (baseStart_6187607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187607 prefixEnd_6187607 := by exact prefixLift 6187607
  have htrace : WordTrace (prefixWord ++ tailWord_6187607) baseStart_6187607 baseEnd_6187607 := by
    simpa [prefixWord, tailWord_6187607, baseEnd_6187607] using wordTrace_append hprefix tailTrace_6187607
  have hstable : (prefixWord ++ tailWord_6187607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187607).length < 2 ^ (prefixWord ++ tailWord_6187607).sum := by decide
  have hdescent : baseEnd_6187607 < baseStart_6187607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187624 : List Nat := [2, 1, 4, 3, 2, 11]
def baseStart_6187624 : Nat := 118140960795 + 6187624 * 2 ^ 59
def prefixEnd_6187624 : Nat := 4983230072969 + 3 ^ 40 * 6187624 * 2
def baseEnd_6187624 : Nat := 13075000910682321507587

theorem tailTrace_6187624 : CollatzResearch.WordTrace tailWord_6187624 prefixEnd_6187624 13075000910682321507587 := by
  unfold tailWord_6187624
  simp only [CollatzResearch.WordTrace]
  refine ⟨112840593867651242445592963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150454125156868323260790617 112840593867651242445592963)
  ·
    refine ⟨169260890801476863668389445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112840593867651242445592963 169260890801476863668389445)
    ·
      refine ⟨31736417025276911937823021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169260890801476863668389445 31736417025276911937823021)
      ·
        refine ⟨11901156384478841976683633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31736417025276911937823021 11901156384478841976683633)
        ·
          refine ⟨8925867288359131482512725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11901156384478841976683633 8925867288359131482512725)
          ·
            refine ⟨13075000910682321507587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8925867288359131482512725 13075000910682321507587)
            ·
              rfl

theorem cell23_6187624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 11].length) (baseStart_6187624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187624 prefixEnd_6187624 := by exact prefixLift 6187624
  have htrace : WordTrace (prefixWord ++ tailWord_6187624) baseStart_6187624 baseEnd_6187624 := by
    simpa [prefixWord, tailWord_6187624, baseEnd_6187624] using wordTrace_append hprefix tailTrace_6187624
  have hstable : (prefixWord ++ tailWord_6187624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187624).length < 2 ^ (prefixWord ++ tailWord_6187624).sum := by decide
  have hdescent : baseEnd_6187624 < baseStart_6187624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187627 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_6187627 : Nat := 118140960795 + 6187627 * 2 ^ 59
def prefixEnd_6187627 : Nat := 4983230072969 + 3 ^ 40 * 6187627 * 2
def baseEnd_6187627 : Nat := 3177226761737767614606127

theorem tailTrace_6187627 : CollatzResearch.WordTrace tailWord_6187627 prefixEnd_6187627 3177226761737767614606127 := by
  unfold tailWord_6187627
  simp only [CollatzResearch.WordTrace]
  refine ⟨225681297154291616403545135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150454198102861077602363423 225681297154291616403545135)
  ·
    refine ⟨338521945731437424605317703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225681297154291616403545135 338521945731437424605317703)
    ·
      refine ⟨507782918597156136907976555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338521945731437424605317703 507782918597156136907976555)
      ·
        refine ⟨761674377895734205361964833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507782918597156136907976555 761674377895734205361964833)
        ·
          refine ⟨571255783421800654021473625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761674377895734205361964833 571255783421800654021473625)
          ·
            refine ⟨428441837566350490516105219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571255783421800654021473625 428441837566350490516105219)
            ·
              refine ⟨642662756349525735774157829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428441837566350490516105219 642662756349525735774157829)
              ·
                refine ⟨120499266815536075457654593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642662756349525735774157829 120499266815536075457654593)
                ·
                  refine ⟨90374450111652056593240945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120499266815536075457654593 90374450111652056593240945)
                  ·
                    refine ⟨67780837583739042444930709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90374450111652056593240945 67780837583739042444930709)
                    ·
                      refine ⟨3177226761737767614606127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67780837583739042444930709 3177226761737767614606127)
                      ·
                        rfl

theorem cell23_6187627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_6187627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187627 prefixEnd_6187627 := by exact prefixLift 6187627
  have htrace : WordTrace (prefixWord ++ tailWord_6187627) baseStart_6187627 baseEnd_6187627 := by
    simpa [prefixWord, tailWord_6187627, baseEnd_6187627] using wordTrace_append hprefix tailTrace_6187627
  have hstable : (prefixWord ++ tailWord_6187627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187627).length < 2 ^ (prefixWord ++ tailWord_6187627).sum := by decide
  have hdescent : baseEnd_6187627 < baseStart_6187627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187668 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6187668 : Nat := 118140960795 + 6187668 * 2 ^ 59
def prefixEnd_6187668 : Nat := 4983230072969 + 3 ^ 40 * 6187668 * 2
def baseEnd_6187668 : Nat := 3177247814444601954193439

theorem tailTrace_6187668 : CollatzResearch.WordTrace tailWord_6187668 prefixEnd_6187668 3177247814444601954193439 := by
  unfold tailWord_6187668
  simp only [CollatzResearch.WordTrace]
  refine ⟨112841396273571540202893829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150455195031428720270525105 112841396273571540202893829)
  ·
    refine ⟨21157761801294663788042593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112841396273571540202893829 21157761801294663788042593)
    ·
      refine ⟨15868321350970997841031945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21157761801294663788042593 15868321350970997841031945)
      ·
        refine ⟨11901241013228248380773959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15868321350970997841031945 11901241013228248380773959)
        ·
          refine ⟨17851861519842372571160939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11901241013228248380773959 17851861519842372571160939)
          ·
            refine ⟨26777792279763558856741409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17851861519842372571160939 26777792279763558856741409)
            ·
              refine ⟨20083344209822669142556057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26777792279763558856741409 20083344209822669142556057)
              ·
                refine ⟨15062508157367001856917043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20083344209822669142556057 15062508157367001856917043)
                ·
                  refine ⟨22593762236050502785375565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15062508157367001856917043 22593762236050502785375565)
                  ·
                    refine ⟨8472660838518938544515837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22593762236050502785375565 8472660838518938544515837)
                    ·
                      refine ⟨3177247814444601954193439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472660838518938544515837 3177247814444601954193439)
                      ·
                        rfl

theorem cell23_6187668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6187668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187668 prefixEnd_6187668 := by exact prefixLift 6187668
  have htrace : WordTrace (prefixWord ++ tailWord_6187668) baseStart_6187668 baseEnd_6187668 := by
    simpa [prefixWord, tailWord_6187668, baseEnd_6187668] using wordTrace_append hprefix tailTrace_6187668
  have hstable : (prefixWord ++ tailWord_6187668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187668).length < 2 ^ (prefixWord ++ tailWord_6187668).sum := by decide
  have hdescent : baseEnd_6187668 < baseStart_6187668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187684 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_6187684 : Nat := 118140960795 + 6187684 * 2 ^ 59
def prefixEnd_6187684 : Nat := 4983230072969 + 3 ^ 40 * 6187684 * 2
def baseEnd_6187684 : Nat := 1059085343378357963864455

theorem tailTrace_6187684 : CollatzResearch.WordTrace tailWord_6187684 prefixEnd_6187684 1059085343378357963864455 := by
  unfold tailWord_6187684
  simp only [CollatzResearch.WordTrace]
  refine ⟨112841688057542557569185053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150455584076723410092246737 112841688057542557569185053)
  ·
    refine ⟨42315633021578459088444395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112841688057542557569185053 42315633021578459088444395)
    ·
      refine ⟨63473449532367688632666593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42315633021578459088444395 63473449532367688632666593)
      ·
        refine ⟨47605087149275766474499945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63473449532367688632666593 47605087149275766474499945)
        ·
          refine ⟨35703815361956824855874959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47605087149275766474499945 35703815361956824855874959)
          ·
            refine ⟨53555723042935237283812439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35703815361956824855874959 53555723042935237283812439)
            ·
              refine ⟨80333584564402855925718659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53555723042935237283812439 80333584564402855925718659)
              ·
                refine ⟨120500376846604283888577989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80333584564402855925718659 120500376846604283888577989)
                ·
                  refine ⟨22593820658738303229108373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120500376846604283888577989 22593820658738303229108373)
                  ·
                    refine ⟨1059085343378357963864455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22593820658738303229108373 1059085343378357963864455)
                    ·
                      rfl

theorem cell23_6187684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_6187684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187684 prefixEnd_6187684 := by exact prefixLift 6187684
  have htrace : WordTrace (prefixWord ++ tailWord_6187684) baseStart_6187684 baseEnd_6187684 := by
    simpa [prefixWord, tailWord_6187684, baseEnd_6187684] using wordTrace_append hprefix tailTrace_6187684
  have hstable : (prefixWord ++ tailWord_6187684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187684).length < 2 ^ (prefixWord ++ tailWord_6187684).sum := by decide
  have hdescent : baseEnd_6187684 < baseStart_6187684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187701 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6187701 : Nat := 118140960795 + 6187701 * 2 ^ 59
def prefixEnd_6187701 : Nat := 4983230072969 + 3 ^ 40 * 6187701 * 2
def baseEnd_6187701 : Nat := 1059088253102066775026929

theorem tailTrace_6187701 : CollatzResearch.WordTrace tailWord_6187701 prefixEnd_6187701 1059088253102066775026929 := by
  unfold tailWord_6187701
  simp only [CollatzResearch.WordTrace]
  refine ⟨225683996156023527041738957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150455997437349018027825971 225683996156023527041738957)
  ·
    refine ⟨84631498558508822640652109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225683996156023527041738957 84631498558508822640652109)
    ·
      refine ⟨31736811959440808490244541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84631498558508822640652109 31736811959440808490244541)
      ·
        refine ⟨11901304484790303183841703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31736811959440808490244541 11901304484790303183841703)
        ·
          refine ⟨17851956727185454775762555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11901304484790303183841703 17851956727185454775762555)
          ·
            refine ⟨26777935090778182163643833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17851956727185454775762555 26777935090778182163643833)
            ·
              refine ⟨20083451318083636622732875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26777935090778182163643833 20083451318083636622732875)
              ·
                refine ⟨30125176977125454934099313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20083451318083636622732875 30125176977125454934099313)
                ·
                  refine ⟨22593882732844091200574485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30125176977125454934099313 22593882732844091200574485)
                  ·
                    refine ⟨1059088253102066775026929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22593882732844091200574485 1059088253102066775026929)
                    ·
                      rfl

theorem cell23_6187701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6187701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187701 prefixEnd_6187701 := by exact prefixLift 6187701
  have htrace : WordTrace (prefixWord ++ tailWord_6187701) baseStart_6187701 baseEnd_6187701 := by
    simpa [prefixWord, tailWord_6187701, baseEnd_6187701] using wordTrace_append hprefix tailTrace_6187701
  have hstable : (prefixWord ++ tailWord_6187701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187701).length < 2 ^ (prefixWord ++ tailWord_6187701).sum := by decide
  have hdescent : baseEnd_6187701 < baseStart_6187701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187702 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6187702 : Nat := 118140960795 + 6187702 * 2 ^ 59
def prefixEnd_6187702 : Nat := 4983230072969 + 3 ^ 40 * 6187702 * 2
def baseEnd_6187702 : Nat := 3177265272786854821168283

theorem tailTrace_6187702 : CollatzResearch.WordTrace tailWord_6187702 prefixEnd_6187702 3177265272786854821168283 := by
  unfold tailWord_6187702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105252039313744013282835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150456021752679936141683573 14105252039313744013282835)
  ·
    refine ⟨21157878058970616019924253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14105252039313744013282835 21157878058970616019924253)
    ·
      refine ⟨7934204272113981007471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21157878058970616019924253 7934204272113981007471595)
      ·
        refine ⟨11901306408170971511207393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7934204272113981007471595 11901306408170971511207393)
        ·
          refine ⟨8925979806128228633405545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11901306408170971511207393 8925979806128228633405545)
          ·
            refine ⟨6694484854596171475054159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8925979806128228633405545 6694484854596171475054159)
            ·
              refine ⟨10041727281894257212581239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694484854596171475054159 10041727281894257212581239)
              ·
                refine ⟨15062590922841385818871859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041727281894257212581239 15062590922841385818871859)
                ·
                  refine ⟨22593886384262078728307789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15062590922841385818871859 22593886384262078728307789)
                  ·
                    refine ⟨8472707394098279523115421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22593886384262078728307789 8472707394098279523115421)
                    ·
                      refine ⟨3177265272786854821168283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472707394098279523115421 3177265272786854821168283)
                      ·
                        rfl

theorem cell23_6187702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6187702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187702 prefixEnd_6187702 := by exact prefixLift 6187702
  have htrace : WordTrace (prefixWord ++ tailWord_6187702) baseStart_6187702 baseEnd_6187702 := by
    simpa [prefixWord, tailWord_6187702, baseEnd_6187702] using wordTrace_append hprefix tailTrace_6187702
  have hstable : (prefixWord ++ tailWord_6187702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187702).length < 2 ^ (prefixWord ++ tailWord_6187702).sum := by decide
  have hdescent : baseEnd_6187702 < baseStart_6187702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187778 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6187778 : Nat := 118140960795 + 6187778 * 2 ^ 59
def prefixEnd_6187778 : Nat := 4983230072969 + 3 ^ 40 * 6187778 * 2
def baseEnd_6187778 : Nat := 1059101432438865507939311

theorem tailTrace_6187778 : CollatzResearch.WordTrace tailWord_6187778 prefixEnd_6187778 1059101432438865507939311 := by
  unfold tailWord_6187778
  simp only [CollatzResearch.WordTrace]
  refine ⟨56421701144186142298072997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150457869717829712794861325 56421701144186142298072997)
  ·
    refine ⟨10579068964534901680888687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56421701144186142298072997 10579068964534901680888687)
    ·
      refine ⟨15868603446802352521333031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579068964534901680888687 15868603446802352521333031)
      ·
        refine ⟨23802905170203528781999547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15868603446802352521333031 23802905170203528781999547)
        ·
          refine ⟨35704357755305293172999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23802905170203528781999547 35704357755305293172999321)
          ·
            refine ⟨26778268316478969879749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35704357755305293172999321 26778268316478969879749491)
            ·
              refine ⟨40167402474718454819624237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26778268316478969879749491 40167402474718454819624237)
              ·
                refine ⟨15062775928019420557359089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40167402474718454819624237 15062775928019420557359089)
                ·
                  refine ⟨11297081946014565418019317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15062775928019420557359089 11297081946014565418019317)
                  ·
                    refine ⟨1059101432438865507939311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11297081946014565418019317 1059101432438865507939311)
                    ·
                      rfl

theorem cell23_6187778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6187778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187778 prefixEnd_6187778 := by exact prefixLift 6187778
  have htrace : WordTrace (prefixWord ++ tailWord_6187778) baseStart_6187778 baseEnd_6187778 := by
    simpa [prefixWord, tailWord_6187778, baseEnd_6187778] using wordTrace_append hprefix tailTrace_6187778
  have hstable : (prefixWord ++ tailWord_6187778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187778).length < 2 ^ (prefixWord ++ tailWord_6187778).sum := by decide
  have hdescent : baseEnd_6187778 < baseStart_6187778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187801 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_6187801 : Nat := 118140960795 + 6187801 * 2 ^ 59
def prefixEnd_6187801 : Nat := 4983230072969 + 3 ^ 40 * 6187801 * 2
def baseEnd_6187801 : Nat := 3177316107371649933830327

theorem tailTrace_6187801 : CollatzResearch.WordTrace tailWord_6187801 prefixEnd_6187801 3177316107371649933830327 := by
  unfold tailWord_6187801
  simp only [CollatzResearch.WordTrace]
  refine ⟨225687643455661244120379257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150458428970440829413586171 225687643455661244120379257)
  ·
    refine ⟨169265732591745933090284443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225687643455661244120379257 169265732591745933090284443)
    ·
      refine ⟨253898598887618899635426665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169265732591745933090284443 253898598887618899635426665)
      ·
        refine ⟨190423949165714174726569999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253898598887618899635426665 190423949165714174726569999)
        ·
          refine ⟨285635923748571262089854999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190423949165714174726569999 285635923748571262089854999)
          ·
            refine ⟨428453885622856893134782499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285635923748571262089854999 428453885622856893134782499)
            ·
              refine ⟨642680828434285339702173749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428453885622856893134782499 642680828434285339702173749)
              ·
                refine ⟨60251327665714250597078789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 642680828434285339702173749 60251327665714250597078789)
                ·
                  refine ⟨11297123937321421986952273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60251327665714250597078789 11297123937321421986952273)
                  ·
                    refine ⟨8472842952991066490214205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11297123937321421986952273 8472842952991066490214205)
                    ·
                      refine ⟨3177316107371649933830327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472842952991066490214205 3177316107371649933830327)
                      ·
                        rfl

theorem cell23_6187801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_6187801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187801 prefixEnd_6187801 := by exact prefixLift 6187801
  have htrace : WordTrace (prefixWord ++ tailWord_6187801) baseStart_6187801 baseEnd_6187801 := by
    simpa [prefixWord, tailWord_6187801, baseEnd_6187801] using wordTrace_append hprefix tailTrace_6187801
  have hstable : (prefixWord ++ tailWord_6187801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187801).length < 2 ^ (prefixWord ++ tailWord_6187801).sum := by decide
  have hdescent : baseEnd_6187801 < baseStart_6187801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187848 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_6187848 : Nat := 118140960795 + 6187848 * 2 ^ 59
def prefixEnd_6187848 : Nat := 4983230072969 + 3 ^ 40 * 6187848 * 2
def baseEnd_6187848 : Nat := 3177340240962411249942611

theorem tailTrace_6187848 : CollatzResearch.WordTrace tailWord_6187848 prefixEnd_6187848 3177340240962411249942611 := by
  unfold tailWord_6187848
  simp only [CollatzResearch.WordTrace]
  refine ⟨112844678843245485573670099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150459571790993980764893465 112844678843245485573670099)
  ·
    refine ⟨169267018264868228360505149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112844678843245485573670099 169267018264868228360505149)
    ·
      refine ⟨63475131849325585635189431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169267018264868228360505149 63475131849325585635189431)
      ·
        refine ⟨95212697773988378452784147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63475131849325585635189431 95212697773988378452784147)
        ·
          refine ⟨142819046660982567679176221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95212697773988378452784147 142819046660982567679176221)
          ·
            refine ⟨53557142497868462879691083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142819046660982567679176221 53557142497868462879691083)
            ·
              refine ⟨80335713746802694319536625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53557142497868462879691083 80335713746802694319536625)
              ·
                refine ⟨60251785310102020739652469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80335713746802694319536625 60251785310102020739652469)
                ·
                  refine ⟨5648604872822064444342419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60251785310102020739652469 5648604872822064444342419)
                  ·
                    refine ⟨8472907309233096666513629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648604872822064444342419 8472907309233096666513629)
                    ·
                      refine ⟨3177340240962411249942611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472907309233096666513629 3177340240962411249942611)
                      ·
                        rfl

theorem cell23_6187848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_6187848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187848 prefixEnd_6187848 := by exact prefixLift 6187848
  have htrace : WordTrace (prefixWord ++ tailWord_6187848) baseStart_6187848 baseEnd_6187848 := by
    simpa [prefixWord, tailWord_6187848, baseEnd_6187848] using wordTrace_append hprefix tailTrace_6187848
  have hstable : (prefixWord ++ tailWord_6187848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187848).length < 2 ^ (prefixWord ++ tailWord_6187848).sum := by decide
  have hdescent : baseEnd_6187848 < baseStart_6187848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187865 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_6187865 : Nat := 118140960795 + 6187865 * 2 ^ 59
def prefixEnd_6187865 : Nat := 4983230072969 + 3 ^ 40 * 6187865 * 2
def baseEnd_6187865 : Nat := 3177348970133537683430033

theorem tailTrace_6187865 : CollatzResearch.WordTrace tailWord_6187865 prefixEnd_6187865 3177348970133537683430033 := by
  unfold tailWord_6187865
  simp only [CollatzResearch.WordTrace]
  refine ⟨225689977727429383050709049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150459985151619588700472699 225689977727429383050709049)
  ·
    refine ⟨169267483295572037288031787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225689977727429383050709049 169267483295572037288031787)
    ·
      refine ⟨253901224943358055932047681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169267483295572037288031787 253901224943358055932047681)
      ·
        refine ⟨190425918707518541949035761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253901224943358055932047681 190425918707518541949035761)
        ·
          refine ⟨142819439030638906461776821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190425918707518541949035761 142819439030638906461776821)
          ·
            refine ⟨13389322409122397480791577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142819439030638906461776821 13389322409122397480791577)
            ·
              refine ⟨10041991806841798110593683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13389322409122397480791577 10041991806841798110593683)
              ·
                refine ⟨15062987710262697165890525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041991806841798110593683 15062987710262697165890525)
                ·
                  refine ⟨5648620391348511437208947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15062987710262697165890525 5648620391348511437208947)
                  ·
                    refine ⟨8472930587022767155813421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648620391348511437208947 8472930587022767155813421)
                    ·
                      refine ⟨3177348970133537683430033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472930587022767155813421 3177348970133537683430033)
                      ·
                        rfl

theorem cell23_6187865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_6187865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187865 prefixEnd_6187865 := by exact prefixLift 6187865
  have htrace : WordTrace (prefixWord ++ tailWord_6187865) baseStart_6187865 baseEnd_6187865 := by
    simpa [prefixWord, tailWord_6187865, baseEnd_6187865] using wordTrace_append hprefix tailTrace_6187865
  have hstable : (prefixWord ++ tailWord_6187865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187865).length < 2 ^ (prefixWord ++ tailWord_6187865).sum := by decide
  have hdescent : baseEnd_6187865 < baseStart_6187865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187888 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_6187888 : Nat := 118140960795 + 6187888 * 2 ^ 59
def prefixEnd_6187888 : Nat := 4983230072969 + 3 ^ 40 * 6187888 * 2
def baseEnd_6187888 : Nat := 3177360780188591093442427

theorem tailTrace_6187888 : CollatzResearch.WordTrace tailWord_6187888 prefixEnd_6187888 3177360780188591093442427 := by
  unfold tailWord_6187888
  simp only [CollatzResearch.WordTrace]
  refine ⟨112845408303173028989398159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150460544404230705319197545 112845408303173028989398159)
  ·
    refine ⟨169268112454759543484097239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112845408303173028989398159 169268112454759543484097239)
    ·
      refine ⟨253902168682139315226145859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169268112454759543484097239 253902168682139315226145859)
      ·
        refine ⟨380853253023208972839218789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253902168682139315226145859 380853253023208972839218789)
        ·
          refine ⟨71409984941851682407353523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380853253023208972839218789 71409984941851682407353523)
          ·
            refine ⟨107114977412777523611030285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71409984941851682407353523 107114977412777523611030285)
            ·
              refine ⟨40168116529791571354136357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107114977412777523611030285 40168116529791571354136357)
              ·
                refine ⟨7531521849335919628900567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40168116529791571354136357 7531521849335919628900567)
                ·
                  refine ⟨11297282774003879443350851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531521849335919628900567 11297282774003879443350851)
                  ·
                    refine ⟨16945924161005819165026277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11297282774003879443350851 16945924161005819165026277)
                    ·
                      refine ⟨3177360780188591093442427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16945924161005819165026277 3177360780188591093442427)
                      ·
                        rfl

theorem cell23_6187888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_6187888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187888 prefixEnd_6187888 := by exact prefixLift 6187888
  have htrace : WordTrace (prefixWord ++ tailWord_6187888) baseStart_6187888 baseEnd_6187888 := by
    simpa [prefixWord, tailWord_6187888, baseEnd_6187888] using wordTrace_append hprefix tailTrace_6187888
  have hstable : (prefixWord ++ tailWord_6187888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187888).length < 2 ^ (prefixWord ++ tailWord_6187888).sum := by decide
  have hdescent : baseEnd_6187888 < baseStart_6187888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187908 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_6187908 : Nat := 118140960795 + 6187908 * 2 ^ 59
def prefixEnd_6187908 : Nat := 4983230072969 + 3 ^ 40 * 6187908 * 2
def baseEnd_6187908 : Nat := 3177371049801681015192335

theorem tailTrace_6187908 : CollatzResearch.WordTrace tailWord_6187908 prefixEnd_6187908 3177371049801681015192335 := by
  unfold tailWord_6187908
  simp only [CollatzResearch.WordTrace]
  refine ⟨112845773033136800697262189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150461030710849067596349585 112845773033136800697262189)
  ·
    refine ⟨42317164887426300261473321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112845773033136800697262189 42317164887426300261473321)
    ·
      refine ⟨31737873665569725196104991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42317164887426300261473321 31737873665569725196104991)
      ·
        refine ⟨47606810498354587794157487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31737873665569725196104991 47606810498354587794157487)
        ·
          refine ⟨71410215747531881691236231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47606810498354587794157487 71410215747531881691236231)
          ·
            refine ⟨107115323621297822536854347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71410215747531881691236231 107115323621297822536854347)
            ·
              refine ⟨160672985431946733805281521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107115323621297822536854347 160672985431946733805281521)
              ·
                refine ⟨120504739073960050353961141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160672985431946733805281521 120504739073960050353961141)
                ·
                  refine ⟨11297319288183754720683857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120504739073960050353961141 11297319288183754720683857)
                  ·
                    refine ⟨8472989466137816040512893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11297319288183754720683857 8472989466137816040512893)
                    ·
                      refine ⟨3177371049801681015192335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8472989466137816040512893 3177371049801681015192335)
                      ·
                        rfl

theorem cell23_6187908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_6187908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187908 prefixEnd_6187908 := by exact prefixLift 6187908
  have htrace : WordTrace (prefixWord ++ tailWord_6187908) baseStart_6187908 baseEnd_6187908 := by
    simpa [prefixWord, tailWord_6187908, baseEnd_6187908] using wordTrace_append hprefix tailTrace_6187908
  have hstable : (prefixWord ++ tailWord_6187908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187908).length < 2 ^ (prefixWord ++ tailWord_6187908).sum := by decide
  have hdescent : baseEnd_6187908 < baseStart_6187908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187911 : List Nat := [1, 1, 4, 2, 3, 1, 11]
def baseStart_6187911 : Nat := 118140960795 + 6187911 * 2 ^ 59
def prefixEnd_6187911 : Nat := 4983230072969 + 3 ^ 40 * 6187911 * 2
def baseEnd_6187911 : Nat := 39226822101773388931541

theorem tailTrace_6187911 : CollatzResearch.WordTrace tailWord_6187911 prefixEnd_6187911 39226822101773388931541 := by
  unfold tailWord_6187911
  simp only [CollatzResearch.WordTrace]
  refine ⟨225691655485262732906883587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150461103656841821937922391 225691655485262732906883587)
  ·
    refine ⟨338537483227894099360325381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225691655485262732906883587 338537483227894099360325381)
    ·
      refine ⟨63475778105230143630061009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338537483227894099360325381 63475778105230143630061009)
      ·
        refine ⟨47606833578922607722545757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63475778105230143630061009 47606833578922607722545757)
        ·
          refine ⟨17852562592095977895954659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47606833578922607722545757 17852562592095977895954659)
          ·
            refine ⟨26778843888143966843931989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17852562592095977895954659 26778843888143966843931989)
            ·
              refine ⟨39226822101773388931541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26778843888143966843931989 39226822101773388931541)
              ·
                rfl

theorem cell23_6187911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 11].length) (baseStart_6187911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187911 prefixEnd_6187911 := by exact prefixLift 6187911
  have htrace : WordTrace (prefixWord ++ tailWord_6187911) baseStart_6187911 baseEnd_6187911 := by
    simpa [prefixWord, tailWord_6187911, baseEnd_6187911] using wordTrace_append hprefix tailTrace_6187911
  have hstable : (prefixWord ++ tailWord_6187911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187911).length < 2 ^ (prefixWord ++ tailWord_6187911).sum := by decide
  have hdescent : baseEnd_6187911 < baseStart_6187911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187932 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6187932 : Nat := 118140960795 + 6187932 * 2 ^ 59
def prefixEnd_6187932 : Nat := 4983230072969 + 3 ^ 40 * 6187932 * 2
def baseEnd_6187932 : Nat := 1059127791112462973764075

theorem tailTrace_6187932 : CollatzResearch.WordTrace tailWord_6187932 prefixEnd_6187932 1059127791112462973764075 := by
  unfold tailWord_6187932
  simp only [CollatzResearch.WordTrace]
  refine ⟨112846210709093326746699025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150461614278791102328932033 112846210709093326746699025)
  ·
    refine ⟨84634658031819995060024269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112846210709093326746699025 84634658031819995060024269)
    ·
      refine ⟨31737996761932498147509101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84634658031819995060024269 31737996761932498147509101)
      ·
        refine ⟨11901748785724686805315913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31737996761932498147509101 11901748785724686805315913)
        ·
          refine ⟨8926311589293515103986935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11901748785724686805315913 8926311589293515103986935)
          ·
            refine ⟨13389467383940272655980403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926311589293515103986935 13389467383940272655980403)
            ·
              refine ⟨20084201075910408983970605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13389467383940272655980403 20084201075910408983970605)
              ·
                refine ⟨7531575403466403368988977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20084201075910408983970605 7531575403466403368988977)
                ·
                  refine ⟨5648681552599802526741733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531575403466403368988977 5648681552599802526741733)
                  ·
                    refine ⟨1059127791112462973764075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5648681552599802526741733 1059127791112462973764075)
                    ·
                      rfl

theorem cell23_6187932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6187932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187932 prefixEnd_6187932 := by exact prefixLift 6187932
  have htrace : WordTrace (prefixWord ++ tailWord_6187932) baseStart_6187932 baseEnd_6187932 := by
    simpa [prefixWord, tailWord_6187932, baseEnd_6187932] using wordTrace_append hprefix tailTrace_6187932
  have hstable : (prefixWord ++ tailWord_6187932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187932).length < 2 ^ (prefixWord ++ tailWord_6187932).sum := by decide
  have hdescent : baseEnd_6187932 < baseStart_6187932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187948 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_6187948 : Nat := 118140960795 + 6187948 * 2 ^ 59
def prefixEnd_6187948 : Nat := 4983230072969 + 3 ^ 40 * 6187948 * 2
def baseEnd_6187948 : Nat := 3177391589027860858692151

theorem tailTrace_6187948 : CollatzResearch.WordTrace tailWord_6187948 prefixEnd_6187948 3177391589027860858692151 := by
  unfold tailWord_6187948
  simp only [CollatzResearch.WordTrace]
  refine ⟨112846502493064344112990249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150462003324085792150653665 112846502493064344112990249)
  ·
    refine ⟨84634876869798258084742687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112846502493064344112990249 84634876869798258084742687)
    ·
      refine ⟨126952315304697387127114031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84634876869798258084742687 126952315304697387127114031)
      ·
        refine ⟨190428472957046080690671047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126952315304697387127114031 190428472957046080690671047)
        ·
          refine ⟨285642709435569121036006571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190428472957046080690671047 285642709435569121036006571)
          ·
            refine ⟨428464064153353681554009857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285642709435569121036006571 428464064153353681554009857)
            ·
              refine ⟨321348048115015261165507393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428464064153353681554009857 321348048115015261165507393)
              ·
                refine ⟨241011036086261445874130545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321348048115015261165507393 241011036086261445874130545)
                ·
                  refine ⟨180758277064696084405597909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241011036086261445874130545 180758277064696084405597909)
                  ·
                    refine ⟨4236522118703814478256201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180758277064696084405597909 4236522118703814478256201)
                    ·
                      refine ⟨3177391589027860858692151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236522118703814478256201 3177391589027860858692151)
                      ·
                        rfl

theorem cell23_6187948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_6187948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187948 prefixEnd_6187948 := by exact prefixLift 6187948
  have htrace : WordTrace (prefixWord ++ tailWord_6187948) baseStart_6187948 baseEnd_6187948 := by
    simpa [prefixWord, tailWord_6187948, baseEnd_6187948] using wordTrace_append hprefix tailTrace_6187948
  have hstable : (prefixWord ++ tailWord_6187948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187948).length < 2 ^ (prefixWord ++ tailWord_6187948).sum := by decide
  have hdescent : baseEnd_6187948 < baseStart_6187948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187951 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_6187951 : Nat := 118140960795 + 6187951 * 2 ^ 59
def prefixEnd_6187951 : Nat := 4983230072969 + 3 ^ 40 * 6187951 * 2
def baseEnd_6187951 : Nat := 3177393129469824346954637

theorem tailTrace_6187951 : CollatzResearch.WordTrace tailWord_6187951 prefixEnd_6187951 3177393129469824346954637 := by
  unfold tailWord_6187951
  simp only [CollatzResearch.WordTrace]
  refine ⟨225693114405117819738339707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150462076270078546492226471 225693114405117819738339707)
  ·
    refine ⟨338539671607676729607509561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225693114405117819738339707 338539671607676729607509561)
    ·
      refine ⟨253904753705757547205632171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338539671607676729607509561 253904753705757547205632171)
      ·
        refine ⟨380857130558636320808448257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253904753705757547205632171 380857130558636320808448257)
        ·
          refine ⟨285642847918977240606336193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380857130558636320808448257 285642847918977240606336193)
          ·
            refine ⟨214232135939232930454752145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285642847918977240606336193 214232135939232930454752145)
            ·
              refine ⟨160674101954424697841064109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214232135939232930454752145 160674101954424697841064109)
              ·
                refine ⟨60252788232909261690399041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160674101954424697841064109 60252788232909261690399041)
                ·
                  refine ⟨45189591174681946267799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60252788232909261690399041 45189591174681946267799281)
                  ·
                    refine ⟨33892193381011459700849461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45189591174681946267799281 33892193381011459700849461)
                    ·
                      refine ⟨3177393129469824346954637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33892193381011459700849461 3177393129469824346954637)
                      ·
                        rfl

theorem cell23_6187951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_6187951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187951 prefixEnd_6187951 := by exact prefixLift 6187951
  have htrace : WordTrace (prefixWord ++ tailWord_6187951) baseStart_6187951 baseEnd_6187951 := by
    simpa [prefixWord, tailWord_6187951, baseEnd_6187951] using wordTrace_append hprefix tailTrace_6187951
  have hstable : (prefixWord ++ tailWord_6187951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187951).length < 2 ^ (prefixWord ++ tailWord_6187951).sum := by decide
  have hdescent : baseEnd_6187951 < baseStart_6187951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187971 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 6]
def baseStart_6187971 : Nat := 118140960795 + 6187971 * 2 ^ 59
def prefixEnd_6187971 : Nat := 4983230072969 + 3 ^ 40 * 6187971 * 2
def baseEnd_6187971 : Nat := 1059134466360971422901515

theorem tailTrace_6187971 : CollatzResearch.WordTrace tailWord_6187971 prefixEnd_6187971 1059134466360971422901515 := by
  unfold tailWord_6187971
  simp only [CollatzResearch.WordTrace]
  refine ⟨225693843865045363154067767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150462562576696908769378511 225693843865045363154067767)
  ·
    refine ⟨338540765797568044731101651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225693843865045363154067767 338540765797568044731101651)
    ·
      refine ⟨507811148696352067096652477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338540765797568044731101651 507811148696352067096652477)
      ·
        refine ⟨190429180761132025161244679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507811148696352067096652477 190429180761132025161244679)
        ·
          refine ⟨285643771141698037741867019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190429180761132025161244679 285643771141698037741867019)
          ·
            refine ⟨428465656712547056612800529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285643771141698037741867019 428465656712547056612800529)
            ·
              refine ⟨321349242534410292459600397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428465656712547056612800529 321349242534410292459600397)
              ·
                refine ⟨120505965950403859672350149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321349242534410292459600397 120505965950403859672350149)
                ·
                  refine ⟨22594868615700723688565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120505965950403859672350149 22594868615700723688565653)
                  ·
                    refine ⟨1059134466360971422901515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22594868615700723688565653 1059134466360971422901515)
                    ·
                      rfl

theorem cell23_6187971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_6187971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187971 prefixEnd_6187971 := by exact prefixLift 6187971
  have htrace : WordTrace (prefixWord ++ tailWord_6187971) baseStart_6187971 baseEnd_6187971 := by
    simpa [prefixWord, tailWord_6187971, baseEnd_6187971] using wordTrace_append hprefix tailTrace_6187971
  have hstable : (prefixWord ++ tailWord_6187971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187971).length < 2 ^ (prefixWord ++ tailWord_6187971).sum := by decide
  have hdescent : baseEnd_6187971 < baseStart_6187971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6187988 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_6187988 : Nat := 118140960795 + 6187988 * 2 ^ 59
def prefixEnd_6187988 : Nat := 4983230072969 + 3 ^ 40 * 6187988 * 2
def baseEnd_6187988 : Nat := 1059137376084680234063989

theorem tailTrace_6187988 : CollatzResearch.WordTrace tailWord_6187988 prefixEnd_6187988 1059137376084680234063989 := by
  unfold tailWord_6187988
  simp only [CollatzResearch.WordTrace]
  refine ⟨112847231952991887528718309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150462975937322516704957745 112847231952991887528718309)
  ·
    refine ⟨21158855991185978911634683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112847231952991887528718309 21158855991185978911634683)
    ·
      refine ⟨31738283986778968367452025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21158855991185978911634683 31738283986778968367452025)
      ·
        refine ⟨23803712990084226275589019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31738283986778968367452025 23803712990084226275589019)
        ·
          refine ⟨35705569485126339413383529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23803712990084226275589019 35705569485126339413383529)
          ·
            refine ⟨26779177113844754560037647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35705569485126339413383529 26779177113844754560037647)
            ·
              refine ⟨40168765670767131840056471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26779177113844754560037647 40168765670767131840056471)
              ·
                refine ⟨60253148506150697760084707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40168765670767131840056471 60253148506150697760084707)
                ·
                  refine ⟨90379722759226046640127061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60253148506150697760084707 90379722759226046640127061)
                  ·
                    refine ⟨1059137376084680234063989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90379722759226046640127061 1059137376084680234063989)
                    ·
                      rfl

theorem cell23_6187988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_6187988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6187988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6187988 prefixEnd_6187988 := by exact prefixLift 6187988
  have htrace : WordTrace (prefixWord ++ tailWord_6187988) baseStart_6187988 baseEnd_6187988 := by
    simpa [prefixWord, tailWord_6187988, baseEnd_6187988] using wordTrace_append hprefix tailTrace_6187988
  have hstable : (prefixWord ++ tailWord_6187988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6187988).length < 2 ^ (prefixWord ++ tailWord_6187988).sum := by decide
  have hdescent : baseEnd_6187988 < baseStart_6187988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6187988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188011 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_6188011 : Nat := 118140960795 + 6188011 * 2 ^ 59
def prefixEnd_6188011 : Nat := 4983230072969 + 3 ^ 40 * 6188011 * 2
def baseEnd_6188011 : Nat := 3177423938309094112204361

theorem tailTrace_6188011 : CollatzResearch.WordTrace tailWord_6188011 prefixEnd_6188011 3177423938309094112204361 := by
  unfold tailWord_6188011
  simp only [CollatzResearch.WordTrace]
  refine ⟨225695302784900449985523887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150463535189933633323682591 225695302784900449985523887)
  ·
    refine ⟨338542954177350674978285831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225695302784900449985523887 338542954177350674978285831)
    ·
      refine ⟨507814431266026012467428747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338542954177350674978285831 507814431266026012467428747)
      ·
        refine ⟨761721646899039018701143121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507814431266026012467428747 761721646899039018701143121)
        ·
          refine ⟨571291235174279264025857341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761721646899039018701143121 571291235174279264025857341)
          ·
            refine ⟨214234213190354724009696503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571291235174279264025857341 214234213190354724009696503)
            ·
              refine ⟨321351319785532086014544755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214234213190354724009696503 321351319785532086014544755)
              ·
                refine ⟨482026979678298129021817133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321351319785532086014544755 482026979678298129021817133)
                ·
                  refine ⟨180760117379361798383181425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482026979678298129021817133 180760117379361798383181425)
                  ·
                    refine ⟨135570088034521348787386069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180760117379361798383181425 135570088034521348787386069)
                    ·
                      refine ⟨3177423938309094112204361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135570088034521348787386069 3177423938309094112204361)
                      ·
                        rfl

theorem cell23_6188011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_6188011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188011 prefixEnd_6188011 := by exact prefixLift 6188011
  have htrace : WordTrace (prefixWord ++ tailWord_6188011) baseStart_6188011 baseEnd_6188011 := by
    simpa [prefixWord, tailWord_6188011, baseEnd_6188011] using wordTrace_append hprefix tailTrace_6188011
  have hstable : (prefixWord ++ tailWord_6188011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188011).length < 2 ^ (prefixWord ++ tailWord_6188011).sum := by decide
  have hdescent : baseEnd_6188011 < baseStart_6188011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188046 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6188046 : Nat := 118140960795 + 6188046 * 2 ^ 59
def prefixEnd_6188046 : Nat := 4983230072969 + 3 ^ 40 * 6188046 * 2
def baseEnd_6188046 : Nat := 3177441910132001475266701

theorem tailTrace_6188046 : CollatzResearch.WordTrace tailWord_6188046 prefixEnd_6188046 3177441910132001475266701 := by
  unfold tailWord_6188046
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212072417471706370380999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150464386226515767308698661 28212072417471706370380999)
  ·
    refine ⟨42318108626207559555571499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28212072417471706370380999 42318108626207559555571499)
    ·
      refine ⟨63477162939311339333357249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42318108626207559555571499 63477162939311339333357249)
      ·
        refine ⟨47607872204483504500017937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63477162939311339333357249 47607872204483504500017937)
        ·
          refine ⟨35705904153362628375013453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47607872204483504500017937 35705904153362628375013453)
          ·
            refine ⟨13389714057510985640630045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35705904153362628375013453 13389714057510985640630045)
            ·
              refine ⟨5021142771566619615236267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13389714057510985640630045 5021142771566619615236267)
              ·
                refine ⟨7531714157349929422854401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021142771566619615236267 7531714157349929422854401)
                ·
                  refine ⟨5648785618012447067140801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531714157349929422854401 5648785618012447067140801)
                  ·
                    refine ⟨4236589213509335300355601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5648785618012447067140801 4236589213509335300355601)
                    ·
                      refine ⟨3177441910132001475266701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236589213509335300355601 3177441910132001475266701)
                      ·
                        rfl

theorem cell23_6188046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6188046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188046 prefixEnd_6188046 := by exact prefixLift 6188046
  have htrace : WordTrace (prefixWord ++ tailWord_6188046) baseStart_6188046 baseEnd_6188046 := by
    simpa [prefixWord, tailWord_6188046, baseEnd_6188046] using wordTrace_append hprefix tailTrace_6188046
  have hstable : (prefixWord ++ tailWord_6188046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188046).length < 2 ^ (prefixWord ++ tailWord_6188046).sum := by decide
  have hdescent : baseEnd_6188046 < baseStart_6188046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188142 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_6188142 : Nat := 118140960795 + 6188142 * 2 ^ 59
def prefixEnd_6188142 : Nat := 4983230072969 + 3 ^ 40 * 6188142 * 2
def baseEnd_6188142 : Nat := 353054578252759233296251

theorem tailTrace_6188142 : CollatzResearch.WordTrace tailWord_6188142 prefixEnd_6188142 353054578252759233296251 := by
  unfold tailWord_6188142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212510093428232419817835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150466720498283906239028453 28212510093428232419817835)
  ·
    refine ⟨42318765140142348629726753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28212510093428232419817835 42318765140142348629726753)
    ·
      refine ⟨31739073855106761472295065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42318765140142348629726753 31739073855106761472295065)
      ·
        refine ⟨23804305391330071104221299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31739073855106761472295065 23804305391330071104221299)
        ·
          refine ⟨35706458086995106656331949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23804305391330071104221299 35706458086995106656331949)
          ·
            refine ⟨13389921782623164996124481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35706458086995106656331949 13389921782623164996124481)
            ·
              refine ⟨10042441336967373747093361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13389921782623164996124481 10042441336967373747093361)
              ·
                refine ⟨7531831002725530310320021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10042441336967373747093361 7531831002725530310320021)
                ·
                  refine ⟨353054578252759233296251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7531831002725530310320021 353054578252759233296251)
                  ·
                    rfl

theorem cell23_6188142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_6188142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188142 prefixEnd_6188142 := by exact prefixLift 6188142
  have htrace : WordTrace (prefixWord ++ tailWord_6188142) baseStart_6188142 baseEnd_6188142 := by
    simpa [prefixWord, tailWord_6188142, baseEnd_6188142] using wordTrace_append hprefix tailTrace_6188142
  have hstable : (prefixWord ++ tailWord_6188142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188142).length < 2 ^ (prefixWord ++ tailWord_6188142).sum := by decide
  have hdescent : baseEnd_6188142 < baseStart_6188142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188186 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6188186 : Nat := 118140960795 + 6188186 * 2 ^ 59
def prefixEnd_6188186 : Nat := 4983230072969 + 3 ^ 40 * 6188186 * 2
def baseEnd_6188186 : Nat := 3177513797423630927516057

theorem tailTrace_6188186 : CollatzResearch.WordTrace tailWord_6188186 prefixEnd_6188186 3177513797423630927516057 := by
  unfold tailWord_6188186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56425421389816613718286103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150467790372844303248762941 56425421389816613718286103)
  ·
    refine ⟨84638132084724920577429155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56425421389816613718286103 84638132084724920577429155)
    ·
      refine ⟨126957198127087380866143733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84638132084724920577429155 126957198127087380866143733)
      ·
        refine ⟨11902237324414441956200975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126957198127087380866143733 11902237324414441956200975)
        ·
          refine ⟨17853355986621662934301463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902237324414441956200975 17853355986621662934301463)
          ·
            refine ⟨26780033979932494401452195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17853355986621662934301463 26780033979932494401452195)
            ·
              refine ⟨40170050969898741602178293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26780033979932494401452195 40170050969898741602178293)
              ·
                refine ⟨3765942278428007025204215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40170050969898741602178293 3765942278428007025204215)
                ·
                  refine ⟨5648913417642010537806323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765942278428007025204215 5648913417642010537806323)
                  ·
                    refine ⟨8473370126463015806709485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648913417642010537806323 8473370126463015806709485)
                    ·
                      refine ⟨3177513797423630927516057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8473370126463015806709485 3177513797423630927516057)
                      ·
                        rfl

theorem cell23_6188186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6188186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188186 prefixEnd_6188186 := by exact prefixLift 6188186
  have htrace : WordTrace (prefixWord ++ tailWord_6188186) baseStart_6188186 baseEnd_6188186 := by
    simpa [prefixWord, tailWord_6188186, baseEnd_6188186] using wordTrace_append hprefix tailTrace_6188186
  have hstable : (prefixWord ++ tailWord_6188186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188186).length < 2 ^ (prefixWord ++ tailWord_6188186).sum := by decide
  have hdescent : baseEnd_6188186 < baseStart_6188186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188192 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_6188192 : Nat := 118140960795 + 6188192 * 2 ^ 59
def prefixEnd_6188192 : Nat := 4983230072969 + 3 ^ 40 * 6188192 * 2
def baseEnd_6188192 : Nat := 3177516878307557904041029

theorem tailTrace_6188192 : CollatzResearch.WordTrace tailWord_6188192 prefixEnd_6188192 3177516878307557904041029 := by
  unfold tailWord_6188192
  simp only [CollatzResearch.WordTrace]
  refine ⟨112850952198622358948931415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150467936264829811931908553 112850952198622358948931415)
  ·
    refine ⟨169276428297933538423397123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112850952198622358948931415 169276428297933538423397123)
    ·
      refine ⟨253914642446900307635095685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169276428297933538423397123 253914642446900307635095685)
      ·
        refine ⟨47608995458793807681580441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253914642446900307635095685 47608995458793807681580441)
        ·
          refine ⟨35706746594095355761185331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47608995458793807681580441 35706746594095355761185331)
          ·
            refine ⟨53560119891143033641777997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35706746594095355761185331 53560119891143033641777997)
            ·
              refine ⟨20085044959178637615666749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53560119891143033641777997 20085044959178637615666749)
              ·
                refine ⟨7531891859691989105875031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20085044959178637615666749 7531891859691989105875031)
                ·
                  refine ⟨11297837789537983658812547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531891859691989105875031 11297837789537983658812547)
                  ·
                    refine ⟨16946756684306975488218821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11297837789537983658812547 16946756684306975488218821)
                    ·
                      refine ⟨3177516878307557904041029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16946756684306975488218821 3177516878307557904041029)
                      ·
                        rfl

theorem cell23_6188192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_6188192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188192 prefixEnd_6188192 := by exact prefixLift 6188192
  have htrace : WordTrace (prefixWord ++ tailWord_6188192) baseStart_6188192 baseEnd_6188192 := by
    simpa [prefixWord, tailWord_6188192, baseEnd_6188192] using wordTrace_append hprefix tailTrace_6188192
  have hstable : (prefixWord ++ tailWord_6188192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188192).length < 2 ^ (prefixWord ++ tailWord_6188192).sum := by decide
  have hdescent : baseEnd_6188192 < baseStart_6188192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188222 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6188222 : Nat := 118140960795 + 6188222 * 2 ^ 59
def prefixEnd_6188222 : Nat := 4983230072969 + 3 ^ 40 * 6188222 * 2
def baseEnd_6188222 : Nat := 3177532282727192786665891

theorem tailTrace_6188222 : CollatzResearch.WordTrace tailWord_6188222 prefixEnd_6188222 3177532282727192786665891 := by
  unfold tailWord_6188222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212874823392004127681865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150468665724757355347636613 28212874823392004127681865)
  ·
    refine ⟨21159656117544003095761399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28212874823392004127681865 21159656117544003095761399)
    ·
      refine ⟨31739484176316004643642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159656117544003095761399 31739484176316004643642099)
      ·
        refine ⟨47609226264474006965463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739484176316004643642099 47609226264474006965463149)
        ·
          refine ⟨17853459849177752612048681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47609226264474006965463149 17853459849177752612048681)
          ·
            refine ⟨13390094886883314459036511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17853459849177752612048681 13390094886883314459036511)
            ·
              refine ⟨20085142330324971688554767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390094886883314459036511 20085142330324971688554767)
              ·
                refine ⟨30127713495487457532832151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20085142330324971688554767 30127713495487457532832151)
                ·
                  refine ⟨45191570243231186299248227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30127713495487457532832151 45191570243231186299248227)
                  ·
                    refine ⟨67787355364846779448872341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45191570243231186299248227 67787355364846779448872341)
                    ·
                      refine ⟨3177532282727192786665891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67787355364846779448872341 3177532282727192786665891)
                      ·
                        rfl

theorem cell23_6188222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6188222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188222 prefixEnd_6188222 := by exact prefixLift 6188222
  have htrace : WordTrace (prefixWord ++ tailWord_6188222) baseStart_6188222 baseEnd_6188222 := by
    simpa [prefixWord, tailWord_6188222, baseEnd_6188222] using wordTrace_append hprefix tailTrace_6188222
  have hstable : (prefixWord ++ tailWord_6188222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188222).length < 2 ^ (prefixWord ++ tailWord_6188222).sum := by decide
  have hdescent : baseEnd_6188222 < baseStart_6188222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188237 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6188237 : Nat := 118140960795 + 6188237 * 2 ^ 59
def prefixEnd_6188237 : Nat := 4983230072969 + 3 ^ 40 * 6188237 * 2
def baseEnd_6188237 : Nat := 3177539984937010227978323

theorem tailTrace_6188237 : CollatzResearch.WordTrace tailWord_6188237 prefixEnd_6188237 3177539984937010227978323 := by
  unfold tailWord_6188237
  simp only [CollatzResearch.WordTrace]
  refine ⟨225703545682081690583250965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150469030454721127055500643 225703545682081690583250965)
  ·
    refine ⟨10579853703847579246089889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225703545682081690583250965 10579853703847579246089889)
    ·
      refine ⟨7934890277885684434567417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10579853703847579246089889 7934890277885684434567417)
      ·
        refine ⟨5951167708414263325925563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7934890277885684434567417 5951167708414263325925563)
        ·
          refine ⟨8926751562621394988888345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951167708414263325925563 8926751562621394988888345)
          ·
            refine ⟨6695063671966046241666259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8926751562621394988888345 6695063671966046241666259)
            ·
              refine ⟨10042595507949069362499389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695063671966046241666259 10042595507949069362499389)
              ·
                refine ⟨3765973315480901010937271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10042595507949069362499389 3765973315480901010937271)
                ·
                  refine ⟨5648959973221351516405907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765973315480901010937271 5648959973221351516405907)
                  ·
                    refine ⟨8473439959832027274608861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5648959973221351516405907 8473439959832027274608861)
                    ·
                      refine ⟨3177539984937010227978323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8473439959832027274608861 3177539984937010227978323)
                      ·
                        rfl

theorem cell23_6188237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6188237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188237 prefixEnd_6188237 := by exact prefixLift 6188237
  have htrace : WordTrace (prefixWord ++ tailWord_6188237) baseStart_6188237 baseEnd_6188237 := by
    simpa [prefixWord, tailWord_6188237, baseEnd_6188237] using wordTrace_append hprefix tailTrace_6188237
  have hstable : (prefixWord ++ tailWord_6188237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188237).length < 2 ^ (prefixWord ++ tailWord_6188237).sum := by decide
  have hdescent : baseEnd_6188237 < baseStart_6188237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188242 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6188242 : Nat := 118140960795 + 6188242 * 2 ^ 59
def prefixEnd_6188242 : Nat := 4983230072969 + 3 ^ 40 * 6188242 * 2
def baseEnd_6188242 : Nat := 3177542552340282708415799

theorem tailTrace_6188242 : CollatzResearch.WordTrace tailWord_6188242 prefixEnd_6188242 3177542552340282708415799 := by
  unfold tailWord_6188242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56425932011765894109295745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150469152031375717624788653 56425932011765894109295745)
  ·
    refine ⟨42319449008824420581971809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56425932011765894109295745 42319449008824420581971809)
    ·
      refine ⟨31739586756618315436478857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42319449008824420581971809 31739586756618315436478857)
      ·
        refine ⟨23804690067463736577359143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31739586756618315436478857 23804690067463736577359143)
        ·
          refine ⟨35707035101195604866038715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23804690067463736577359143 35707035101195604866038715)
          ·
            refine ⟨53560552651793407299058073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35707035101195604866038715 53560552651793407299058073)
            ·
              refine ⟨40170414488845055474293555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53560552651793407299058073 40170414488845055474293555)
              ·
                refine ⟨60255621733267583211440333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40170414488845055474293555 60255621733267583211440333)
                ·
                  refine ⟨22595858149975343704290125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60255621733267583211440333 22595858149975343704290125)
                  ·
                    refine ⟨8473446806240753889108797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22595858149975343704290125 8473446806240753889108797)
                    ·
                      refine ⟨3177542552340282708415799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8473446806240753889108797 3177542552340282708415799)
                      ·
                        rfl

theorem cell23_6188242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6188242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188242 prefixEnd_6188242 := by exact prefixLift 6188242
  have htrace : WordTrace (prefixWord ++ tailWord_6188242) baseStart_6188242 baseEnd_6188242 := by
    simpa [prefixWord, tailWord_6188242, baseEnd_6188242] using wordTrace_append hprefix tailTrace_6188242
  have hstable : (prefixWord ++ tailWord_6188242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188242).length < 2 ^ (prefixWord ++ tailWord_6188242).sum := by decide
  have hdescent : baseEnd_6188242 < baseStart_6188242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188246 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6188246 : Nat := 118140960795 + 6188246 * 2 ^ 59
def prefixEnd_6188246 : Nat := 4983230072969 + 3 ^ 40 * 6188246 * 2
def baseEnd_6188246 : Nat := 3177544606262900692765781

theorem tailTrace_6188246 : CollatzResearch.WordTrace tailWord_6188246 prefixEnd_6188246 3177544606262900692765781 := by
  unfold tailWord_6188246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106492121190567820020537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150469249292699390080219061 14106492121190567820020537)
  ·
    refine ⟨10579869090892925865015403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14106492121190567820020537 10579869090892925865015403)
    ·
      refine ⟨15869803636339388797523105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579869090892925865015403 15869803636339388797523105)
      ·
        refine ⟨11902352727254541598142329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15869803636339388797523105 11902352727254541598142329)
        ·
          refine ⟨8926764545440906198606747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11902352727254541598142329 8926764545440906198606747)
          ·
            refine ⟨13390146818161359297910121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926764545440906198606747 13390146818161359297910121)
            ·
              refine ⟨10042610113621019473432591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13390146818161359297910121 10042610113621019473432591)
              ·
                refine ⟨15063915170431529210148887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10042610113621019473432591 15063915170431529210148887)
                ·
                  refine ⟨22595872755647293815223331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15063915170431529210148887 22595872755647293815223331)
                  ·
                    refine ⟨33893809133470940722834997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22595872755647293815223331 33893809133470940722834997)
                    ·
                      refine ⟨3177544606262900692765781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33893809133470940722834997 3177544606262900692765781)
                      ·
                        rfl

theorem cell23_6188246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6188246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188246 prefixEnd_6188246 := by exact prefixLift 6188246
  have htrace : WordTrace (prefixWord ++ tailWord_6188246) baseStart_6188246 baseEnd_6188246 := by
    simpa [prefixWord, tailWord_6188246, baseEnd_6188246] using wordTrace_append hprefix tailTrace_6188246
  have hstable : (prefixWord ++ tailWord_6188246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188246).length < 2 ^ (prefixWord ++ tailWord_6188246).sum := by decide
  have hdescent : baseEnd_6188246 < baseStart_6188246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188286 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_6188286 : Nat := 118140960795 + 6188286 * 2 ^ 59
def prefixEnd_6188286 : Nat := 4983230072969 + 3 ^ 40 * 6188286 * 2
def baseEnd_6188286 : Nat := 3177565145489080536265597

theorem tailTrace_6188286 : CollatzResearch.WordTrace tailWord_6188286 prefixEnd_6188286 3177565145489080536265597 := by
  unfold tailWord_6188286
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213166607363021493973089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150470221905936114634523141 28213166607363021493973089)
  ·
    refine ⟨21159874955522266120479817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28213166607363021493973089 21159874955522266120479817)
    ·
      refine ⟨15869906216641699590359863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21159874955522266120479817 15869906216641699590359863)
      ·
        refine ⟨23804859324962549385539795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15869906216641699590359863 23804859324962549385539795)
        ·
          refine ⟨35707288987443824078309693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23804859324962549385539795 35707288987443824078309693)
          ·
            refine ⟨13390233370291434029366135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35707288987443824078309693 13390233370291434029366135)
            ·
              refine ⟨20085350055437151044049203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390233370291434029366135 20085350055437151044049203)
              ·
                refine ⟨30128025083155726566073805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20085350055437151044049203 30128025083155726566073805)
                ·
                  refine ⟨11298009406183397462277677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30128025083155726566073805 11298009406183397462277677)
                  ·
                    refine ⟨4236753527318774048354129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11298009406183397462277677 4236753527318774048354129)
                    ·
                      refine ⟨3177565145489080536265597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236753527318774048354129 3177565145489080536265597)
                      ·
                        rfl

theorem cell23_6188286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_6188286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188286 prefixEnd_6188286 := by exact prefixLift 6188286
  have htrace : WordTrace (prefixWord ++ tailWord_6188286) baseStart_6188286 baseEnd_6188286 := by
    simpa [prefixWord, tailWord_6188286, baseEnd_6188286] using wordTrace_append hprefix tailTrace_6188286
  have hstable : (prefixWord ++ tailWord_6188286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188286).length < 2 ^ (prefixWord ++ tailWord_6188286).sum := by decide
  have hdescent : baseEnd_6188286 < baseStart_6188286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188299 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 4, 2]
def baseStart_6188299 : Nat := 118140960795 + 6188299 * 2 ^ 59
def prefixEnd_6188299 : Nat := 4983230072969 + 3 ^ 40 * 6188299 * 2
def baseEnd_6188299 : Nat := 3177571820737588985403037

theorem tailTrace_6188299 : CollatzResearch.WordTrace tailWord_6188299 prefixEnd_6188299 3177571820737588985403037 := by
  unfold tailWord_6188299
  simp only [CollatzResearch.WordTrace]
  refine ⟨225705807007857075172007951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150470538005238050114671967 225705807007857075172007951)
  ·
    refine ⟨338558710511785612758011927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225705807007857075172007951 338558710511785612758011927)
    ·
      refine ⟨507838065767678419137017891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338558710511785612758011927 507838065767678419137017891)
      ·
        refine ⟨761757098651517628705526837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507838065767678419137017891 761757098651517628705526837)
        ·
          refine ⟨71414727998579777691143141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 761757098651517628705526837 71414727998579777691143141)
          ·
            refine ⟨13390261499733708317089339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71414727998579777691143141 13390261499733708317089339)
            ·
              refine ⟨20085392249600562475634009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390261499733708317089339 20085392249600562475634009)
              ·
                refine ⟨15064044187200421856725507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20085392249600562475634009 15064044187200421856725507)
                ·
                  refine ⟨22596066280800632785088261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15064044187200421856725507 22596066280800632785088261)
                  ·
                    refine ⟨4236762427650118647204049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22596066280800632785088261 4236762427650118647204049)
                    ·
                      refine ⟨3177571820737588985403037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236762427650118647204049 3177571820737588985403037)
                      ·
                        rfl

theorem cell23_6188299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4, 2].length) (baseStart_6188299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188299 prefixEnd_6188299 := by exact prefixLift 6188299
  have htrace : WordTrace (prefixWord ++ tailWord_6188299) baseStart_6188299 baseEnd_6188299 := by
    simpa [prefixWord, tailWord_6188299, baseEnd_6188299] using wordTrace_append hprefix tailTrace_6188299
  have hstable : (prefixWord ++ tailWord_6188299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188299).length < 2 ^ (prefixWord ++ tailWord_6188299).sum := by decide
  have hdescent : baseEnd_6188299 < baseStart_6188299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188302 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6188302 : Nat := 118140960795 + 6188302 * 2 ^ 59
def prefixEnd_6188302 : Nat := 4983230072969 + 3 ^ 40 * 6188302 * 2
def baseEnd_6188302 : Nat := 3177573361179552473665523

theorem tailTrace_6188302 : CollatzResearch.WordTrace tailWord_6188302 prefixEnd_6188302 3177573361179552473665523 := by
  unfold tailWord_6188302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213239553355775835545895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150470610951230804456244773 28213239553355775835545895)
  ·
    refine ⟨42319859330033663753318843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28213239553355775835545895 42319859330033663753318843)
    ·
      refine ⟨63479788995050495629978265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42319859330033663753318843 63479788995050495629978265)
      ·
        refine ⟨47609841746287871722483699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63479788995050495629978265 47609841746287871722483699)
        ·
          refine ⟨71414762619431807583725549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47609841746287871722483699 71414762619431807583725549)
          ·
            refine ⟨26780535982286927843897081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71414762619431807583725549 26780535982286927843897081)
            ·
              refine ⟨20085401986715195882922811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26780535982286927843897081 20085401986715195882922811)
              ·
                refine ⟨30128102980072793824384217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20085401986715195882922811 30128102980072793824384217)
                ·
                  refine ⟨22596077235054595368288163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30128102980072793824384217 22596077235054595368288163)
                  ·
                    refine ⟨33894115852581893052432245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22596077235054595368288163 33894115852581893052432245)
                    ·
                      refine ⟨3177573361179552473665523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33894115852581893052432245 3177573361179552473665523)
                      ·
                        rfl

theorem cell23_6188302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6188302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188302 prefixEnd_6188302 := by exact prefixLift 6188302
  have htrace : WordTrace (prefixWord ++ tailWord_6188302) baseStart_6188302 baseEnd_6188302 := by
    simpa [prefixWord, tailWord_6188302, baseEnd_6188302] using wordTrace_append hprefix tailTrace_6188302
  have hstable : (prefixWord ++ tailWord_6188302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188302).length < 2 ^ (prefixWord ++ tailWord_6188302).sum := by decide
  have hdescent : baseEnd_6188302 < baseStart_6188302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188316 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6188316 : Nat := 118140960795 + 6188316 * 2 ^ 59
def prefixEnd_6188316 : Nat := 4983230072969 + 3 ^ 40 * 6188316 * 2
def baseEnd_6188316 : Nat := 3177580549908715418890459

theorem tailTrace_6188316 : CollatzResearch.WordTrace tailWord_6188316 prefixEnd_6188316 3177580549908715418890459 := by
  unfold tailWord_6188316
  simp only [CollatzResearch.WordTrace]
  refine ⟨112853213524397743537688401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150470951365863658050251201 112853213524397743537688401)
  ·
    refine ⟨84639910143298307653266301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112853213524397743537688401 84639910143298307653266301)
    ·
      refine ⟨31739966303736865369974863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84639910143298307653266301 31739966303736865369974863)
      ·
        refine ⟨47609949455605298054962295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739966303736865369974863 47609949455605298054962295)
        ·
          refine ⟨71414924183407947082443443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47609949455605298054962295 71414924183407947082443443)
          ·
            refine ⟨107122386275111920623665165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71414924183407947082443443 107122386275111920623665165)
            ·
              refine ⟨40170894853166970233874437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107122386275111920623665165 40170894853166970233874437)
              ·
                refine ⟨7532042784968806918851457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40170894853166970233874437 7532042784968806918851457)
                ·
                  refine ⟨5649032088726605189138593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7532042784968806918851457 5649032088726605189138593)
                  ·
                    refine ⟨4236774066544953891853945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649032088726605189138593 4236774066544953891853945)
                    ·
                      refine ⟨3177580549908715418890459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236774066544953891853945 3177580549908715418890459)
                      ·
                        rfl

theorem cell23_6188316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6188316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188316 prefixEnd_6188316 := by exact prefixLift 6188316
  have htrace : WordTrace (prefixWord ++ tailWord_6188316) baseStart_6188316 baseEnd_6188316 := by
    simpa [prefixWord, tailWord_6188316, baseEnd_6188316] using wordTrace_append hprefix tailTrace_6188316
  have hstable : (prefixWord ++ tailWord_6188316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188316).length < 2 ^ (prefixWord ++ tailWord_6188316).sum := by decide
  have hdescent : baseEnd_6188316 < baseStart_6188316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188333 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6188333 : Nat := 118140960795 + 6188333 * 2 ^ 59
def prefixEnd_6188333 : Nat := 4983230072969 + 3 ^ 40 * 6188333 * 2
def baseEnd_6188333 : Nat := 3177589279079841852377881

theorem tailTrace_6188333 : CollatzResearch.WordTrace tailWord_6188333 prefixEnd_6188333 3177589279079841852377881 := by
  unfold tailWord_6188333
  simp only [CollatzResearch.WordTrace]
  refine ⟨225707047089733898978745653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150471364726489265985830435 225707047089733898978745653)
  ·
    refine ⟨21160035664662553029257405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225707047089733898978745653 21160035664662553029257405)
    ·
      refine ⟨7935013374248457385971527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21160035664662553029257405 7935013374248457385971527)
      ·
        refine ⟨11902520061372686078957291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935013374248457385971527 11902520061372686078957291)
        ·
          refine ⟨17853780092059029118435937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902520061372686078957291 17853780092059029118435937)
          ·
            refine ⟨13390335069044271838826953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17853780092059029118435937 13390335069044271838826953)
            ·
              refine ⟨10042751301783203879120215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13390335069044271838826953 10042751301783203879120215)
              ·
                refine ⟨15064126952674805818680323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10042751301783203879120215 15064126952674805818680323)
                ·
                  refine ⟨22596190429012208728020485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15064126952674805818680323 22596190429012208728020485)
                  ·
                    refine ⟨4236785705439789136503841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22596190429012208728020485 4236785705439789136503841)
                    ·
                      refine ⟨3177589279079841852377881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236785705439789136503841 3177589279079841852377881)
                      ·
                        rfl

theorem cell23_6188333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6188333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188333 prefixEnd_6188333 := by exact prefixLift 6188333
  have htrace : WordTrace (prefixWord ++ tailWord_6188333) baseStart_6188333 baseEnd_6188333 := by
    simpa [prefixWord, tailWord_6188333, baseEnd_6188333] using wordTrace_append hprefix tailTrace_6188333
  have hstable : (prefixWord ++ tailWord_6188333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188333).length < 2 ^ (prefixWord ++ tailWord_6188333).sum := by decide
  have hdescent : baseEnd_6188333 < baseStart_6188333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188335 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 7]
def baseStart_6188335 : Nat := 118140960795 + 6188335 * 2 ^ 59
def prefixEnd_6188335 : Nat := 4983230072969 + 3 ^ 40 * 6188335 * 2
def baseEnd_6188335 : Nat := 1059196768680383614850957

theorem tailTrace_6188335 : CollatzResearch.WordTrace tailWord_6188335 prefixEnd_6188335 1059196768680383614850957 := by
  unfold tailWord_6188335
  simp only [CollatzResearch.WordTrace]
  refine ⟨225707120035726653320318459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150471413357151102213545639 225707120035726653320318459)
  ·
    refine ⟨338560680053589979980477689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225707120035726653320318459 338560680053589979980477689)
    ·
      refine ⟨253920510040192484985358267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338560680053589979980477689 253920510040192484985358267)
      ·
        refine ⟨380880765060288727478037401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253920510040192484985358267 380880765060288727478037401)
        ·
          refine ⟨285660573795216545608528051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380880765060288727478037401 285660573795216545608528051)
          ·
            refine ⟨428490860692824818412792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285660573795216545608528051 428490860692824818412792077)
            ·
              refine ⟨160684072759809306904797029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428490860692824818412792077 160684072759809306904797029)
              ·
                refine ⟨30128263642464245044649443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160684072759809306904797029 30128263642464245044649443)
                ·
                  refine ⟨45192395463696367566974165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30128263642464245044649443 45192395463696367566974165)
                  ·
                    refine ⟨1059196768680383614850957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45192395463696367566974165 1059196768680383614850957)
                    ·
                      rfl

theorem cell23_6188335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_6188335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188335 prefixEnd_6188335 := by exact prefixLift 6188335
  have htrace : WordTrace (prefixWord ++ tailWord_6188335) baseStart_6188335 baseEnd_6188335 := by
    simpa [prefixWord, tailWord_6188335, baseEnd_6188335] using wordTrace_append hprefix tailTrace_6188335
  have hstable : (prefixWord ++ tailWord_6188335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188335).length < 2 ^ (prefixWord ++ tailWord_6188335).sum := by decide
  have hdescent : baseEnd_6188335 < baseStart_6188335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188356 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 5]
def baseStart_6188356 : Nat := 118140960795 + 6188356 * 2 ^ 59
def prefixEnd_6188356 : Nat := 4983230072969 + 3 ^ 40 * 6188356 * 2
def baseEnd_6188356 : Nat := 353066787681655029154475

theorem tailTrace_6188356 : CollatzResearch.WordTrace tailWord_6188356 prefixEnd_6188356 353066787681655029154475 := by
  unfold tailWord_6188356
  simp only [CollatzResearch.WordTrace]
  refine ⟨112853942984325286953416461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150471923979100382604555281 112853942984325286953416461)
  ·
    refine ⟨42320228619121982607531173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112853942984325286953416461 42320228619121982607531173)
    ·
      refine ⟨7935042866085371738912095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42320228619121982607531173 7935042866085371738912095)
      ·
        refine ⟨11902564299128057608368143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935042866085371738912095 11902564299128057608368143)
        ·
          refine ⟨17853846448692086412552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902564299128057608368143 17853846448692086412552215)
          ·
            refine ⟨26780769673038129618828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17853846448692086412552215 26780769673038129618828323)
            ·
              refine ⟨40171154509557194428242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26780769673038129618828323 40171154509557194428242485)
              ·
                refine ⟨3766045735270986977647733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40171154509557194428242485 3766045735270986977647733)
                ·
                  refine ⟨353066787681655029154475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766045735270986977647733 353066787681655029154475)
                  ·
                    rfl

theorem cell23_6188356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_6188356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188356 prefixEnd_6188356 := by exact prefixLift 6188356
  have htrace : WordTrace (prefixWord ++ tailWord_6188356) baseStart_6188356 baseEnd_6188356 := by
    simpa [prefixWord, tailWord_6188356, baseEnd_6188356] using wordTrace_append hprefix tailTrace_6188356
  have hstable : (prefixWord ++ tailWord_6188356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188356).length < 2 ^ (prefixWord ++ tailWord_6188356).sum := by decide
  have hdescent : baseEnd_6188356 < baseStart_6188356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188389 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_6188389 : Nat := 118140960795 + 6188389 * 2 ^ 59
def prefixEnd_6188389 : Nat := 4983230072969 + 3 ^ 40 * 6188389 * 2
def baseEnd_6188389 : Nat := 3177618033996493633277623

theorem tailTrace_6188389 : CollatzResearch.WordTrace tailWord_6188389 prefixEnd_6188389 3177618033996493633277623 := by
  unfold tailWord_6188389
  simp only [CollatzResearch.WordTrace]
  refine ⟨225709089577531020542784221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150472726385020680361856147 225709089577531020542784221)
  ·
    refine ⟨84640908591574132703544083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225709089577531020542784221 84640908591574132703544083)
    ·
      refine ⟨126961362887361199055316125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84640908591574132703544083 126961362887361199055316125)
      ·
        refine ⟨47610511082760449645743547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126961362887361199055316125 47610511082760449645743547)
        ·
          refine ⟨71415766624140674468615321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47610511082760449645743547 71415766624140674468615321)
          ·
            refine ⟨53561824968105505851461491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71415766624140674468615321 53561824968105505851461491)
            ·
              refine ⟨80342737452158258777192237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53561824968105505851461491 80342737452158258777192237)
              ·
                refine ⟨30128526544559347041447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80342737452158258777192237 30128526544559347041447089)
                ·
                  refine ⟨22596394908419510281085317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30128526544559347041447089 22596394908419510281085317)
                  ·
                    refine ⟨4236824045328658177703497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22596394908419510281085317 4236824045328658177703497)
                    ·
                      refine ⟨3177618033996493633277623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236824045328658177703497 3177618033996493633277623)
                      ·
                        rfl

theorem cell23_6188389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_6188389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188389 prefixEnd_6188389 := by exact prefixLift 6188389
  have htrace : WordTrace (prefixWord ++ tailWord_6188389) baseStart_6188389 baseEnd_6188389 := by
    simpa [prefixWord, tailWord_6188389, baseEnd_6188389] using wordTrace_append hprefix tailTrace_6188389
  have hstable : (prefixWord ++ tailWord_6188389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188389).length < 2 ^ (prefixWord ++ tailWord_6188389).sum := by decide
  have hdescent : baseEnd_6188389 < baseStart_6188389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188395 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 12]
def baseStart_6188395 : Nat := 118140960795 + 6188395 * 2 ^ 59
def prefixEnd_6188395 : Nat := 4983230072969 + 3 ^ 40 * 6188395 * 2
def baseEnd_6188395 : Nat := 353069012764491178866955

theorem tailTrace_6188395 : CollatzResearch.WordTrace tailWord_6188395 prefixEnd_6188395 353069012764491178866955 := by
  unfold tailWord_6188395
  simp only [CollatzResearch.WordTrace]
  refine ⟨225709308415509283567502639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150472872277006189045001759 225709308415509283567502639)
  ·
    refine ⟨338563962623263925351253959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225709308415509283567502639 338563962623263925351253959)
    ·
      refine ⟨507845943934895888026880939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338563962623263925351253959 507845943934895888026880939)
      ·
        refine ⟨761768915902343832040321409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507845943934895888026880939 761768915902343832040321409)
        ·
          refine ⟨571326686926757874030241057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761768915902343832040321409 571326686926757874030241057)
          ·
            refine ⟨428495015195068405522680793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571326686926757874030241057 428495015195068405522680793)
            ·
              refine ⟨321371261396301304142010595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428495015195068405522680793 321371261396301304142010595)
              ·
                refine ⟨482056892094451956213015893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321371261396301304142010595 482056892094451956213015893)
                ·
                  refine ⟨353069012764491178866955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 482056892094451956213015893 353069012764491178866955)
                  ·
                    rfl

theorem cell23_6188395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_6188395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188395 prefixEnd_6188395 := by exact prefixLift 6188395
  have htrace : WordTrace (prefixWord ++ tailWord_6188395) baseStart_6188395 baseEnd_6188395 := by
    simpa [prefixWord, tailWord_6188395, baseEnd_6188395] using wordTrace_append hprefix tailTrace_6188395
  have hstable : (prefixWord ++ tailWord_6188395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188395).length < 2 ^ (prefixWord ++ tailWord_6188395).sum := by decide
  have hdescent : baseEnd_6188395 < baseStart_6188395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188402 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6188402 : Nat := 118140960795 + 6188402 * 2 ^ 59
def prefixEnd_6188402 : Nat := 4983230072969 + 3 ^ 40 * 6188402 * 2
def baseEnd_6188402 : Nat := 3177624709245002082415063

theorem tailTrace_6188402 : CollatzResearch.WordTrace tailWord_6188402 prefixEnd_6188402 3177624709245002082415063 := by
  unfold tailWord_6188402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56427390931620980940751865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150473042484322615842004973 56427390931620980940751865)
  ·
    refine ⟨42320543198715735705563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56427390931620980940751865 42320543198715735705563899)
    ·
      refine ⟨63480814798073603558345849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42320543198715735705563899 63480814798073603558345849)
      ·
        refine ⟨47610611098555202668759387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63480814798073603558345849 47610611098555202668759387)
        ·
          refine ⟨71415916647832804003139081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47610611098555202668759387 71415916647832804003139081)
          ·
            refine ⟨53561937485874603002354311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71415916647832804003139081 53561937485874603002354311)
            ·
              refine ⟨80342906228811904503531467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53561937485874603002354311 80342906228811904503531467)
              ·
                refine ⟨120514359343217856755297201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80342906228811904503531467 120514359343217856755297201)
                ·
                  refine ⟨90385769507413392566472901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120514359343217856755297201 90385769507413392566472901)
                  ·
                    refine ⟨16947331782640011106213669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90385769507413392566472901 16947331782640011106213669)
                    ·
                      refine ⟨3177624709245002082415063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16947331782640011106213669 3177624709245002082415063)
                      ·
                        rfl

theorem cell23_6188402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6188402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188402 prefixEnd_6188402 := by exact prefixLift 6188402
  have htrace : WordTrace (prefixWord ++ tailWord_6188402) baseStart_6188402 baseEnd_6188402 := by
    simpa [prefixWord, tailWord_6188402, baseEnd_6188402] using wordTrace_append hprefix tailTrace_6188402
  have hstable : (prefixWord ++ tailWord_6188402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188402).length < 2 ^ (prefixWord ++ tailWord_6188402).sum := by decide
  have hdescent : baseEnd_6188402 < baseStart_6188402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188472 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_6188472 : Nat := 118140960795 + 6188472 * 2 ^ 59
def prefixEnd_6188472 : Nat := 4983230072969 + 3 ^ 40 * 6188472 * 2
def baseEnd_6188472 : Nat := 1059220217630272269513247

theorem tailTrace_6188472 : CollatzResearch.WordTrace tailWord_6188472 prefixEnd_6188472 1059220217630272269513247 := by
  unfold tailWord_6188472
  simp only [CollatzResearch.WordTrace]
  refine ⟨112856058418115162859027835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150474744557486883812037113 112856058418115162859027835)
  ·
    refine ⟨169284087627172744288541753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112856058418115162859027835 169284087627172744288541753)
    ·
      refine ⟨126963065720379558216406315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169284087627172744288541753 126963065720379558216406315)
      ·
        refine ⟨190444598580569337324609473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126963065720379558216406315 190444598580569337324609473)
        ·
          refine ⟨142833448935427002993457105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190444598580569337324609473 142833448935427002993457105)
          ·
            refine ⟨107125086701570252245092829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142833448935427002993457105 107125086701570252245092829)
            ·
              refine ⟨40171907513088844591909811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107125086701570252245092829 40171907513088844591909811)
              ·
                refine ⟨60257861269633266887864717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40171907513088844591909811 60257861269633266887864717)
                ·
                  refine ⟨22596697976112475082949269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60257861269633266887864717 22596697976112475082949269)
                  ·
                    refine ⟨1059220217630272269513247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22596697976112475082949269 1059220217630272269513247)
                    ·
                      rfl

theorem cell23_6188472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_6188472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188472 prefixEnd_6188472 := by exact prefixLift 6188472
  have htrace : WordTrace (prefixWord ++ tailWord_6188472) baseStart_6188472 baseEnd_6188472 := by
    simpa [prefixWord, tailWord_6188472, baseEnd_6188472] using wordTrace_append hprefix tailTrace_6188472
  have hstable : (prefixWord ++ tailWord_6188472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188472).length < 2 ^ (prefixWord ++ tailWord_6188472).sum := by decide
  have hdescent : baseEnd_6188472 < baseStart_6188472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_6188479 : Nat := 118140960795 + 6188479 * 2 ^ 59
def prefixEnd_6188479 : Nat := 4983230072969 + 3 ^ 40 * 6188479 * 2
def baseEnd_6188479 : Nat := 3177664247255398281152209

theorem tailTrace_6188479 : CollatzResearch.WordTrace tailWord_6188479 prefixEnd_6188479 3177664247255398281152209 := by
  unfold tailWord_6188479
  simp only [CollatzResearch.WordTrace]
  refine ⟨225712372147204965913560491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150474914764803310609040327 225712372147204965913560491)
  ·
    refine ⟨338568558220807448870340737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225712372147204965913560491 338568558220807448870340737)
    ·
      refine ⟨253926418665605586652755553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338568558220807448870340737 253926418665605586652755553)
      ·
        refine ⟨190444813999204189989566665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253926418665605586652755553 190444813999204189989566665)
        ·
          refine ⟨142833610499403142492174999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190444813999204189989566665 142833610499403142492174999)
          ·
            refine ⟨214250415749104713738262499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142833610499403142492174999 214250415749104713738262499)
            ·
              refine ⟨321375623623657070607393749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214250415749104713738262499 321375623623657070607393749)
              ·
                refine ⟨7532241178679462592360791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 321375623623657070607393749 7532241178679462592360791)
                ·
                  refine ⟨11298361768019193888541187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532241178679462592360791 11298361768019193888541187)
                  ·
                    refine ⟨16947542652028790832811781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11298361768019193888541187 16947542652028790832811781)
                    ·
                      refine ⟨3177664247255398281152209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16947542652028790832811781 3177664247255398281152209)
                      ·
                        rfl

theorem cell23_6188479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_6188479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188479 prefixEnd_6188479 := by exact prefixLift 6188479
  have htrace : WordTrace (prefixWord ++ tailWord_6188479) baseStart_6188479 baseEnd_6188479 := by
    simpa [prefixWord, tailWord_6188479, baseEnd_6188479] using wordTrace_append hprefix tailTrace_6188479
  have hstable : (prefixWord ++ tailWord_6188479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188479).length < 2 ^ (prefixWord ++ tailWord_6188479).sum := by decide
  have hdescent : baseEnd_6188479 < baseStart_6188479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188490 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_6188490 : Nat := 118140960795 + 6188490 * 2 ^ 59
def prefixEnd_6188490 : Nat := 4983230072969 + 3 ^ 40 * 6188490 * 2
def baseEnd_6188490 : Nat := 3177669895542597738114659

theorem tailTrace_6188490 : CollatzResearch.WordTrace tailWord_6188490 prefixEnd_6188490 3177669895542597738114659 := by
  unfold tailWord_6188490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428193337541278698052731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150475182233443409861473949 56428193337541278698052731)
  ·
    refine ⟨84642290006311918047079097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428193337541278698052731 84642290006311918047079097)
    ·
      refine ⟨63481717504733938535309323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84642290006311918047079097 63481717504733938535309323)
      ·
        refine ⟨95222576257100907802963985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63481717504733938535309323 95222576257100907802963985)
        ·
          refine ⟨71416932192825680852222989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95222576257100907802963985 71416932192825680852222989)
          ·
            refine ⟨26781349572309630319583621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71416932192825680852222989 26781349572309630319583621)
            ·
              refine ⟨5021503044808055684921929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26781349572309630319583621 5021503044808055684921929)
              ·
                refine ⟨3766127283606041763691447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021503044808055684921929 3766127283606041763691447)
                ·
                  refine ⟨5649190925409062645537171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766127283606041763691447 5649190925409062645537171)
                  ·
                    refine ⟨8473786388113593968305757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5649190925409062645537171 8473786388113593968305757)
                    ·
                      refine ⟨3177669895542597738114659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8473786388113593968305757 3177669895542597738114659)
                      ·
                        rfl

theorem cell23_6188490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_6188490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188490 prefixEnd_6188490 := by exact prefixLift 6188490
  have htrace : WordTrace (prefixWord ++ tailWord_6188490) baseStart_6188490 baseEnd_6188490 := by
    simpa [prefixWord, tailWord_6188490, baseEnd_6188490] using wordTrace_append hprefix tailTrace_6188490
  have hstable : (prefixWord ++ tailWord_6188490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188490).length < 2 ^ (prefixWord ++ tailWord_6188490).sum := by decide
  have hdescent : baseEnd_6188490 < baseStart_6188490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188506 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_6188506 : Nat := 118140960795 + 6188506 * 2 ^ 59
def prefixEnd_6188506 : Nat := 4983230072969 + 3 ^ 40 * 6188506 * 2
def baseEnd_6188506 : Nat := 1059226037077689891838195

theorem tailTrace_6188506 : CollatzResearch.WordTrace tailWord_6188506 prefixEnd_6188506 1059226037077689891838195 := by
  unfold tailWord_6188506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428339229526787381198343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150475571278738099683195581 56428339229526787381198343)
  ·
    refine ⟨84642508844290181071797515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428339229526787381198343 84642508844290181071797515)
    ·
      refine ⟨126963763266435271607696273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84642508844290181071797515 126963763266435271607696273)
      ·
        refine ⟨95222822449826453705772205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126963763266435271607696273 95222822449826453705772205)
        ·
          refine ⟨35708558418684920139664577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95222822449826453705772205 35708558418684920139664577)
          ·
            refine ⟨26781418814013690104748433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35708558418684920139664577 26781418814013690104748433)
            ·
              refine ⟨20086064110510267578561325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26781418814013690104748433 20086064110510267578561325)
              ·
                refine ⟨7532274041441350341960497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20086064110510267578561325 7532274041441350341960497)
                ·
                  refine ⟨5649205531081012756470373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7532274041441350341960497 5649205531081012756470373)
                  ·
                    refine ⟨1059226037077689891838195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5649205531081012756470373 1059226037077689891838195)
                    ·
                      rfl

theorem cell23_6188506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_6188506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188506 prefixEnd_6188506 := by exact prefixLift 6188506
  have htrace : WordTrace (prefixWord ++ tailWord_6188506) baseStart_6188506 baseEnd_6188506 := by
    simpa [prefixWord, tailWord_6188506, baseEnd_6188506] using wordTrace_append hprefix tailTrace_6188506
  have hstable : (prefixWord ++ tailWord_6188506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188506).length < 2 ^ (prefixWord ++ tailWord_6188506).sum := by decide
  have hdescent : baseEnd_6188506 < baseStart_6188506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188513 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_6188513 : Nat := 118140960795 + 6188513 * 2 ^ 59
def prefixEnd_6188513 : Nat := 4983230072969 + 3 ^ 40 * 6188513 * 2
def baseEnd_6188513 : Nat := 3177681705597651148127053

theorem tailTrace_6188513 : CollatzResearch.WordTrace tailWord_6188513 prefixEnd_6188513 3177681705597651148127053 := by
  unfold tailWord_6188513
  simp only [CollatzResearch.WordTrace]
  refine ⟨225713612229081789720298193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150475741486054526480198795 225713612229081789720298193)
  ·
    refine ⟨169285209171811342290223645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225713612229081789720298193 169285209171811342290223645)
    ·
      refine ⟨63481953439429253358833867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169285209171811342290223645 63481953439429253358833867)
      ·
        refine ⟨95222930159143880038250801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63481953439429253358833867 95222930159143880038250801)
        ·
          refine ⟨71417197619357910028688101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95222930159143880038250801 71417197619357910028688101)
          ·
            refine ⟨13390724553629608130379019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71417197619357910028688101 13390724553629608130379019)
            ·
              refine ⟨20086086830444412195568529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390724553629608130379019 20086086830444412195568529)
              ·
                refine ⟨15064565122833309146676397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20086086830444412195568529 15064565122833309146676397)
                ·
                  refine ⟨5649211921062490930003649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15064565122833309146676397 5649211921062490930003649)
                  ·
                    refine ⟨4236908940796868197502737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649211921062490930003649 4236908940796868197502737)
                    ·
                      refine ⟨3177681705597651148127053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236908940796868197502737 3177681705597651148127053)
                      ·
                        rfl

theorem cell23_6188513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_6188513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188513 prefixEnd_6188513 := by exact prefixLift 6188513
  have htrace : WordTrace (prefixWord ++ tailWord_6188513) baseStart_6188513 baseEnd_6188513 := by
    simpa [prefixWord, tailWord_6188513, baseEnd_6188513] using wordTrace_append hprefix tailTrace_6188513
  have hstable : (prefixWord ++ tailWord_6188513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188513).length < 2 ^ (prefixWord ++ tailWord_6188513).sum := by decide
  have hdescent : baseEnd_6188513 < baseStart_6188513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188530 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6188530 : Nat := 118140960795 + 6188530 * 2 ^ 59
def prefixEnd_6188530 : Nat := 4983230072969 + 3 ^ 40 * 6188530 * 2
def baseEnd_6188530 : Nat := 3177690434768777581614475

theorem tailTrace_6188530 : CollatzResearch.WordTrace tailWord_6188530 prefixEnd_6188530 3177690434768777581614475 := by
  unfold tailWord_6188530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428558067505050405916761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150476154846680134415778029 56428558067505050405916761)
  ·
    refine ⟨42321418550628787804437571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56428558067505050405916761 42321418550628787804437571)
    ·
      refine ⟨63482127825943181706656357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42321418550628787804437571 63482127825943181706656357)
      ·
        refine ⟨11902898967364346569998067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63482127825943181706656357 11902898967364346569998067)
        ·
          refine ⟨17854348451046519854997101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902898967364346569998067 17854348451046519854997101)
          ·
            refine ⟨6695380669142444945623913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17854348451046519854997101 6695380669142444945623913)
            ·
              refine ⟨5021535501856833709217935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695380669142444945623913 5021535501856833709217935)
              ·
                refine ⟨7532303252785250563826903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021535501856833709217935 7532303252785250563826903)
                ·
                  refine ⟨11298454879177875845740355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532303252785250563826903 11298454879177875845740355)
                  ·
                    refine ⟨16947682318766813768610533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11298454879177875845740355 16947682318766813768610533)
                    ·
                      refine ⟨3177690434768777581614475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16947682318766813768610533 3177690434768777581614475)
                      ·
                        rfl

theorem cell23_6188530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6188530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188530 prefixEnd_6188530 := by exact prefixLift 6188530
  have htrace : WordTrace (prefixWord ++ tailWord_6188530) baseStart_6188530 baseEnd_6188530 := by
    simpa [prefixWord, tailWord_6188530, baseEnd_6188530] using wordTrace_append hprefix tailTrace_6188530
  have hstable : (prefixWord ++ tailWord_6188530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188530).length < 2 ^ (prefixWord ++ tailWord_6188530).sum := by decide
  have hdescent : baseEnd_6188530 < baseStart_6188530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188557 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6188557 : Nat := 118140960795 + 6188557 * 2 ^ 59
def prefixEnd_6188557 : Nat := 4983230072969 + 3 ^ 40 * 6188557 * 2
def baseEnd_6188557 : Nat := 1059234766248816325325617

theorem tailTrace_6188557 : CollatzResearch.WordTrace tailWord_6188557 prefixEnd_6188557 1059234766248816325325617 := by
  unfold tailWord_6188557
  simp only [CollatzResearch.WordTrace]
  refine ⟨225715217040922385234899925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150476811360614923489933283 225715217040922385234899925)
  ·
    refine ⟨5290200399396618403942967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 225715217040922385234899925 5290200399396618403942967)
    ·
      refine ⟨7935300599094927605914451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290200399396618403942967 7935300599094927605914451)
      ·
        refine ⟨11902950898642391408871677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935300599094927605914451 11902950898642391408871677)
        ·
          refine ⟨4463606586990896778326879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11902950898642391408871677 4463606586990896778326879)
          ·
            refine ⟨6695409880486345167490319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463606586990896778326879 6695409880486345167490319)
            ·
              refine ⟨10043114820729517751235479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695409880486345167490319 10043114820729517751235479)
              ·
                refine ⟨15064672231094276626853219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043114820729517751235479 15064672231094276626853219)
                ·
                  refine ⟨22597008346641414940279829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15064672231094276626853219 22597008346641414940279829)
                  ·
                    refine ⟨1059234766248816325325617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22597008346641414940279829 1059234766248816325325617)
                    ·
                      rfl

theorem cell23_6188557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6188557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188557 prefixEnd_6188557 := by exact prefixLift 6188557
  have htrace : WordTrace (prefixWord ++ tailWord_6188557) baseStart_6188557 baseEnd_6188557 := by
    simpa [prefixWord, tailWord_6188557, baseEnd_6188557] using wordTrace_append hprefix tailTrace_6188557
  have hstable : (prefixWord ++ tailWord_6188557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188557).length < 2 ^ (prefixWord ++ tailWord_6188557).sum := by decide
  have hdescent : baseEnd_6188557 < baseStart_6188557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188590 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6188590 : Nat := 118140960795 + 6188590 * 2 ^ 59
def prefixEnd_6188590 : Nat := 4983230072969 + 3 ^ 40 * 6188590 * 2
def baseEnd_6188590 : Nat := 3177721243608047346864199

theorem tailTrace_6188590 : CollatzResearch.WordTrace tailWord_6188590 prefixEnd_6188590 3177721243608047346864199 := by
  unfold tailWord_6188590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214552581225353983856403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150477613766535221247234149 28214552581225353983856403)
  ·
    refine ⟨42321828871838030975784605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28214552581225353983856403 42321828871838030975784605)
    ·
      refine ⟨15870685826939261615919227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42321828871838030975784605 15870685826939261615919227)
      ·
        refine ⟨23806028740408892423878841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870685826939261615919227 23806028740408892423878841)
        ·
          refine ⟨17854521555306669317909131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23806028740408892423878841 17854521555306669317909131)
          ·
            refine ⟨26781782332960003976863697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854521555306669317909131 26781782332960003976863697)
            ·
              refine ⟨20086336749720002982647773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26781782332960003976863697 20086336749720002982647773)
              ·
                refine ⟨7532376281145001118492915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20086336749720002982647773 7532376281145001118492915)
                ·
                  refine ⟨11298564421717501677739373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532376281145001118492915 11298564421717501677739373)
                  ·
                    refine ⟨4236961658144063129152265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11298564421717501677739373 4236961658144063129152265)
                    ·
                      refine ⟨3177721243608047346864199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236961658144063129152265 3177721243608047346864199)
                      ·
                        rfl

theorem cell23_6188590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6188590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188590 prefixEnd_6188590 := by exact prefixLift 6188590
  have htrace : WordTrace (prefixWord ++ tailWord_6188590) baseStart_6188590 baseEnd_6188590 := by
    simpa [prefixWord, tailWord_6188590, baseEnd_6188590] using wordTrace_append hprefix tailTrace_6188590
  have hstable : (prefixWord ++ tailWord_6188590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188590).length < 2 ^ (prefixWord ++ tailWord_6188590).sum := by decide
  have hdescent : baseEnd_6188590 < baseStart_6188590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188619 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3]
def baseStart_6188619 : Nat := 118140960795 + 6188619 * 2 ^ 59
def prefixEnd_6188619 : Nat := 4983230072969 + 3 ^ 40 * 6188619 * 2
def baseEnd_6188619 : Nat := 3177736134547027733401565

theorem tailTrace_6188619 : CollatzResearch.WordTrace tailWord_6188619 prefixEnd_6188619 3177736134547027733401565 := by
  unfold tailWord_6188619
  simp only [CollatzResearch.WordTrace]
  refine ⟨225717478366697769823656911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150478318911131846549104607 225717478366697769823656911)
  ·
    refine ⟨338576217550046654735485367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225717478366697769823656911 338576217550046654735485367)
    ·
      refine ⟨507864326325069982103228051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338576217550046654735485367 507864326325069982103228051)
      ·
        refine ⟨761796489487604973154842077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507864326325069982103228051 761796489487604973154842077)
        ·
          refine ⟨285673683557851864933065779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761796489487604973154842077 285673683557851864933065779)
          ·
            refine ⟨428510525336777797399598669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285673683557851864933065779 428510525336777797399598669)
            ·
              refine ⟨160691447001291674024849501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428510525336777797399598669 160691447001291674024849501)
              ·
                refine ⟨60259292625484377759318563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160691447001291674024849501 60259292625484377759318563)
                ·
                  refine ⟨90388938938226566638977845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60259292625484377759318563 90388938938226566638977845)
                  ·
                    refine ⟨8473963025458740622404173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90388938938226566638977845 8473963025458740622404173)
                    ·
                      refine ⟨3177736134547027733401565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8473963025458740622404173 3177736134547027733401565)
                      ·
                        rfl

theorem cell23_6188619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].length) (baseStart_6188619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188619 prefixEnd_6188619 := by exact prefixLift 6188619
  have htrace : WordTrace (prefixWord ++ tailWord_6188619) baseStart_6188619 baseEnd_6188619 := by
    simpa [prefixWord, tailWord_6188619, baseEnd_6188619] using wordTrace_append hprefix tailTrace_6188619
  have hstable : (prefixWord ++ tailWord_6188619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188619).length < 2 ^ (prefixWord ++ tailWord_6188619).sum := by decide
  have hdescent : baseEnd_6188619 < baseStart_6188619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188620 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6188620 : Nat := 118140960795 + 6188620 * 2 ^ 59
def prefixEnd_6188620 : Nat := 4983230072969 + 3 ^ 40 * 6188620 * 2
def baseEnd_6188620 : Nat := 3177736648027682229489061

theorem tailTrace_6188620 : CollatzResearch.WordTrace tailWord_6188620 prefixEnd_6188620 3177736648027682229489061 := by
  unfold tailWord_6188620
  simp only [CollatzResearch.WordTrace]
  refine ⟨112858757419847073497221657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150478343226462764662962209 112858757419847073497221657)
  ·
    refine ⟨84644068064885305122916243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112858757419847073497221657 84644068064885305122916243)
    ·
      refine ⟨126966102097327957684374365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84644068064885305122916243 126966102097327957684374365)
      ·
        refine ⟨47612288286497984131640387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126966102097327957684374365 47612288286497984131640387)
        ·
          refine ⟨71418432429746976197460581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47612288286497984131640387 71418432429746976197460581)
          ·
            refine ⟨13390956080577558037023859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71418432429746976197460581 13390956080577558037023859)
            ·
              refine ⟨20086434120866337055535789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390956080577558037023859 20086434120866337055535789)
              ·
                refine ⟨7532412795324876395825921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20086434120866337055535789 7532412795324876395825921)
                ·
                  refine ⟨5649309596493657296869441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7532412795324876395825921 5649309596493657296869441)
                  ·
                    refine ⟨4236982197370242972652081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649309596493657296869441 4236982197370242972652081)
                    ·
                      refine ⟨3177736648027682229489061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236982197370242972652081 3177736648027682229489061)
                      ·
                        rfl

theorem cell23_6188620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6188620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188620 prefixEnd_6188620 := by exact prefixLift 6188620
  have htrace : WordTrace (prefixWord ++ tailWord_6188620) baseStart_6188620 baseEnd_6188620 := by
    simpa [prefixWord, tailWord_6188620, baseEnd_6188620] using wordTrace_append hprefix tailTrace_6188620
  have hstable : (prefixWord ++ tailWord_6188620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188620).length < 2 ^ (prefixWord ++ tailWord_6188620).sum := by decide
  have hdescent : baseEnd_6188620 < baseStart_6188620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188637 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6188637 : Nat := 118140960795 + 6188637 * 2 ^ 59
def prefixEnd_6188637 : Nat := 4983230072969 + 3 ^ 40 * 6188637 * 2
def baseEnd_6188637 : Nat := 3177745377198808662976483

theorem tailTrace_6188637 : CollatzResearch.WordTrace tailWord_6188637 prefixEnd_6188637 3177745377198808662976483 := by
  unfold tailWord_6188637
  simp only [CollatzResearch.WordTrace]
  refine ⟨225718134880632558897812165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150478756587088372598541443 225718134880632558897812165)
  ·
    refine ⟨42322150290118604793339781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225718134880632558897812165 42322150290118604793339781)
    ·
      refine ⟨7935403179397238398751209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42322150290118604793339781 7935403179397238398751209)
      ·
        refine ⟨5951552384547928799063407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7935403179397238398751209 5951552384547928799063407)
        ·
          refine ⟨8927328576821893198595111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951552384547928799063407 8927328576821893198595111)
          ·
            refine ⟨13390992865232839797892667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8927328576821893198595111 13390992865232839797892667)
            ·
              refine ⟨20086489297849259696839001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390992865232839797892667 20086489297849259696839001)
              ·
                refine ⟨15064866973386944772629251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20086489297849259696839001 15064866973386944772629251)
                ·
                  refine ⟨22597300460080417158943877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15064866973386944772629251 22597300460080417158943877)
                  ·
                    refine ⟨4236993836265078217301977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22597300460080417158943877 4236993836265078217301977)
                    ·
                      refine ⟨3177745377198808662976483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4236993836265078217301977 3177745377198808662976483)
                      ·
                        rfl

theorem cell23_6188637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6188637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188637 prefixEnd_6188637 := by exact prefixLift 6188637
  have htrace : WordTrace (prefixWord ++ tailWord_6188637) baseStart_6188637 baseEnd_6188637 := by
    simpa [prefixWord, tailWord_6188637, baseEnd_6188637] using wordTrace_append hprefix tailTrace_6188637
  have hstable : (prefixWord ++ tailWord_6188637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188637).length < 2 ^ (prefixWord ++ tailWord_6188637).sum := by decide
  have hdescent : baseEnd_6188637 < baseStart_6188637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188649 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_6188649 : Nat := 118140960795 + 6188649 * 2 ^ 59
def prefixEnd_6188649 : Nat := 4983230072969 + 3 ^ 40 * 6188649 * 2
def baseEnd_6188649 : Nat := 3177751538966662616026427

theorem tailTrace_6188649 : CollatzResearch.WordTrace tailWord_6188649 prefixEnd_6188649 3177751538966662616026427 := by
  unfold tailWord_6188649
  simp only [CollatzResearch.WordTrace]
  refine ⟨225718572556589084947249001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150479048371059389964832667 225718572556589084947249001)
  ·
    refine ⟨169288929417441813710436751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225718572556589084947249001 169288929417441813710436751)
    ·
      refine ⟨253933394126162720565655127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169288929417441813710436751 253933394126162720565655127)
      ·
        refine ⟨380900091189244080848482691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253933394126162720565655127 380900091189244080848482691)
        ·
          refine ⟨571350136783866121272724037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380900091189244080848482691 571350136783866121272724037)
          ·
            refine ⟨107128150646974897738635757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571350136783866121272724037 107128150646974897738635757)
            ·
              refine ⟨40173056492615586651988409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107128150646974897738635757 40173056492615586651988409)
              ·
                refine ⟨30129792369461689988991307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40173056492615586651988409 30129792369461689988991307)
                ·
                  refine ⟨45194688554192534983486961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30129792369461689988991307 45194688554192534983486961)
                  ·
                    refine ⟨33896016415644401237615221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45194688554192534983486961 33896016415644401237615221)
                    ·
                      refine ⟨3177751538966662616026427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33896016415644401237615221 3177751538966662616026427)
                      ·
                        rfl

theorem cell23_6188649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_6188649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188649 prefixEnd_6188649 := by exact prefixLift 6188649
  have htrace : WordTrace (prefixWord ++ tailWord_6188649) baseStart_6188649 baseEnd_6188649 := by
    simpa [prefixWord, tailWord_6188649, baseEnd_6188649] using wordTrace_append hprefix tailTrace_6188649
  have hstable : (prefixWord ++ tailWord_6188649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188649).length < 2 ^ (prefixWord ++ tailWord_6188649).sum := by decide
  have hdescent : baseEnd_6188649 < baseStart_6188649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188656 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_6188656 : Nat := 118140960795 + 6188656 * 2 ^ 59
def prefixEnd_6188656 : Nat := 4983230072969 + 3 ^ 40 * 6188656 * 2
def baseEnd_6188656 : Nat := 1059251711110414696212965

theorem tailTrace_6188656 : CollatzResearch.WordTrace tailWord_6188656 prefixEnd_6188656 1059251711110414696212965 := by
  unfold tailWord_6188656
  simp only [CollatzResearch.WordTrace]
  refine ⟨112859413933781862571376911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150479218578375816761835881 112859413933781862571376911)
  ·
    refine ⟨169289120900672793857065367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112859413933781862571376911 169289120900672793857065367)
    ·
      refine ⟨253933681351009190785598051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169289120900672793857065367 253933681351009190785598051)
      ·
        refine ⟨380900522026513786178397077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253933681351009190785598051 380900522026513786178397077)
        ·
          refine ⟨17854711969992833727112363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380900522026513786178397077 17854711969992833727112363)
          ·
            refine ⟨26782067954989250590668545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854711969992833727112363 26782067954989250590668545)
            ·
              refine ⟨20086550966241937943001409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26782067954989250590668545 20086550966241937943001409)
              ·
                refine ⟨15064913224681453457251057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20086550966241937943001409 15064913224681453457251057)
                ·
                  refine ⟨11298684918511090092938293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15064913224681453457251057 11298684918511090092938293)
                  ·
                    refine ⟨1059251711110414696212965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11298684918511090092938293 1059251711110414696212965)
                    ·
                      rfl

theorem cell23_6188656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_6188656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188656 prefixEnd_6188656 := by exact prefixLift 6188656
  have htrace : WordTrace (prefixWord ++ tailWord_6188656) baseStart_6188656 baseEnd_6188656 := by
    simpa [prefixWord, tailWord_6188656, baseEnd_6188656] using wordTrace_append hprefix tailTrace_6188656
  have hstable : (prefixWord ++ tailWord_6188656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188656).length < 2 ^ (prefixWord ++ tailWord_6188656).sum := by decide
  have hdescent : baseEnd_6188656 < baseStart_6188656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188689 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_6188689 : Nat := 118140960795 + 6188689 * 2 ^ 59
def prefixEnd_6188689 : Nat := 4983230072969 + 3 ^ 40 * 6188689 * 2
def baseEnd_6188689 : Nat := 3177772078192842459526243

theorem tailTrace_6188689 : CollatzResearch.WordTrace tailWord_6188689 prefixEnd_6188689 3177772078192842459526243 := by
  unfold tailWord_6188689
  simp only [CollatzResearch.WordTrace]
  refine ⟨225720031476444171778705121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150480020984296114519136747 225720031476444171778705121)
  ·
    refine ⟨169290023607333128834028841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225720031476444171778705121 169290023607333128834028841)
    ·
      refine ⟨126967517705499846625521631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169290023607333128834028841 126967517705499846625521631)
      ·
        refine ⟨190451276558249769938282447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126967517705499846625521631 190451276558249769938282447)
        ·
          refine ⟨285676914837374654907423671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190451276558249769938282447 285676914837374654907423671)
          ·
            refine ⟨428515372256061982361135507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285676914837374654907423671 428515372256061982361135507)
            ·
              refine ⟨642773058384092973541703261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428515372256061982361135507 642773058384092973541703261)
              ·
                refine ⟨241039896894034865078138723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642773058384092973541703261 241039896894034865078138723)
                ·
                  refine ⟨361559845341052297617208085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241039896894034865078138723 361559845341052297617208085)
                  ·
                    refine ⟨16948117750361826450806629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 361559845341052297617208085 16948117750361826450806629)
                    ·
                      refine ⟨3177772078192842459526243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16948117750361826450806629 3177772078192842459526243)
                      ·
                        rfl

theorem cell23_6188689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_6188689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188689 prefixEnd_6188689 := by exact prefixLift 6188689
  have htrace : WordTrace (prefixWord ++ tailWord_6188689) baseStart_6188689 baseEnd_6188689 := by
    simpa [prefixWord, tailWord_6188689, baseEnd_6188689] using wordTrace_append hprefix tailTrace_6188689
  have hstable : (prefixWord ++ tailWord_6188689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188689).length < 2 ^ (prefixWord ++ tailWord_6188689).sum := by decide
  have hdescent : baseEnd_6188689 < baseStart_6188689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188690 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_6188690 : Nat := 118140960795 + 6188690 * 2 ^ 59
def prefixEnd_6188690 : Nat := 4983230072969 + 3 ^ 40 * 6188690 * 2
def baseEnd_6188690 : Nat := 1059257530557832318537913

theorem tailTrace_6188690 : CollatzResearch.WordTrace tailWord_6188690 prefixEnd_6188690 1059257530557832318537913 := by
  unfold tailWord_6188690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56430016987360137237372881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150480045299627032632994349 56430016987360137237372881)
  ·
    refine ⟨42322512740520102928029661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56430016987360137237372881 42322512740520102928029661)
    ·
      refine ⟨15870942277695038598011123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42322512740520102928029661 15870942277695038598011123)
      ·
        refine ⟨23806413416542557897016685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870942277695038598011123 23806413416542557897016685)
        ·
          refine ⟨8927405031203459211381257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23806413416542557897016685 8927405031203459211381257)
          ·
            refine ⟨6695553773402594408535943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8927405031203459211381257 6695553773402594408535943)
            ·
              refine ⟨10043330660103891612803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695553773402594408535943 10043330660103891612803915)
              ·
                refine ⟨15064995990155837419205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043330660103891612803915 15064995990155837419205873)
                ·
                  refine ⟨11298746992616878064404405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15064995990155837419205873 11298746992616878064404405)
                  ·
                    refine ⟨1059257530557832318537913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11298746992616878064404405 1059257530557832318537913)
                    ·
                      rfl

theorem cell23_6188690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_6188690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188690 prefixEnd_6188690 := by exact prefixLift 6188690
  have htrace : WordTrace (prefixWord ++ tailWord_6188690) baseStart_6188690 baseEnd_6188690 := by
    simpa [prefixWord, tailWord_6188690, baseEnd_6188690] using wordTrace_append hprefix tailTrace_6188690
  have hstable : (prefixWord ++ tailWord_6188690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188690).length < 2 ^ (prefixWord ++ tailWord_6188690).sum := by decide
  have hdescent : baseEnd_6188690 < baseStart_6188690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188719 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_6188719 : Nat := 118140960795 + 6188719 * 2 ^ 59
def prefixEnd_6188719 : Nat := 4983230072969 + 3 ^ 40 * 6188719 * 2
def baseEnd_6188719 : Nat := 3177787482612477342151105

theorem tailTrace_6188719 : CollatzResearch.WordTrace tailWord_6188719 prefixEnd_6188719 3177787482612477342151105 := by
  unfold tailWord_6188719
  simp only [CollatzResearch.WordTrace]
  refine ⟨225721125666335486902297211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150480750444223657934864807 225721125666335486902297211)
  ·
    refine ⟨338581688499503230353445817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225721125666335486902297211 338581688499503230353445817)
    ·
      refine ⟨253936266374627422765084363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338581688499503230353445817 253936266374627422765084363)
      ·
        refine ⟨380904399561941134147626545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253936266374627422765084363 380904399561941134147626545)
        ·
          refine ⟨285678299671455850610719909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380904399561941134147626545 285678299671455850610719909)
          ·
            refine ⟨53564681188397971989509983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285678299671455850610719909 53564681188397971989509983)
            ·
              refine ⟨80347021782596957984264975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53564681188397971989509983 80347021782596957984264975)
              ·
                refine ⟨120520532673895436976397463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80347021782596957984264975 120520532673895436976397463)
                ·
                  refine ⟨180780799010843155464596195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120520532673895436976397463 180780799010843155464596195)
                  ·
                    refine ⟨271171198516264733196894293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180780799010843155464596195 271171198516264733196894293)
                    ·
                      refine ⟨3177787482612477342151105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271171198516264733196894293 3177787482612477342151105)
                      ·
                        rfl

theorem cell23_6188719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_6188719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188719 prefixEnd_6188719 := by exact prefixLift 6188719
  have htrace : WordTrace (prefixWord ++ tailWord_6188719) baseStart_6188719 baseEnd_6188719 := by
    simpa [prefixWord, tailWord_6188719, baseEnd_6188719] using wordTrace_append hprefix tailTrace_6188719
  have hstable : (prefixWord ++ tailWord_6188719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188719).length < 2 ^ (prefixWord ++ tailWord_6188719).sum := by decide
  have hdescent : baseEnd_6188719 < baseStart_6188719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188733 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 6]
def baseStart_6188733 : Nat := 118140960795 + 6188733 * 2 ^ 59
def prefixEnd_6188733 : Nat := 4983230072969 + 3 ^ 40 * 6188733 * 2
def baseEnd_6188733 : Nat := 353088296815737809708449

theorem tailTrace_6188733 : CollatzResearch.WordTrace tailWord_6188733 prefixEnd_6188733 353088296815737809708449 := by
  unfold tailWord_6188733
  simp only [CollatzResearch.WordTrace]
  refine ⟨225721636288284767293306853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150481090858856511528871235 225721636288284767293306853)
  ·
    refine ⟨42322806804053393867495035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225721636288284767293306853 42322806804053393867495035)
    ·
      refine ⟨63484210206080090801242553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42322806804053393867495035 63484210206080090801242553)
      ·
        refine ⟨47613157654560068100931915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63484210206080090801242553 47613157654560068100931915)
        ·
          refine ⟨71419736481840102151397873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47613157654560068100931915 71419736481840102151397873)
          ·
            refine ⟨53564802361380076613548405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71419736481840102151397873 53564802361380076613548405)
            ·
              refine ⟨5021700221379382182520163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53564802361380076613548405 5021700221379382182520163)
              ·
                refine ⟨7532550332069073273780245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021700221379382182520163 7532550332069073273780245)
                ·
                  refine ⟨353088296815737809708449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7532550332069073273780245 353088296815737809708449)
                  ·
                    rfl

theorem cell23_6188733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_6188733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188733 prefixEnd_6188733 := by exact prefixLift 6188733
  have htrace : WordTrace (prefixWord ++ tailWord_6188733) baseStart_6188733 baseEnd_6188733 := by
    simpa [prefixWord, tailWord_6188733, baseEnd_6188733] using wordTrace_append hprefix tailTrace_6188733
  have hstable : (prefixWord ++ tailWord_6188733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188733).length < 2 ^ (prefixWord ++ tailWord_6188733).sum := by decide
  have hdescent : baseEnd_6188733 < baseStart_6188733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188743 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_6188743 : Nat := 118140960795 + 6188743 * 2 ^ 59
def prefixEnd_6188743 : Nat := 4983230072969 + 3 ^ 40 * 6188743 * 2
def baseEnd_6188743 : Nat := 3177799806148185248250995

theorem tailTrace_6188743 : CollatzResearch.WordTrace tailWord_6188743 prefixEnd_6188743 3177799806148185248250995 := by
  unfold tailWord_6188743
  simp only [CollatzResearch.WordTrace]
  refine ⟨225722001018248539001170883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150481334012165692667447255 225722001018248539001170883)
  ·
    refine ⟨338583001527372808501756325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225722001018248539001170883 338583001527372808501756325)
    ·
      refine ⟨63484312786382401594079311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338583001527372808501756325 63484312786382401594079311)
      ·
        refine ⟨95226469179573602391118967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63484312786382401594079311 95226469179573602391118967)
        ·
          refine ⟨142839703769360403586678451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95226469179573602391118967 142839703769360403586678451)
          ·
            refine ⟨214259555654040605380017677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142839703769360403586678451 214259555654040605380017677)
            ·
              refine ⟨80347333370265227017506629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214259555654040605380017677 80347333370265227017506629)
              ·
                refine ⟨15065125006924730065782493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80347333370265227017506629 15065125006924730065782493)
                ·
                  refine ⟨5649421877596773774668435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15065125006924730065782493 5649421877596773774668435)
                  ·
                    refine ⟨8474132816395160662002653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5649421877596773774668435 8474132816395160662002653)
                    ·
                      refine ⟨3177799806148185248250995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474132816395160662002653 3177799806148185248250995)
                      ·
                        rfl

theorem cell23_6188743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_6188743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188743 prefixEnd_6188743 := by exact prefixLift 6188743
  have htrace : WordTrace (prefixWord ++ tailWord_6188743) baseStart_6188743 baseEnd_6188743 := by
    simpa [prefixWord, tailWord_6188743, baseEnd_6188743] using wordTrace_append hprefix tailTrace_6188743
  have hstable : (prefixWord ++ tailWord_6188743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188743).length < 2 ^ (prefixWord ++ tailWord_6188743).sum := by decide
  have hdescent : baseEnd_6188743 < baseStart_6188743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188753 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_6188753 : Nat := 118140960795 + 6188753 * 2 ^ 59
def prefixEnd_6188753 : Nat := 4983230072969 + 3 ^ 40 * 6188753 * 2
def baseEnd_6188753 : Nat := 3177804940954730209125949

theorem tailTrace_6188753 : CollatzResearch.WordTrace tailWord_6188753 prefixEnd_6188753 3177804940954730209125949 := by
  unfold tailWord_6188753
  simp only [CollatzResearch.WordTrace]
  refine ⟨225722365748212310709034913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150481577165474873806023275 225722365748212310709034913)
  ·
    refine ⟨169291774311159233031776185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225722365748212310709034913 169291774311159233031776185)
    ·
      refine ⟨126968830733369424773832139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169291774311159233031776185 126968830733369424773832139)
      ·
        refine ⟨190453246100054137160748209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126968830733369424773832139 190453246100054137160748209)
        ·
          refine ⟨142839934575040602870561157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190453246100054137160748209 142839934575040602870561157)
          ·
            refine ⟨26782487732820113038230217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142839934575040602870561157 26782487732820113038230217)
            ·
              refine ⟨20086865799615084778672663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26782487732820113038230217 20086865799615084778672663)
              ·
                refine ⟨30130298699422627168008995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20086865799615084778672663 30130298699422627168008995)
                ·
                  refine ⟨45195448049133940752013493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30130298699422627168008995 45195448049133940752013493)
                  ·
                    refine ⟨4237073254606306945501265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45195448049133940752013493 4237073254606306945501265)
                    ·
                      refine ⟨3177804940954730209125949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237073254606306945501265 3177804940954730209125949)
                      ·
                        rfl

theorem cell23_6188753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_6188753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188753 prefixEnd_6188753 := by exact prefixLift 6188753
  have htrace : WordTrace (prefixWord ++ tailWord_6188753) baseStart_6188753 baseEnd_6188753 := by
    simpa [prefixWord, tailWord_6188753, baseEnd_6188753] using wordTrace_append hprefix tailTrace_6188753
  have hstable : (prefixWord ++ tailWord_6188753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188753).length < 2 ^ (prefixWord ++ tailWord_6188753).sum := by decide
  have hdescent : baseEnd_6188753 < baseStart_6188753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188796 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_6188796 : Nat := 118140960795 + 6188796 * 2 ^ 59
def prefixEnd_6188796 : Nat := 4983230072969 + 3 ^ 40 * 6188796 * 2
def baseEnd_6188796 : Nat := 3177827020622873540888251

theorem tailTrace_6188796 : CollatzResearch.WordTrace tailWord_6188796 prefixEnd_6188796 3177827020622873540888251 := by
  unfold tailWord_6188796
  simp only [CollatzResearch.WordTrace]
  refine ⟨112861967043528264526425121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150482622724704352701900161 112861967043528264526425121)
  ·
    refine ⟨84646475282646198394818841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112861967043528264526425121 84646475282646198394818841)
    ·
      refine ⟨63484856461984648796114131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84646475282646198394818841 63484856461984648796114131)
      ·
        refine ⟨95227284692976973194171197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63484856461984648796114131 95227284692976973194171197)
        ·
          refine ⟨35710231759866364947814199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95227284692976973194171197 35710231759866364947814199)
          ·
            refine ⟨53565347639799547421721299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35710231759866364947814199 53565347639799547421721299)
            ·
              refine ⟨80348021459699321132581949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53565347639799547421721299 80348021459699321132581949)
              ·
                refine ⟨30130508047387245424718231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80348021459699321132581949 30130508047387245424718231)
                ·
                  refine ⟨45195762071080868137077347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30130508047387245424718231 45195762071080868137077347)
                  ·
                    refine ⟨67793643106621302205616021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45195762071080868137077347 67793643106621302205616021)
                    ·
                      refine ⟨3177827020622873540888251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67793643106621302205616021 3177827020622873540888251)
                      ·
                        rfl

theorem cell23_6188796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_6188796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188796 prefixEnd_6188796 := by exact prefixLift 6188796
  have htrace : WordTrace (prefixWord ++ tailWord_6188796) baseStart_6188796 baseEnd_6188796 := by
    simpa [prefixWord, tailWord_6188796, baseEnd_6188796] using wordTrace_append hprefix tailTrace_6188796
  have hstable : (prefixWord ++ tailWord_6188796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188796).length < 2 ^ (prefixWord ++ tailWord_6188796).sum := by decide
  have hdescent : baseEnd_6188796 < baseStart_6188796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188817 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_6188817 : Nat := 118140960795 + 6188817 * 2 ^ 59
def prefixEnd_6188817 : Nat := 4983230072969 + 3 ^ 40 * 6188817 * 2
def baseEnd_6188817 : Nat := 3177837803716617958725655

theorem tailTrace_6188817 : CollatzResearch.WordTrace tailWord_6188817 prefixEnd_6188817 3177837803716617958725655 := by
  unfold tailWord_6188817
  simp only [CollatzResearch.WordTrace]
  refine ⟨225724700019980449639364705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150483133346653633092909803 225724700019980449639364705)
  ·
    refine ⟨169293525014985337229523529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225724700019980449639364705 169293525014985337229523529)
    ·
      refine ⟨126970143761239002922142647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169293525014985337229523529 126970143761239002922142647)
      ·
        refine ⟨190455215641858504383213971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126970143761239002922142647 190455215641858504383213971)
        ·
          refine ⟨285682823462787756574820957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190455215641858504383213971 285682823462787756574820957)
          ·
            refine ⟨107131058798545408715557859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285682823462787756574820957 107131058798545408715557859)
            ·
              refine ⟨160696588197818113073336789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107131058798545408715557859 160696588197818113073336789)
              ·
                refine ⟨3766326285886362025156331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160696588197818113073336789 3766326285886362025156331)
                ·
                  refine ⟨5649489428829543037734497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766326285886362025156331 5649489428829543037734497)
                  ·
                    refine ⟨4237117071622157278300873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649489428829543037734497 4237117071622157278300873)
                    ·
                      refine ⟨3177837803716617958725655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237117071622157278300873 3177837803716617958725655)
                      ·
                        rfl

theorem cell23_6188817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_6188817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188817 prefixEnd_6188817 := by exact prefixLift 6188817
  have htrace : WordTrace (prefixWord ++ tailWord_6188817) baseStart_6188817 baseEnd_6188817 := by
    simpa [prefixWord, tailWord_6188817, baseEnd_6188817] using wordTrace_append hprefix tailTrace_6188817
  have hstable : (prefixWord ++ tailWord_6188817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188817).length < 2 ^ (prefixWord ++ tailWord_6188817).sum := by decide
  have hdescent : baseEnd_6188817 < baseStart_6188817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188834 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_6188834 : Nat := 118140960795 + 6188834 * 2 ^ 59
def prefixEnd_6188834 : Nat := 4983230072969 + 3 ^ 40 * 6188834 * 2
def baseEnd_6188834 : Nat := 3177846532887744392213077

theorem tailTrace_6188834 : CollatzResearch.WordTrace tailWord_6188834 prefixEnd_6188834 3177846532887744392213077 := by
  unfold tailWord_6188834
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431330015229715385683389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150483546707279241028489037 56431330015229715385683389)
  ·
    refine ⟨21161748755711143269631271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56431330015229715385683389 21161748755711143269631271)
    ·
      refine ⟨31742623133566714904446907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21161748755711143269631271 31742623133566714904446907)
      ·
        refine ⟨47613934700350072356670361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31742623133566714904446907 47613934700350072356670361)
        ·
          refine ⟨35710451025262554267502771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47613934700350072356670361 35710451025262554267502771)
          ·
            refine ⟨53565676537893831401254157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35710451025262554267502771 53565676537893831401254157)
            ·
              refine ⟨20087128701710186775470309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53565676537893831401254157 20087128701710186775470309)
              ·
                refine ⟨3766336631570660020400683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20087128701710186775470309 3766336631570660020400683)
                ·
                  refine ⟨5649504947355990030601025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766336631570660020400683 5649504947355990030601025)
                  ·
                    refine ⟨4237128710516992522950769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649504947355990030601025 4237128710516992522950769)
                    ·
                      refine ⟨3177846532887744392213077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237128710516992522950769 3177846532887744392213077)
                      ·
                        rfl

theorem cell23_6188834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_6188834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188834 prefixEnd_6188834 := by exact prefixLift 6188834
  have htrace : WordTrace (prefixWord ++ tailWord_6188834) baseStart_6188834 baseEnd_6188834 := by
    simpa [prefixWord, tailWord_6188834, baseEnd_6188834] using wordTrace_append hprefix tailTrace_6188834
  have hstable : (prefixWord ++ tailWord_6188834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188834).length < 2 ^ (prefixWord ++ tailWord_6188834).sum := by decide
  have hdescent : baseEnd_6188834 < baseStart_6188834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188850 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_6188850 : Nat := 118140960795 + 6188850 * 2 ^ 59
def prefixEnd_6188850 : Nat := 4983230072969 + 3 ^ 40 * 6188850 * 2
def baseEnd_6188850 : Nat := 3177854748578216329613003

theorem tailTrace_6188850 : CollatzResearch.WordTrace tailWord_6188850 prefixEnd_6188850 3177854748578216329613003 := by
  unfold tailWord_6188850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431475907215224068829001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150483935752573930850210669 56431475907215224068829001)
  ·
    refine ⟨42323606930411418051621751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56431475907215224068829001 42323606930411418051621751)
    ·
      refine ⟨63485410395617127077432627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42323606930411418051621751 63485410395617127077432627)
      ·
        refine ⟨95228115593425690616148941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63485410395617127077432627 95228115593425690616148941)
        ·
          refine ⟨35710543347534633981055853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95228115593425690616148941 35710543347534633981055853)
          ·
            refine ⟨13391453755325487742895945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35710543347534633981055853 13391453755325487742895945)
            ·
              refine ⟨10043590316494115807171959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13391453755325487742895945 10043590316494115807171959)
              ·
                refine ⟨15065385474741173710757939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043590316494115807171959 15065385474741173710757939)
                ·
                  refine ⟨22598078212111760566136909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15065385474741173710757939 22598078212111760566136909)
                  ·
                    refine ⟨8474279329541910212301341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22598078212111760566136909 8474279329541910212301341)
                    ·
                      refine ⟨3177854748578216329613003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474279329541910212301341 3177854748578216329613003)
                      ·
                        rfl

theorem cell23_6188850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_6188850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188850 prefixEnd_6188850 := by exact prefixLift 6188850
  have htrace : WordTrace (prefixWord ++ tailWord_6188850) baseStart_6188850 baseEnd_6188850 := by
    simpa [prefixWord, tailWord_6188850, baseEnd_6188850] using wordTrace_append hprefix tailTrace_6188850
  have hstable : (prefixWord ++ tailWord_6188850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188850).length < 2 ^ (prefixWord ++ tailWord_6188850).sum := by decide
  have hdescent : baseEnd_6188850 < baseStart_6188850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188860 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_6188860 : Nat := 118140960795 + 6188860 * 2 ^ 59
def prefixEnd_6188860 : Nat := 4983230072969 + 3 ^ 40 * 6188860 * 2
def baseEnd_6188860 : Nat := 3177859883384761290487957

theorem tailTrace_6188860 : CollatzResearch.WordTrace tailWord_6188860 prefixEnd_6188860 3177859883384761290487957 := by
  unfold tailWord_6188860
  simp only [CollatzResearch.WordTrace]
  refine ⟨112863134179412333991590017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150484178905883111988786689 112863134179412333991590017)
  ·
    refine ⟨84647350634559250493692513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112863134179412333991590017 84647350634559250493692513)
    ·
      refine ⟨63485512975919437870269385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84647350634559250493692513 63485512975919437870269385)
      ·
        refine ⟨47614134731939578402702039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63485512975919437870269385 47614134731939578402702039)
        ·
          refine ⟨71421202097909367604053059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47614134731939578402702039 71421202097909367604053059)
          ·
            refine ⟨107131803146864051406079589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71421202097909367604053059 107131803146864051406079589)
            ·
              refine ⟨20087213090037009638639923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107131803146864051406079589 20087213090037009638639923)
              ·
                refine ⟨30130819635055514457959885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20087213090037009638639923 30130819635055514457959885)
                ·
                  refine ⟨11299057363145817921734957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30130819635055514457959885 11299057363145817921734957)
                  ·
                    refine ⟨4237146511179681720650609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11299057363145817921734957 4237146511179681720650609)
                    ·
                      refine ⟨3177859883384761290487957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237146511179681720650609 3177859883384761290487957)
                      ·
                        rfl

theorem cell23_6188860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_6188860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188860 prefixEnd_6188860 := by exact prefixLift 6188860
  have htrace : WordTrace (prefixWord ++ tailWord_6188860) baseStart_6188860 baseEnd_6188860 := by
    simpa [prefixWord, tailWord_6188860, baseEnd_6188860] using wordTrace_append hprefix tailTrace_6188860
  have hstable : (prefixWord ++ tailWord_6188860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188860).length < 2 ^ (prefixWord ++ tailWord_6188860).sum := by decide
  have hdescent : baseEnd_6188860 < baseStart_6188860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188884 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_6188884 : Nat := 118140960795 + 6188884 * 2 ^ 59
def prefixEnd_6188884 : Nat := 4983230072969 + 3 ^ 40 * 6188884 * 2
def baseEnd_6188884 : Nat := 3177872206920469196587847

theorem tailTrace_6188884 : CollatzResearch.WordTrace tailWord_6188884 prefixEnd_6188884 3177872206920469196587847 := by
  unfold tailWord_6188884
  simp only [CollatzResearch.WordTrace]
  refine ⟨112863571855368860041026853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150484762473825146721369137 112863571855368860041026853)
  ·
    refine ⟨21161919722881661257692535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112863571855368860041026853 21161919722881661257692535)
    ·
      refine ⟨31742879584322491886538803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21161919722881661257692535 31742879584322491886538803)
      ·
        refine ⟨47614319376483737829808205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31742879584322491886538803 47614319376483737829808205)
        ·
          refine ⟨17855369766181401686178077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47614319376483737829808205 17855369766181401686178077)
          ·
            refine ⟨6695763662318025632316779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17855369766181401686178077 6695763662318025632316779)
            ·
              refine ⟨10043645493477038448475169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695763662318025632316779 10043645493477038448475169)
              ·
                refine ⟨7532734120107778836356377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10043645493477038448475169 7532734120107778836356377)
                ·
                  refine ⟨5649550590080834127267283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7532734120107778836356377 5649550590080834127267283)
                  ·
                    refine ⟨8474325885121251190900925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5649550590080834127267283 8474325885121251190900925)
                    ·
                      refine ⟨3177872206920469196587847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474325885121251190900925 3177872206920469196587847)
                      ·
                        rfl

theorem cell23_6188884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_6188884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188884 prefixEnd_6188884 := by exact prefixLift 6188884
  have htrace : WordTrace (prefixWord ++ tailWord_6188884) baseStart_6188884 baseEnd_6188884 := by
    simpa [prefixWord, tailWord_6188884, baseEnd_6188884] using wordTrace_append hprefix tailTrace_6188884
  have hstable : (prefixWord ++ tailWord_6188884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188884).length < 2 ^ (prefixWord ++ tailWord_6188884).sum := by decide
  have hdescent : baseEnd_6188884 < baseStart_6188884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188903 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6188903 : Nat := 118140960795 + 6188903 * 2 ^ 59
def prefixEnd_6188903 : Nat := 4983230072969 + 3 ^ 40 * 6188903 * 2
def baseEnd_6188903 : Nat := 3177881963052904622250259

theorem tailTrace_6188903 : CollatzResearch.WordTrace tailWord_6188903 prefixEnd_6188903 3177881963052904622250259 := by
  unfold tailWord_6188903
  simp only [CollatzResearch.WordTrace]
  refine ⟨225727836697668886326995363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150485224465112590884663575 225727836697668886326995363)
  ·
    refine ⟨338591755046503329490493045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225727836697668886326995363 338591755046503329490493045)
    ·
      refine ⟨31742977035609687139733723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338591755046503329490493045 31742977035609687139733723)
      ·
        refine ⟨47614465553414530709600585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31742977035609687139733723 47614465553414530709600585)
        ·
          refine ⟨35710849165060898032200439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47614465553414530709600585 35710849165060898032200439)
          ·
            refine ⟨53566273747591347048300659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35710849165060898032200439 53566273747591347048300659)
            ·
              refine ⟨80349410621387020572450989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53566273747591347048300659 80349410621387020572450989)
              ·
                refine ⟨30131028983020132714669121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80349410621387020572450989 30131028983020132714669121)
                ·
                  refine ⟨22598271737265099536001841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30131028983020132714669121 22598271737265099536001841)
                  ·
                    refine ⟨16948703802948824652001381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22598271737265099536001841 16948703802948824652001381)
                    ·
                      refine ⟨3177881963052904622250259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16948703802948824652001381 3177881963052904622250259)
                      ·
                        rfl

theorem cell23_6188903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6188903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188903 prefixEnd_6188903 := by exact prefixLift 6188903
  have htrace : WordTrace (prefixWord ++ tailWord_6188903) baseStart_6188903 baseEnd_6188903 := by
    simpa [prefixWord, tailWord_6188903, baseEnd_6188903] using wordTrace_append hprefix tailTrace_6188903
  have hstable : (prefixWord ++ tailWord_6188903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188903).length < 2 ^ (prefixWord ++ tailWord_6188903).sum := by decide
  have hdescent : baseEnd_6188903 < baseStart_6188903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188958 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6188958 : Nat := 118140960795 + 6188958 * 2 ^ 59
def prefixEnd_6188958 : Nat := 4983230072969 + 3 ^ 40 * 6188958 * 2
def baseEnd_6188958 : Nat := 3177910204488901907062507

theorem tailTrace_6188958 : CollatzResearch.WordTrace tailWord_6188958 prefixEnd_6188958 3177910204488901907062507 := by
  unfold tailWord_6188958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216230339058703840030941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150486561808313087146831685 28216230339058703840030941)
  ·
    refine ⟨10581086377147013940011603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28216230339058703840030941 10581086377147013940011603)
    ·
      refine ⟨15871629565720520910017405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581086377147013940011603 15871629565720520910017405)
      ·
        refine ⟨5951861087145195341256527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15871629565720520910017405 5951861087145195341256527)
        ·
          refine ⟨8927791630717793011884791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951861087145195341256527 8927791630717793011884791)
          ·
            refine ⟨13391687446076689517827187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8927791630717793011884791 13391687446076689517827187)
            ·
              refine ⟨20087531169115034276740781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13391687446076689517827187 20087531169115034276740781)
              ·
                refine ⟨7532824188418137853777793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20087531169115034276740781 7532824188418137853777793)
                ·
                  refine ⟨5649618141313603390333345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7532824188418137853777793 5649618141313603390333345)
                  ·
                    refine ⟨4237213605985202542750009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649618141313603390333345 4237213605985202542750009)
                    ·
                      refine ⟨3177910204488901907062507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237213605985202542750009 3177910204488901907062507)
                      ·
                        rfl

theorem cell23_6188958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6188958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188958 prefixEnd_6188958 := by exact prefixLift 6188958
  have htrace : WordTrace (prefixWord ++ tailWord_6188958) baseStart_6188958 baseEnd_6188958 := by
    simpa [prefixWord, tailWord_6188958, baseEnd_6188958] using wordTrace_append hprefix tailTrace_6188958
  have hstable : (prefixWord ++ tailWord_6188958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188958).length < 2 ^ (prefixWord ++ tailWord_6188958).sum := by decide
  have hdescent : baseEnd_6188958 < baseStart_6188958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6188963 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4]
def baseStart_6188963 : Nat := 118140960795 + 6188963 * 2 ^ 59
def prefixEnd_6188963 : Nat := 4983230072969 + 3 ^ 40 * 6188963 * 2
def baseEnd_6188963 : Nat := 3177912771892174387499983

theorem tailTrace_6188963 : CollatzResearch.WordTrace tailWord_6188963 prefixEnd_6188963 3177912771892174387499983 := by
  unfold tailWord_6188963
  simp only [CollatzResearch.WordTrace]
  refine ⟨225730025077451516574179543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150486683384967677716119695 225730025077451516574179543)
  ·
    refine ⟨338595037616177274861269315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225730025077451516574179543 338595037616177274861269315)
    ·
      refine ⟨507892556424265912291903973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338595037616177274861269315 507892556424265912291903973)
      ·
        refine ⟨95229854329549858554731995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 507892556424265912291903973 95229854329549858554731995)
        ·
          refine ⟨142844781494324787832097993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95229854329549858554731995 142844781494324787832097993)
          ·
            refine ⟨107133586120743590874073495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142844781494324787832097993 107133586120743590874073495)
            ·
              refine ⟨160700379181115386311110243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107133586120743590874073495 160700379181115386311110243)
              ·
                refine ⟨241050568771673079466665365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160700379181115386311110243 241050568771673079466665365)
                ·
                  refine ⟨11299245411172175599999939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241050568771673079466665365 11299245411172175599999939)
                  ·
                    refine ⟨16948868116758263399999909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11299245411172175599999939 16948868116758263399999909)
                    ·
                      refine ⟨3177912771892174387499983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16948868116758263399999909 3177912771892174387499983)
                      ·
                        rfl

theorem cell23_6188963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_6188963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6188963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6188963 prefixEnd_6188963 := by exact prefixLift 6188963
  have htrace : WordTrace (prefixWord ++ tailWord_6188963) baseStart_6188963 baseEnd_6188963 := by
    simpa [prefixWord, tailWord_6188963, baseEnd_6188963] using wordTrace_append hprefix tailTrace_6188963
  have hstable : (prefixWord ++ tailWord_6188963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6188963).length < 2 ^ (prefixWord ++ tailWord_6188963).sum := by decide
  have hdescent : baseEnd_6188963 < baseStart_6188963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6188963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189007 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 1, 4]
def baseStart_6189007 : Nat := 118140960795 + 6189007 * 2 ^ 59
def prefixEnd_6189007 : Nat := 4983230072969 + 3 ^ 40 * 6189007 * 2
def baseEnd_6189007 : Nat := 1059311788346990738449927

theorem tailTrace_6189007 : CollatzResearch.WordTrace tailWord_6189007 prefixEnd_6189007 1059311788346990738449927 := by
  unfold tailWord_6189007
  simp only [CollatzResearch.WordTrace]
  refine ⟨225731629889292112088781275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150487753259528074725854183 225731629889292112088781275)
  ·
    refine ⟨338597444833938168133171913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225731629889292112088781275 338597444833938168133171913)
    ·
      refine ⟨253948083625453626099878935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338597444833938168133171913 253948083625453626099878935)
      ·
        refine ⟨380922125438180439149818403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253948083625453626099878935 380922125438180439149818403)
        ·
          refine ⟨571383188157270658724727605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380922125438180439149818403 571383188157270658724727605)
          ·
            refine ⟨53567173889744124255443213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 571383188157270658724727605 53567173889744124255443213)
            ·
              refine ⟨20087690208654046595791205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53567173889744124255443213 20087690208654046595791205)
              ·
                refine ⟨3766441914122633736710851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20087690208654046595791205 3766441914122633736710851)
                ·
                  refine ⟨5649662871183950605066277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766441914122633736710851 5649662871183950605066277)
                  ·
                    refine ⟨1059311788346990738449927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5649662871183950605066277 1059311788346990738449927)
                    ·
                      rfl

theorem cell23_6189007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_6189007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189007 prefixEnd_6189007 := by exact prefixLift 6189007
  have htrace : WordTrace (prefixWord ++ tailWord_6189007) baseStart_6189007 baseEnd_6189007 := by
    simpa [prefixWord, tailWord_6189007, baseEnd_6189007] using wordTrace_append hprefix tailTrace_6189007
  have hstable : (prefixWord ++ tailWord_6189007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189007).length < 2 ^ (prefixWord ++ tailWord_6189007).sum := by decide
  have hdescent : baseEnd_6189007 < baseStart_6189007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189054 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_6189054 : Nat := 118140960795 + 6189054 * 2 ^ 59
def prefixEnd_6189054 : Nat := 4983230072969 + 3 ^ 40 * 6189054 * 2
def baseEnd_6189054 : Nat := 353106610959081503495785

theorem tailTrace_6189054 : CollatzResearch.WordTrace tailWord_6189054 prefixEnd_6189054 353106610959081503495785 := by
  unfold tailWord_6189054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216668015015229889467777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150488896080081226077161477 28216668015015229889467777)
  ·
    refine ⟨21162501011261422417100833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28216668015015229889467777 21162501011261422417100833)
    ·
      refine ⟨15871875758446066812825625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21162501011261422417100833 15871875758446066812825625)
      ·
        refine ⟨11903906818834550109619219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15871875758446066812825625 11903906818834550109619219)
        ·
          refine ⟨17855860228251825164428829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903906818834550109619219 17855860228251825164428829)
          ·
            refine ⟨6695947585594434436660811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17855860228251825164428829 6695947585594434436660811)
            ·
              refine ⟨10043921378391651654991217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695947585594434436660811 10043921378391651654991217)
              ·
                refine ⟨7532941033793738741243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10043921378391651654991217 7532941033793738741243413)
                ·
                  refine ⟨353106610959081503495785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7532941033793738741243413 353106610959081503495785)
                  ·
                    rfl

theorem cell23_6189054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_6189054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189054 prefixEnd_6189054 := by exact prefixLift 6189054
  have htrace : WordTrace (prefixWord ++ tailWord_6189054) baseStart_6189054 baseEnd_6189054 := by
    simpa [prefixWord, tailWord_6189054, baseEnd_6189054] using wordTrace_append hprefix tailTrace_6189054
  have hstable : (prefixWord ++ tailWord_6189054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189054).length < 2 ^ (prefixWord ++ tailWord_6189054).sum := by decide
  have hdescent : baseEnd_6189054 < baseStart_6189054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189057 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_6189057 : Nat := 118140960795 + 6189057 * 2 ^ 59
def prefixEnd_6189057 : Nat := 4983230072969 + 3 ^ 40 * 6189057 * 2
def baseEnd_6189057 : Nat := 3177961039073697019724551

theorem tailTrace_6189057 : CollatzResearch.WordTrace tailWord_6189057 prefixEnd_6189057 3177961039073697019724551 := by
  unfold tailWord_6189057
  simp only [CollatzResearch.WordTrace]
  refine ⟨225733453539110970628101425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150488969026073980418734283 225733453539110970628101425)
  ·
    refine ⟨169300090154333227971076069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225733453539110970628101425 169300090154333227971076069)
    ·
      refine ⟨31743766903937480244576763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169300090154333227971076069 31743766903937480244576763)
      ·
        refine ⟨47615650355906220366865145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31743766903937480244576763 47615650355906220366865145)
        ·
          refine ⟨35711737766929665275148859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47615650355906220366865145 35711737766929665275148859)
          ·
            refine ⟨53567606650394497912723289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35711737766929665275148859 53567606650394497912723289)
            ·
              refine ⟨40175704987795873434542467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53567606650394497912723289 40175704987795873434542467)
              ·
                refine ⟨60263557481693810151813701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40175704987795873434542467 60263557481693810151813701)
                ·
                  refine ⟨11299417027817589403465069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60263557481693810151813701 11299417027817589403465069)
                  ·
                    refine ⟨4237281385431596026299401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11299417027817589403465069 4237281385431596026299401)
                    ·
                      refine ⟨3177961039073697019724551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237281385431596026299401 3177961039073697019724551)
                      ·
                        rfl

theorem cell23_6189057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_6189057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189057 prefixEnd_6189057 := by exact prefixLift 6189057
  have htrace : WordTrace (prefixWord ++ tailWord_6189057) baseStart_6189057 baseEnd_6189057 := by
    simpa [prefixWord, tailWord_6189057, baseEnd_6189057] using wordTrace_append hprefix tailTrace_6189057
  have hstable : (prefixWord ++ tailWord_6189057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189057).length < 2 ^ (prefixWord ++ tailWord_6189057).sum := by decide
  have hdescent : baseEnd_6189057 < baseStart_6189057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189064 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_6189064 : Nat := 118140960795 + 6189064 * 2 ^ 59
def prefixEnd_6189064 : Nat := 4983230072969 + 3 ^ 40 * 6189064 * 2
def baseEnd_6189064 : Nat := 3177964633438278492337019

theorem tailTrace_6189064 : CollatzResearch.WordTrace tailWord_6189064 prefixEnd_6189064 3177964633438278492337019 := by
  unfold tailWord_6189064
  simp only [CollatzResearch.WordTrace]
  refine ⟨112866854425042805411803123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150489139233390407215737497 112866854425042805411803123)
  ·
    refine ⟨169300281637564208117704685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112866854425042805411803123 169300281637564208117704685)
    ·
      refine ⟨63487605614086578044139257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169300281637564208117704685 63487605614086578044139257)
      ·
        refine ⟨47615704210564933533104443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63487605614086578044139257 47615704210564933533104443)
        ·
          refine ⟨71423556315847400299656665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47615704210564933533104443 71423556315847400299656665)
          ·
            refine ⟨53567667236885550224742499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71423556315847400299656665 53567667236885550224742499)
            ·
              refine ⟨80351500855328325337113749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53567667236885550224742499 80351500855328325337113749)
              ·
                refine ⟨3766476602593515250177207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80351500855328325337113749 3766476602593515250177207)
                ·
                  refine ⟨5649714903890272875265811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766476602593515250177207 5649714903890272875265811)
                  ·
                    refine ⟨8474572355835409312898717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5649714903890272875265811 8474572355835409312898717)
                    ·
                      refine ⟨3177964633438278492337019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474572355835409312898717 3177964633438278492337019)
                      ·
                        rfl

theorem cell23_6189064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_6189064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189064 prefixEnd_6189064 := by exact prefixLift 6189064
  have htrace : WordTrace (prefixWord ++ tailWord_6189064) baseStart_6189064 baseEnd_6189064 := by
    simpa [prefixWord, tailWord_6189064, baseEnd_6189064] using wordTrace_append hprefix tailTrace_6189064
  have hstable : (prefixWord ++ tailWord_6189064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189064).length < 2 ^ (prefixWord ++ tailWord_6189064).sum := by decide
  have hdescent : baseEnd_6189064 < baseStart_6189064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189087 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_6189087 : Nat := 118140960795 + 6189087 * 2 ^ 59
def prefixEnd_6189087 : Nat := 4983230072969 + 3 ^ 40 * 6189087 * 2
def baseEnd_6189087 : Nat := 3177976443493331902349413

theorem tailTrace_6189087 : CollatzResearch.WordTrace tailWord_6189087 prefixEnd_6189087 3177976443493331902349413 := by
  unfold tailWord_6189087
  simp only [CollatzResearch.WordTrace]
  refine ⟨225734547729002285751693515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150489698486001523834462343 225734547729002285751693515)
  ·
    refine ⟨338601821593503428627540273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225734547729002285751693515 338601821593503428627540273)
    ·
      refine ⟨253951366195127571470655205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338601821593503428627540273 253951366195127571470655205)
      ·
        refine ⟨47615881161586419650747851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253951366195127571470655205 47615881161586419650747851)
        ·
          refine ⟨71423821742379629476121777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47615881161586419650747851 71423821742379629476121777)
          ·
            refine ⟨53567866306784722107091333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71423821742379629476121777 53567866306784722107091333)
            ·
              refine ⟨10043974932522135395079625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53567866306784722107091333 10043974932522135395079625)
              ·
                refine ⟨7532981199391601546309719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10043974932522135395079625 7532981199391601546309719)
                ·
                  refine ⟨11299471799087402319464579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532981199391601546309719 11299471799087402319464579)
                  ·
                    refine ⟨16949207698631103479196869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11299471799087402319464579 16949207698631103479196869)
                    ·
                      refine ⟨3177976443493331902349413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16949207698631103479196869 3177976443493331902349413)
                      ·
                        rfl

theorem cell23_6189087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_6189087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189087 prefixEnd_6189087 := by exact prefixLift 6189087
  have htrace : WordTrace (prefixWord ++ tailWord_6189087) baseStart_6189087 baseEnd_6189087 := by
    simpa [prefixWord, tailWord_6189087, baseEnd_6189087] using wordTrace_append hprefix tailTrace_6189087
  have hstable : (prefixWord ++ tailWord_6189087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189087).length < 2 ^ (prefixWord ++ tailWord_6189087).sum := by decide
  have hdescent : baseEnd_6189087 < baseStart_6189087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189090 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6189090 : Nat := 118140960795 + 6189090 * 2 ^ 59
def prefixEnd_6189090 : Nat := 4983230072969 + 3 ^ 40 * 6189090 * 2
def baseEnd_6189090 : Nat := 3177977983935295390611899

theorem tailTrace_6189090 : CollatzResearch.WordTrace tailWord_6189090 prefixEnd_6189090 3177977983935295390611899 := by
  unfold tailWord_6189090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56433664286997854316013181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150489771431994278176035149 56433664286997854316013181)
  ·
    refine ⟨21162624107624195368504943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56433664286997854316013181 21162624107624195368504943)
    ·
      refine ⟨31743936161436293052757415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162624107624195368504943 31743936161436293052757415)
      ·
        refine ⟨47615904242154439579136123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31743936161436293052757415 47615904242154439579136123)
        ·
          refine ⟨71423856363231659368704185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47615904242154439579136123 71423856363231659368704185)
          ·
            refine ⟨53567892272423744526528139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71423856363231659368704185 53567892272423744526528139)
            ·
              refine ⟨80351838408635616789792209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53567892272423744526528139 80351838408635616789792209)
              ·
                refine ⟨60263878806476712592344157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80351838408635616789792209 60263878806476712592344157)
                ·
                  refine ⟨22598954552428767222129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60263878806476712592344157 22598954552428767222129059)
                  ·
                    refine ⟨33898431828643150833193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22598954552428767222129059 33898431828643150833193589)
                    ·
                      refine ⟨3177977983935295390611899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33898431828643150833193589 3177977983935295390611899)
                      ·
                        rfl

theorem cell23_6189090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6189090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189090 prefixEnd_6189090 := by exact prefixLift 6189090
  have htrace : WordTrace (prefixWord ++ tailWord_6189090) baseStart_6189090 baseEnd_6189090 := by
    simpa [prefixWord, tailWord_6189090, baseEnd_6189090] using wordTrace_append hprefix tailTrace_6189090
  have hstable : (prefixWord ++ tailWord_6189090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189090).length < 2 ^ (prefixWord ++ tailWord_6189090).sum := by decide
  have hdescent : baseEnd_6189090 < baseStart_6189090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189098 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6189098 : Nat := 118140960795 + 6189098 * 2 ^ 59
def prefixEnd_6189098 : Nat := 4983230072969 + 3 ^ 40 * 6189098 * 2
def baseEnd_6189098 : Nat := 3177982091780531359311863

theorem tailTrace_6189098 : CollatzResearch.WordTrace tailWord_6189098 prefixEnd_6189098 3177982091780531359311863 := by
  unfold tailWord_6189098
  simp only [CollatzResearch.WordTrace]
  refine ⟨56433737232990608657585987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150489965954641623086895965 56433737232990608657585987)
  ·
    refine ⟨84650605849485912986378981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56433737232990608657585987 84650605849485912986378981)
    ·
      refine ⟨15871988596778608684946059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84650605849485912986378981 15871988596778608684946059)
      ·
        refine ⟨23807982895167913027419089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15871988596778608684946059 23807982895167913027419089)
        ·
          refine ⟨17855987171375934770564317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23807982895167913027419089 17855987171375934770564317)
          ·
            refine ⟨6695995189265975538961619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17855987171375934770564317 6695995189265975538961619)
            ·
              refine ⟨10043992783898963308442429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695995189265975538961619 10043992783898963308442429)
              ·
                refine ⟨3766497293962111240665911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10043992783898963308442429 3766497293962111240665911)
                ·
                  refine ⟨5649745940943166860998867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766497293962111240665911 5649745940943166860998867)
                  ·
                    refine ⟨8474618911414750291498301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5649745940943166860998867 8474618911414750291498301)
                    ·
                      refine ⟨3177982091780531359311863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474618911414750291498301 3177982091780531359311863)
                      ·
                        rfl

theorem cell23_6189098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6189098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189098 prefixEnd_6189098 := by exact prefixLift 6189098
  have htrace : WordTrace (prefixWord ++ tailWord_6189098) baseStart_6189098 baseEnd_6189098 := by
    simpa [prefixWord, tailWord_6189098, baseEnd_6189098] using wordTrace_append hprefix tailTrace_6189098
  have hstable : (prefixWord ++ tailWord_6189098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189098).length < 2 ^ (prefixWord ++ tailWord_6189098).sum := by decide
  have hdescent : baseEnd_6189098 < baseStart_6189098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189107 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 3]
def baseStart_6189107 : Nat := 118140960795 + 6189107 * 2 ^ 59
def prefixEnd_6189107 : Nat := 4983230072969 + 3 ^ 40 * 6189107 * 2
def baseEnd_6189107 : Nat := 3177986713106421824099321

theorem tailTrace_6189107 : CollatzResearch.WordTrace tailWord_6189107 prefixEnd_6189107 3177986713106421824099321 := by
  unfold tailWord_6189107
  simp only [CollatzResearch.WordTrace]
  refine ⟨225735277188929829167421575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150490184792619886111614383 225735277188929829167421575)
  ·
    refine ⟨338602915783394743751132363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225735277188929829167421575 338602915783394743751132363)
    ·
      refine ⟨507904373675092115626698545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338602915783394743751132363 507904373675092115626698545)
      ·
        refine ⟨380928280256319086720023909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507904373675092115626698545 380928280256319086720023909)
        ·
          refine ⟨71424052548059828760004483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380928280256319086720023909 71424052548059828760004483)
          ·
            refine ⟨107136078822089743140006725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71424052548059828760004483 107136078822089743140006725)
            ·
              refine ⟨20088014779141826838751261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107136078822089743140006725 20088014779141826838751261)
              ·
                refine ⟨7533005542178185064531723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20088014779141826838751261 7533005542178185064531723)
                ·
                  refine ⟨11299508313267277596797585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533005542178185064531723 11299508313267277596797585)
                  ·
                    refine ⟨8474631234950458197598189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11299508313267277596797585 8474631234950458197598189)
                    ·
                      refine ⟨3177986713106421824099321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8474631234950458197598189 3177986713106421824099321)
                      ·
                        rfl

theorem cell23_6189107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_6189107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189107 prefixEnd_6189107 := by exact prefixLift 6189107
  have htrace : WordTrace (prefixWord ++ tailWord_6189107) baseStart_6189107 baseEnd_6189107 := by
    simpa [prefixWord, tailWord_6189107, baseEnd_6189107] using wordTrace_append hprefix tailTrace_6189107
  have hstable : (prefixWord ++ tailWord_6189107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189107).length < 2 ^ (prefixWord ++ tailWord_6189107).sum := by decide
  have hdescent : baseEnd_6189107 < baseStart_6189107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189121 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6189121 : Nat := 118140960795 + 6189121 * 2 ^ 59
def prefixEnd_6189121 : Nat := 4983230072969 + 3 ^ 40 * 6189121 * 2
def baseEnd_6189121 : Nat := 3177993901835584769324257

theorem tailTrace_6189121 : CollatzResearch.WordTrace tailWord_6189121 prefixEnd_6189121 3177993901835584769324257 := by
  unfold tailWord_6189121
  simp only [CollatzResearch.WordTrace]
  refine ⟨225735787810879109558431217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150490525207252739705620811 225735787810879109558431217)
  ·
    refine ⟨169301840858159332168823413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225735787810879109558431217 169301840858159332168823413)
    ·
      refine ⟨15872047580452437390827195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169301840858159332168823413 15872047580452437390827195)
      ·
        refine ⟨23808071370678656086240793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15872047580452437390827195 23808071370678656086240793)
        ·
          refine ⟨17856053528008992064680595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23808071370678656086240793 17856053528008992064680595)
          ·
            refine ⟨26784080292013488097020893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17856053528008992064680595 26784080292013488097020893)
            ·
              refine ⟨10044030109505058036382835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26784080292013488097020893 10044030109505058036382835)
              ·
                refine ⟨15066045164257587054574253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10044030109505058036382835 15066045164257587054574253)
                ·
                  refine ⟨5649766936596595145465345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15066045164257587054574253 5649766936596595145465345)
                  ·
                    refine ⟨4237325202447446359099009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649766936596595145465345 4237325202447446359099009)
                    ·
                      refine ⟨3177993901835584769324257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237325202447446359099009 3177993901835584769324257)
                      ·
                        rfl

theorem cell23_6189121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6189121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189121 prefixEnd_6189121 := by exact prefixLift 6189121
  have htrace : WordTrace (prefixWord ++ tailWord_6189121) baseStart_6189121 baseEnd_6189121 := by
    simpa [prefixWord, tailWord_6189121, baseEnd_6189121] using wordTrace_append hprefix tailTrace_6189121
  have hstable : (prefixWord ++ tailWord_6189121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189121).length < 2 ^ (prefixWord ++ tailWord_6189121).sum := by decide
  have hdescent : baseEnd_6189121 < baseStart_6189121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189194 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6189194 : Nat := 118140960795 + 6189194 * 2 ^ 59
def prefixEnd_6189194 : Nat := 4983230072969 + 3 ^ 40 * 6189194 * 2
def baseEnd_6189194 : Nat := 3178031385923362983711421

theorem tailTrace_6189194 : CollatzResearch.WordTrace tailWord_6189194 prefixEnd_6189194 3178031385923362983711421 := by
  unfold tailWord_6189194
  simp only [CollatzResearch.WordTrace]
  refine ⟨56434612584903660756459659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150492300226409762017225757 56434612584903660756459659)
  ·
    refine ⟨84651918877355491134689489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56434612584903660756459659 84651918877355491134689489)
    ·
      refine ⟨63488939158016618351017117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84651918877355491134689489 63488939158016618351017117)
      ·
        refine ⟨23808352184256231881631419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63488939158016618351017117 23808352184256231881631419)
        ·
          refine ⟨35712528276384347822447129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23808352184256231881631419 35712528276384347822447129)
          ·
            refine ⟨26784396207288260866835347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35712528276384347822447129 26784396207288260866835347)
            ·
              refine ⟨40176594310932391300253021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26784396207288260866835347 40176594310932391300253021)
              ·
                refine ⟨15066222866599646737594883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40176594310932391300253021 15066222866599646737594883)
                ·
                  refine ⟨22599334299899470106392325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15066222866599646737594883 22599334299899470106392325)
                  ·
                    refine ⟨4237375181231150644948561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22599334299899470106392325 4237375181231150644948561)
                    ·
                      refine ⟨3178031385923362983711421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237375181231150644948561 3178031385923362983711421)
                      ·
                        rfl

theorem cell23_6189194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6189194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189194 prefixEnd_6189194 := by exact prefixLift 6189194
  have htrace : WordTrace (prefixWord ++ tailWord_6189194) baseStart_6189194 baseEnd_6189194 := by
    simpa [prefixWord, tailWord_6189194, baseEnd_6189194] using wordTrace_append hprefix tailTrace_6189194
  have hstable : (prefixWord ++ tailWord_6189194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189194).length < 2 ^ (prefixWord ++ tailWord_6189194).sum := by decide
  have hdescent : baseEnd_6189194 < baseStart_6189194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189200 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 7]
def baseStart_6189200 : Nat := 118140960795 + 6189200 * 2 ^ 59
def prefixEnd_6189200 : Nat := 4983230072969 + 3 ^ 40 * 6189200 * 2
def baseEnd_6189200 : Nat := 353114940756365551137377

theorem tailTrace_6189200 : CollatzResearch.WordTrace tailWord_6189200 prefixEnd_6189200 353114940756365551137377 := by
  unfold tailWord_6189200
  simp only [CollatzResearch.WordTrace]
  refine ⟨112869334588796453025278527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150492446118395270700371369 112869334588796453025278527)
  ·
    refine ⟨169304001883194679537917791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112869334588796453025278527 169304001883194679537917791)
    ·
      refine ⟨253956002824792019306876687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169304001883194679537917791 253956002824792019306876687)
      ·
        refine ⟨380934004237188028960315031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253956002824792019306876687 380934004237188028960315031)
        ·
          refine ⟨571401006355782043440472547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380934004237188028960315031 571401006355782043440472547)
          ·
            refine ⟨857101509533673065160708821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571401006355782043440472547 857101509533673065160708821)
            ·
              refine ⟨20088316629695462464704113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 857101509533673065160708821 20088316629695462464704113)
              ·
                refine ⟨15066237472271596848528085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20088316629695462464704113 15066237472271596848528085)
                ·
                  refine ⟨353114940756365551137377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15066237472271596848528085 353114940756365551137377)
                  ·
                    rfl

theorem cell23_6189200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_6189200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189200 prefixEnd_6189200 := by exact prefixLift 6189200
  have htrace : WordTrace (prefixWord ++ tailWord_6189200) baseStart_6189200 baseEnd_6189200 := by
    simpa [prefixWord, tailWord_6189200, baseEnd_6189200] using wordTrace_append hprefix tailTrace_6189200
  have hstable : (prefixWord ++ tailWord_6189200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189200).length < 2 ^ (prefixWord ++ tailWord_6189200).sum := by decide
  have hdescent : baseEnd_6189200 < baseStart_6189200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189206 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6189206 : Nat := 118140960795 + 6189206 * 2 ^ 59
def prefixEnd_6189206 : Nat := 4983230072969 + 3 ^ 40 * 6189206 * 2
def baseEnd_6189206 : Nat := 3178037547691216936761367

theorem tailTrace_6189206 : CollatzResearch.WordTrace tailWord_6189206 prefixEnd_6189206 3178037547691216936761367 := by
  unfold tailWord_6189206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108680500973198067204717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150492592010380779383516981 14108680500973198067204717)
  ·
    refine ⟨5290755187864949275201769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14108680500973198067204717 5290755187864949275201769)
    ·
      refine ⟨3968066390898711956401327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5290755187864949275201769 3968066390898711956401327)
      ·
        refine ⟨5952099586348067934601991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968066390898711956401327 5952099586348067934601991)
        ·
          refine ⟨8928149379522101901902987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952099586348067934601991 8928149379522101901902987)
          ·
            refine ⟨13392224069283152852854481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928149379522101901902987 13392224069283152852854481)
            ·
              refine ⟨10044168051962364639640861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13392224069283152852854481 10044168051962364639640861)
              ·
                refine ⟨3766563019485886739865323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10044168051962364639640861 3766563019485886739865323)
                ·
                  refine ⟨5649844529228830109797985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766563019485886739865323 5649844529228830109797985)
                  ·
                    refine ⟨4237383396921622582348489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5649844529228830109797985 4237383396921622582348489)
                    ·
                      refine ⟨3178037547691216936761367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237383396921622582348489 3178037547691216936761367)
                      ·
                        rfl

theorem cell23_6189206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6189206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189206 prefixEnd_6189206 := by exact prefixLift 6189206
  have htrace : WordTrace (prefixWord ++ tailWord_6189206) baseStart_6189206 baseEnd_6189206 := by
    simpa [prefixWord, tailWord_6189206, baseEnd_6189206] using wordTrace_append hprefix tailTrace_6189206
  have hstable : (prefixWord ++ tailWord_6189206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189206).length < 2 ^ (prefixWord ++ tailWord_6189206).sum := by decide
  have hdescent : baseEnd_6189206 < baseStart_6189206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189240 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_6189240 : Nat := 118140960795 + 6189240 * 2 ^ 59
def prefixEnd_6189240 : Nat := 4983230072969 + 3 ^ 40 * 6189240 * 2
def baseEnd_6189240 : Nat := 3178055006033469803736209

theorem tailTrace_6189240 : CollatzResearch.WordTrace tailWord_6189240 prefixEnd_6189240 3178055006033469803736209 := by
  unfold tailWord_6189240
  simp only [CollatzResearch.WordTrace]
  refine ⟨112870064048723996441006587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150493418731631995254675449 112870064048723996441006587)
  ·
    refine ⟨169305096073085994661509881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112870064048723996441006587 169305096073085994661509881)
    ·
      refine ⟨126978822054814495996132411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169305096073085994661509881 126978822054814495996132411)
      ·
        refine ⟨190468233082221743994198617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126978822054814495996132411 190468233082221743994198617)
        ·
          refine ⟨142851174811666307995648963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190468233082221743994198617 142851174811666307995648963)
          ·
            refine ⟨214276762217499461993473445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142851174811666307995648963 214276762217499461993473445)
            ·
              refine ⟨40176892915781149123776271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214276762217499461993473445 40176892915781149123776271)
              ·
                refine ⟨60265339373671723685664407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40176892915781149123776271 60265339373671723685664407)
                ·
                  refine ⟨90398009060507585528496611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60265339373671723685664407 90398009060507585528496611)
                  ·
                    refine ⟨135597013590761378292744917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90398009060507585528496611 135597013590761378292744917)
                    ·
                      refine ⟨3178055006033469803736209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135597013590761378292744917 3178055006033469803736209)
                      ·
                        rfl

theorem cell23_6189240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_6189240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189240 prefixEnd_6189240 := by exact prefixLift 6189240
  have htrace : WordTrace (prefixWord ++ tailWord_6189240) baseStart_6189240 baseEnd_6189240 := by
    simpa [prefixWord, tailWord_6189240, baseEnd_6189240] using wordTrace_append hprefix tailTrace_6189240
  have hstable : (prefixWord ++ tailWord_6189240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189240).length < 2 ^ (prefixWord ++ tailWord_6189240).sum := by decide
  have hdescent : baseEnd_6189240 < baseStart_6189240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189341 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 6]
def baseStart_6189341 : Nat := 118140960795 + 6189341 * 2 ^ 59
def prefixEnd_6189341 : Nat := 4983230072969 + 3 ^ 40 * 6189341 * 2
def baseEnd_6189341 : Nat := 353122985286619323174805

theorem tailTrace_6189341 : CollatzResearch.WordTrace tailWord_6189341 prefixEnd_6189341 353122985286619323174805 := by
  unfold tailWord_6189341
  simp only [CollatzResearch.WordTrace]
  refine ⟨225743811870082087131439877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150495874580054724754293251 225743811870082087131439877)
  ·
    refine ⟨42326964725640391337144977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225743811870082087131439877 42326964725640391337144977)
    ·
      refine ⟨31745223544230293502858733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42326964725640391337144977 31745223544230293502858733)
      ·
        refine ⟨11904458829086360063572025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31745223544230293502858733 11904458829086360063572025)
        ·
          refine ⟨8928344121814770047679019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11904458829086360063572025 8928344121814770047679019)
          ·
            refine ⟨13392516182722155071518529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928344121814770047679019 13392516182722155071518529)
            ·
              refine ⟨10044387137041616303638897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13392516182722155071518529 10044387137041616303638897)
              ·
                refine ⟨7533290352781212227729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10044387137041616303638897 7533290352781212227729173)
                ·
                  refine ⟨353122985286619323174805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7533290352781212227729173 353122985286619323174805)
                  ·
                    rfl

theorem cell23_6189341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_6189341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189341 prefixEnd_6189341 := by exact prefixLift 6189341
  have htrace : WordTrace (prefixWord ++ tailWord_6189341) baseStart_6189341 baseEnd_6189341 := by
    simpa [prefixWord, tailWord_6189341, baseEnd_6189341] using wordTrace_append hprefix tailTrace_6189341
  have hstable : (prefixWord ++ tailWord_6189341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189341).length < 2 ^ (prefixWord ++ tailWord_6189341).sum := by decide
  have hdescent : baseEnd_6189341 < baseStart_6189341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189387 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_6189387 : Nat := 118140960795 + 6189387 * 2 ^ 59
def prefixEnd_6189387 : Nat := 4983230072969 + 3 ^ 40 * 6189387 * 2
def baseEnd_6189387 : Nat := 3178130487689680728598033

theorem tailTrace_6189387 : CollatzResearch.WordTrace tailWord_6189387 prefixEnd_6189387 3178130487689680728598033 := by
  unfold tailWord_6189387
  simp only [CollatzResearch.WordTrace]
  refine ⟨225745489627915436987614415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150496993085276957991742943 225745489627915436987614415)
  ·
    refine ⟨338618234441873155481421623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225745489627915436987614415 338618234441873155481421623)
    ·
      refine ⟨507927351662809733222132435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338618234441873155481421623 507927351662809733222132435)
      ·
        refine ⟨761891027494214599833198653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507927351662809733222132435 761891027494214599833198653)
        ·
          refine ⟨285709135310330474937449495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761891027494214599833198653 285709135310330474937449495)
          ·
            refine ⟨428563702965495712406174243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285709135310330474937449495 428563702965495712406174243)
            ·
              refine ⟨642845554448243568609261365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428563702965495712406174243 642845554448243568609261365)
              ·
                refine ⟨60266770729522834557118253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 642845554448243568609261365 60266770729522834557118253)
                ·
                  refine ⟨22600039023571062958919345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60266770729522834557118253 22600039023571062958919345)
                  ·
                    refine ⟨16950029267678297219189509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22600039023571062958919345 16950029267678297219189509)
                    ·
                      refine ⟨3178130487689680728598033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16950029267678297219189509 3178130487689680728598033)
                      ·
                        rfl

theorem cell23_6189387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_6189387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189387 prefixEnd_6189387 := by exact prefixLift 6189387
  have htrace : WordTrace (prefixWord ++ tailWord_6189387) baseStart_6189387 baseEnd_6189387 := by
    simpa [prefixWord, tailWord_6189387, baseEnd_6189387] using wordTrace_append hprefix tailTrace_6189387
  have hstable : (prefixWord ++ tailWord_6189387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189387).length < 2 ^ (prefixWord ++ tailWord_6189387).sum := by decide
  have hdescent : baseEnd_6189387 < baseStart_6189387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189474 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6189474 : Nat := 118140960795 + 6189474 * 2 ^ 59
def prefixEnd_6189474 : Nat := 4983230072969 + 3 ^ 40 * 6189474 * 2
def baseEnd_6189474 : Nat := 1059391720168873962736711

theorem tailTrace_6189474 : CollatzResearch.WordTrace tailWord_6189474 prefixEnd_6189474 1059391720168873962736711 := by
  unfold tailWord_6189474
  simp only [CollatzResearch.WordTrace]
  refine ⟨56437165694650062711507869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150499108519066833897354317 56437165694650062711507869)
  ·
    refine ⟨21163937135493773516815451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56437165694650062711507869 21163937135493773516815451)
    ·
      refine ⟨31745905703240660275223177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21163937135493773516815451 31745905703240660275223177)
      ·
        refine ⟨23809429277430495206417383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31745905703240660275223177 23809429277430495206417383)
        ·
          refine ⟨35714143916145742809626075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23809429277430495206417383 35714143916145742809626075)
          ·
            refine ⟨53571215874218614214439113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35714143916145742809626075 53571215874218614214439113)
            ·
              refine ⟨40178411905663960660829335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53571215874218614214439113 40178411905663960660829335)
              ·
                refine ⟨60267617858495940991244003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40178411905663960660829335 60267617858495940991244003)
                ·
                  refine ⟨90401426787743911486866005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60267617858495940991244003 90401426787743911486866005)
                  ·
                    refine ⟨1059391720168873962736711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90401426787743911486866005 1059391720168873962736711)
                    ·
                      rfl

theorem cell23_6189474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6189474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189474 prefixEnd_6189474 := by exact prefixLift 6189474
  have htrace : WordTrace (prefixWord ++ tailWord_6189474) baseStart_6189474 baseEnd_6189474 := by
    simpa [prefixWord, tailWord_6189474, baseEnd_6189474] using wordTrace_append hprefix tailTrace_6189474
  have hstable : (prefixWord ++ tailWord_6189474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189474).length < 2 ^ (prefixWord ++ tailWord_6189474).sum := by decide
  have hdescent : baseEnd_6189474 < baseStart_6189474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189475 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 2, 1, 3]
def baseStart_6189475 : Nat := 118140960795 + 6189475 * 2 ^ 59
def prefixEnd_6189475 : Nat := 4983230072969 + 3 ^ 40 * 6189475 * 2
def baseEnd_6189475 : Nat := 3178175673987276384297629

theorem tailTrace_6189475 : CollatzResearch.WordTrace tailWord_6189475 prefixEnd_6189475 3178175673987276384297629 := by
  unfold tailWord_6189475
  simp only [CollatzResearch.WordTrace]
  refine ⟨225748699251596628016817879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150499132834397752011211919 225748699251596628016817879)
  ·
    refine ⟨338623048877394942025226819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225748699251596628016817879 338623048877394942025226819)
    ·
      refine ⟨507934573316092413037840229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338623048877394942025226819 507934573316092413037840229)
      ·
        refine ⟨95237732496767327444595043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 507934573316092413037840229 95237732496767327444595043)
        ·
          refine ⟨142856598745150991166892565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95237732496767327444595043 142856598745150991166892565)
          ·
            refine ⟨6696403066178952710948089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142856598745150991166892565 6696403066178952710948089)
            ·
              refine ⟨5022302299634214533211067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696403066178952710948089 5022302299634214533211067)
              ·
                refine ⟨7533453449451321799816601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022302299634214533211067 7533453449451321799816601)
                ·
                  refine ⟨5650090087088491349862451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7533453449451321799816601 5650090087088491349862451)
                  ·
                    refine ⟨8475135130632737024793677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5650090087088491349862451 8475135130632737024793677)
                    ·
                      refine ⟨3178175673987276384297629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475135130632737024793677 3178175673987276384297629)
                      ·
                        rfl

theorem cell23_6189475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_6189475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189475 prefixEnd_6189475 := by exact prefixLift 6189475
  have htrace : WordTrace (prefixWord ++ tailWord_6189475) baseStart_6189475 baseEnd_6189475 := by
    simpa [prefixWord, tailWord_6189475, baseEnd_6189475] using wordTrace_append hprefix tailTrace_6189475
  have hstable : (prefixWord ++ tailWord_6189475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189475).length < 2 ^ (prefixWord ++ tailWord_6189475).sum := by decide
  have hdescent : baseEnd_6189475 < baseStart_6189475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189485 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6189485 : Nat := 118140960795 + 6189485 * 2 ^ 59
def prefixEnd_6189485 : Nat := 4983230072969 + 3 ^ 40 * 6189485 * 2
def baseEnd_6189485 : Nat := 3178180808793821345172583

theorem tailTrace_6189485 : CollatzResearch.WordTrace tailWord_6189485 prefixEnd_6189485 3178180808793821345172583 := by
  unfold tailWord_6189485
  simp only [CollatzResearch.WordTrace]
  refine ⟨225749063981560399724681909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150499375987706933149787939 225749063981560399724681909)
  ·
    refine ⟨21163974748271287474188929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225749063981560399724681909 21163974748271287474188929)
    ·
      refine ⟨15872981061203465605641697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21163974748271287474188929 15872981061203465605641697)
      ·
        refine ⟨11904735795902599204231273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15872981061203465605641697 11904735795902599204231273)
        ·
          refine ⟨8928551846926949403173455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11904735795902599204231273 8928551846926949403173455)
          ·
            refine ⟨13392827770390424104760183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928551846926949403173455 13392827770390424104760183)
            ·
              refine ⟨20089241655585636157140275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13392827770390424104760183 20089241655585636157140275)
              ·
                refine ⟨30133862483378454235710413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20089241655585636157140275 30133862483378454235710413)
                ·
                  refine ⟨11300198431266920338391405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30133862483378454235710413 11300198431266920338391405)
                  ·
                    refine ⟨4237574411725095126896777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11300198431266920338391405 4237574411725095126896777)
                    ·
                      refine ⟨3178180808793821345172583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237574411725095126896777 3178180808793821345172583)
                      ·
                        rfl

theorem cell23_6189485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6189485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189485 prefixEnd_6189485 := by exact prefixLift 6189485
  have htrace : WordTrace (prefixWord ++ tailWord_6189485) baseStart_6189485 baseEnd_6189485 := by
    simpa [prefixWord, tailWord_6189485, baseEnd_6189485] using wordTrace_append hprefix tailTrace_6189485
  have hstable : (prefixWord ++ tailWord_6189485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189485).length < 2 ^ (prefixWord ++ tailWord_6189485).sum := by decide
  have hdescent : baseEnd_6189485 < baseStart_6189485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189571 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 4, 2]
def baseStart_6189571 : Nat := 118140960795 + 6189571 * 2 ^ 59
def prefixEnd_6189571 : Nat := 4983230072969 + 3 ^ 40 * 6189571 * 2
def baseEnd_6189571 : Nat := 3178224968130108008697187

theorem tailTrace_6189571 : CollatzResearch.WordTrace tailWord_6189571 prefixEnd_6189571 3178224968130108008697187 := by
  unfold tailWord_6189571
  simp only [CollatzResearch.WordTrace]
  refine ⟨225752200659248836412312567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150501467106165890941541711 225752200659248836412312567)
  ·
    refine ⟨338628300988873254618468851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225752200659248836412312567 338628300988873254618468851)
    ·
      refine ⟨507942451483309881927703277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338628300988873254618468851 507942451483309881927703277)
      ·
        refine ⟨190478419306241205722888729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507942451483309881927703277 190478419306241205722888729)
        ·
          refine ⟨142858814479680904292166547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190478419306241205722888729 142858814479680904292166547)
          ·
            refine ⟨214288221719521356438249821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142858814479680904292166547 214288221719521356438249821)
            ·
              refine ⟨80358083144820508664343683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214288221719521356438249821 80358083144820508664343683)
              ·
                refine ⟨120537124717230762996515525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80358083144820508664343683 120537124717230762996515525)
                ·
                  refine ⟨22600710884480768061846661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120537124717230762996515525 22600710884480768061846661)
                  ·
                    refine ⟨4237633290840144011596249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22600710884480768061846661 4237633290840144011596249)
                    ·
                      refine ⟨3178224968130108008697187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237633290840144011596249 3178224968130108008697187)
                      ·
                        rfl

theorem cell23_6189571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_6189571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189571 prefixEnd_6189571 := by exact prefixLift 6189571
  have htrace : WordTrace (prefixWord ++ tailWord_6189571) baseStart_6189571 baseEnd_6189571 := by
    simpa [prefixWord, tailWord_6189571, baseEnd_6189571] using wordTrace_append hprefix tailTrace_6189571
  have hstable : (prefixWord ++ tailWord_6189571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189571).length < 2 ^ (prefixWord ++ tailWord_6189571).sum := by decide
  have hdescent : baseEnd_6189571 < baseStart_6189571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189588 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6189588 : Nat := 118140960795 + 6189588 * 2 ^ 59
def prefixEnd_6189588 : Nat := 4983230072969 + 3 ^ 40 * 6189588 * 2
def baseEnd_6189588 : Nat := 3178233697301234442184609

theorem tailTrace_6189588 : CollatzResearch.WordTrace tailWord_6189588 prefixEnd_6189588 3178233697301234442184609 := by
  unfold tailWord_6189588
  simp only [CollatzResearch.WordTrace]
  refine ⟨112876410350093624157840709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150501880466791498877120945 112876410350093624157840709)
  ·
    refine ⟨21164326940642554529595133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112876410350093624157840709 21164326940642554529595133)
    ·
      refine ⟨7936622602740957948598175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21164326940642554529595133 7936622602740957948598175)
      ·
        refine ⟨11904933904111436922897263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936622602740957948598175 11904933904111436922897263)
        ·
          refine ⟨17857400856167155384345895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904933904111436922897263 17857400856167155384345895)
          ·
            refine ⟨26786101284250733076518843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17857400856167155384345895 26786101284250733076518843)
            ·
              refine ⟨40179151926376099614778265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26786101284250733076518843 40179151926376099614778265)
              ·
                refine ⟨30134363944782074711083699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40179151926376099614778265 30134363944782074711083699)
                ·
                  refine ⟨45201545917173112066625549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30134363944782074711083699 45201545917173112066625549)
                  ·
                    refine ⟨16950579718939917024984581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45201545917173112066625549 16950579718939917024984581)
                    ·
                      refine ⟨3178233697301234442184609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16950579718939917024984581 3178233697301234442184609)
                      ·
                        rfl

theorem cell23_6189588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6189588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189588 prefixEnd_6189588 := by exact prefixLift 6189588
  have htrace : WordTrace (prefixWord ++ tailWord_6189588) baseStart_6189588 baseEnd_6189588 := by
    simpa [prefixWord, tailWord_6189588, baseEnd_6189588] using wordTrace_append hprefix tailTrace_6189588
  have hstable : (prefixWord ++ tailWord_6189588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189588).length < 2 ^ (prefixWord ++ tailWord_6189588).sum := by decide
  have hdescent : baseEnd_6189588 < baseStart_6189588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189608 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6189608 : Nat := 118140960795 + 6189608 * 2 ^ 59
def prefixEnd_6189608 : Nat := 4983230072969 + 3 ^ 40 * 6189608 * 2
def baseEnd_6189608 : Nat := 3178243966914324363934517

theorem tailTrace_6189608 : CollatzResearch.WordTrace tailWord_6189608 prefixEnd_6189608 3178243966914324363934517 := by
  unfold tailWord_6189608
  simp only [CollatzResearch.WordTrace]
  refine ⟨112876775080057395865704739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150502366773409861154272985 112876775080057395865704739)
  ·
    refine ⟨169315162620086093798557109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112876775080057395865704739 169315162620086093798557109)
    ·
      refine ⟨15873296495633071293614729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169315162620086093798557109 15873296495633071293614729)
      ·
        refine ⟨11904972371724803470211047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15873296495633071293614729 11904972371724803470211047)
        ·
          refine ⟨17857458557587205205316571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904972371724803470211047 17857458557587205205316571)
          ·
            refine ⟨26786187836380807807974857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17857458557587205205316571 26786187836380807807974857)
            ·
              refine ⟨20089640877285605855981143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26786187836380807807974857 20089640877285605855981143)
              ·
                refine ⟨30134461315928408783971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20089640877285605855981143 30134461315928408783971715)
                ·
                  refine ⟨45201691973892613175957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30134461315928408783971715 45201691973892613175957573)
                  ·
                    refine ⟨8475317245104864970492045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45201691973892613175957573 8475317245104864970492045)
                    ·
                      refine ⟨3178243966914324363934517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475317245104864970492045 3178243966914324363934517)
                      ·
                        rfl

theorem cell23_6189608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6189608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189608 prefixEnd_6189608 := by exact prefixLift 6189608
  have htrace : WordTrace (prefixWord ++ tailWord_6189608) baseStart_6189608 baseEnd_6189608 := by
    simpa [prefixWord, tailWord_6189608, baseEnd_6189608] using wordTrace_append hprefix tailTrace_6189608
  have hstable : (prefixWord ++ tailWord_6189608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189608).length < 2 ^ (prefixWord ++ tailWord_6189608).sum := by decide
  have hdescent : baseEnd_6189608 < baseStart_6189608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189645 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6189645 : Nat := 118140960795 + 6189645 * 2 ^ 59
def prefixEnd_6189645 : Nat := 4983230072969 + 3 ^ 40 * 6189645 * 2
def baseEnd_6189645 : Nat := 353140329522060079907983

theorem tailTrace_6189645 : CollatzResearch.WordTrace tailWord_6189645 prefixEnd_6189645 353140329522060079907983 := by
  unfold tailWord_6189645
  simp only [CollatzResearch.WordTrace]
  refine ⟨225754899660980747050506389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150503266440653831367004259 225754899660980747050506389)
  ·
    refine ⟨10582260921608472517992487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225754899660980747050506389 10582260921608472517992487)
    ·
      refine ⟨15873391382412708776988731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582260921608472517992487 15873391382412708776988731)
      ·
        refine ⟨23810087073619063165483097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15873391382412708776988731 23810087073619063165483097)
        ·
          refine ⟨17857565305214297374112323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23810087073619063165483097 17857565305214297374112323)
          ·
            refine ⟨26786347957821446061168485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17857565305214297374112323 26786347957821446061168485)
            ·
              refine ⟨5022440242091521136469091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26786347957821446061168485 5022440242091521136469091)
              ·
                refine ⟨7533660363137281704703637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022440242091521136469091 7533660363137281704703637)
                ·
                  refine ⟨353140329522060079907983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7533660363137281704703637 353140329522060079907983)
                  ·
                    rfl

theorem cell23_6189645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6189645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189645 prefixEnd_6189645 := by exact prefixLift 6189645
  have htrace : WordTrace (prefixWord ++ tailWord_6189645) baseStart_6189645 baseEnd_6189645 := by
    simpa [prefixWord, tailWord_6189645, baseEnd_6189645] using wordTrace_append hprefix tailTrace_6189645
  have hstable : (prefixWord ++ tailWord_6189645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189645).length < 2 ^ (prefixWord ++ tailWord_6189645).sum := by decide
  have hdescent : baseEnd_6189645 < baseStart_6189645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189665 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_6189665 : Nat := 118140960795 + 6189665 * 2 ^ 59
def prefixEnd_6189665 : Nat := 4983230072969 + 3 ^ 40 * 6189665 * 2
def baseEnd_6189665 : Nat := 3178273235311630640921755

theorem tailTrace_6189665 : CollatzResearch.WordTrace tailWord_6189665 prefixEnd_6189665 3178273235311630640921755 := by
  unfold tailWord_6189665
  simp only [CollatzResearch.WordTrace]
  refine ⟨225755629120908290466234449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150503752747272193644156299 225755629120908290466234449)
  ·
    refine ⟨169316721840681217849675837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225755629120908290466234449 169316721840681217849675837)
    ·
      refine ⟨63493770690255456693628439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169316721840681217849675837 63493770690255456693628439)
      ·
        refine ⟨95240656035383185040442659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63493770690255456693628439 95240656035383185040442659)
        ·
          refine ⟨142860984053074777560663989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95240656035383185040442659 142860984053074777560663989)
          ·
            refine ⟨13393217254975760396312249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142860984053074777560663989 13393217254975760396312249)
            ·
              refine ⟨10044912941231820297234187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13393217254975760396312249 10044912941231820297234187)
              ·
                refine ⟨15067369411847730445851281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10044912941231820297234187 15067369411847730445851281)
                ·
                  refine ⟨11300527058885797834388461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15067369411847730445851281 11300527058885797834388461)
                  ·
                    refine ⟨4237697647082174187895673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11300527058885797834388461 4237697647082174187895673)
                    ·
                      refine ⟨3178273235311630640921755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237697647082174187895673 3178273235311630640921755)
                      ·
                        rfl

theorem cell23_6189665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_6189665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189665 prefixEnd_6189665 := by exact prefixLift 6189665
  have htrace : WordTrace (prefixWord ++ tailWord_6189665) baseStart_6189665 baseEnd_6189665 := by
    simpa [prefixWord, tailWord_6189665, baseEnd_6189665] using wordTrace_append hprefix tailTrace_6189665
  have hstable : (prefixWord ++ tailWord_6189665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189665).length < 2 ^ (prefixWord ++ tailWord_6189665).sum := by decide
  have hdescent : baseEnd_6189665 < baseStart_6189665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189689 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 1, 1, 3]
def baseStart_6189689 : Nat := 118140960795 + 6189689 * 2 ^ 59
def prefixEnd_6189689 : Nat := 4983230072969 + 3 ^ 40 * 6189689 * 2
def baseEnd_6189689 : Nat := 3178285558847338547021645

theorem tailTrace_6189689 : CollatzResearch.WordTrace tailWord_6189689 prefixEnd_6189689 3178285558847338547021645 := by
  unfold tailWord_6189689
  simp only [CollatzResearch.WordTrace]
  refine ⟨225756504472821342565108121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150504336315214228376738747 225756504472821342565108121)
  ·
    refine ⟨169317378354616006923831091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225756504472821342565108121 169317378354616006923831091)
    ·
      refine ⟨253976067531924010385746637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169317378354616006923831091 253976067531924010385746637)
      ·
        refine ⟨95241025324471503894654989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253976067531924010385746637 95241025324471503894654989)
        ·
          refine ⟨35715384496676813960495621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95241025324471503894654989 35715384496676813960495621)
          ·
            refine ⟨6696634593126902617592929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35715384496676813960495621 6696634593126902617592929)
            ·
              refine ⟨5022475944845176963194697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696634593126902617592929 5022475944845176963194697)
              ·
                refine ⟨3766856958633882722396023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5022475944845176963194697 3766856958633882722396023)
                ·
                  refine ⟨5650285437950824083594035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766856958633882722396023 5650285437950824083594035)
                  ·
                    refine ⟨8475428156926236125391053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5650285437950824083594035 8475428156926236125391053)
                    ·
                      refine ⟨3178285558847338547021645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475428156926236125391053 3178285558847338547021645)
                      ·
                        rfl

theorem cell23_6189689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_6189689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189689 prefixEnd_6189689 := by exact prefixLift 6189689
  have htrace : WordTrace (prefixWord ++ tailWord_6189689) baseStart_6189689 baseEnd_6189689 := by
    simpa [prefixWord, tailWord_6189689, baseEnd_6189689] using wordTrace_append hprefix tailTrace_6189689
  have hstable : (prefixWord ++ tailWord_6189689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189689).length < 2 ^ (prefixWord ++ tailWord_6189689).sum := by decide
  have hdescent : baseEnd_6189689 < baseStart_6189689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189701 : List Nat := [1, 3, 1, 1, 4, 2, 3, 8]
def baseStart_6189701 : Nat := 118140960795 + 6189701 * 2 ^ 59
def prefixEnd_6189701 : Nat := 4983230072969 + 3 ^ 40 * 6189701 * 2
def baseEnd_6189701 : Nat := 117714508170933055558207

theorem tailTrace_6189701 : CollatzResearch.WordTrace tailWord_6189701 prefixEnd_6189701 117714508170933055558207 := by
  unfold tailWord_6189701
  simp only [CollatzResearch.WordTrace]
  refine ⟨225756942148777868614544957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150504628099185245743029971 225756942148777868614544957)
  ·
    refine ⟨84658853305791700730454359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225756942148777868614544957 84658853305791700730454359)
    ·
      refine ⟨126988279958687551095681539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84658853305791700730454359 126988279958687551095681539)
      ·
        refine ⟨190482419938031326643522309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126988279958687551095681539 190482419938031326643522309)
        ·
          refine ⟨35715453738380873745660433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190482419938031326643522309 35715453738380873745660433)
          ·
            refine ⟨26786590303785655309245325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35715453738380873745660433 26786590303785655309245325)
            ·
              refine ⟨10044971363919620740966997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26786590303785655309245325 10044971363919620740966997)
              ·
                refine ⟨117714508170933055558207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10044971363919620740966997 117714508170933055558207)
                ·
                  rfl

theorem cell23_6189701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 8].length) (baseStart_6189701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189701 prefixEnd_6189701 := by exact prefixLift 6189701
  have htrace : WordTrace (prefixWord ++ tailWord_6189701) baseStart_6189701 baseEnd_6189701 := by
    simpa [prefixWord, tailWord_6189701, baseEnd_6189701] using wordTrace_append hprefix tailTrace_6189701
  have hstable : (prefixWord ++ tailWord_6189701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189701).length < 2 ^ (prefixWord ++ tailWord_6189701).sum := by decide
  have hdescent : baseEnd_6189701 < baseStart_6189701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_6189711 : Nat := 118140960795 + 6189711 * 2 ^ 59
def prefixEnd_6189711 : Nat := 4983230072969 + 3 ^ 40 * 6189711 * 2
def baseEnd_6189711 : Nat := 3178296855421737460946543

theorem tailTrace_6189711 : CollatzResearch.WordTrace tailWord_6189711 prefixEnd_6189711 3178296855421737460946543 := by
  unfold tailWord_6189711
  simp only [CollatzResearch.WordTrace]
  refine ⟨225757306878741640322408987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150504871252494426881605991 225757306878741640322408987)
  ·
    refine ⟨338635960318112460483613481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225757306878741640322408987 338635960318112460483613481)
    ·
      refine ⟨253976970238584345362710111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338635960318112460483613481 253976970238584345362710111)
      ·
        refine ⟨380965455357876518044065167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253976970238584345362710111 380965455357876518044065167)
        ·
          refine ⟨571448183036814777066097751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380965455357876518044065167 571448183036814777066097751)
          ·
            refine ⟨857172274555222165599146627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571448183036814777066097751 857172274555222165599146627)
            ·
              refine ⟨1285758411832833248398719941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857172274555222165599146627 1285758411832833248398719941)
              ·
                refine ⟨241079702218656234074759989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1285758411832833248398719941 241079702218656234074759989)
                ·
                  refine ⟨22601222082999021944508749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241079702218656234074759989 22601222082999021944508749)
                  ·
                    refine ⟨8475458281124633229190781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22601222082999021944508749 8475458281124633229190781)
                    ·
                      refine ⟨3178296855421737460946543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475458281124633229190781 3178296855421737460946543)
                      ·
                        rfl

theorem cell23_6189711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_6189711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189711 prefixEnd_6189711 := by exact prefixLift 6189711
  have htrace : WordTrace (prefixWord ++ tailWord_6189711) baseStart_6189711 baseEnd_6189711 := by
    simpa [prefixWord, tailWord_6189711, baseEnd_6189711] using wordTrace_append hprefix tailTrace_6189711
  have hstable : (prefixWord ++ tailWord_6189711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189711).length < 2 ^ (prefixWord ++ tailWord_6189711).sum := by decide
  have hdescent : baseEnd_6189711 < baseStart_6189711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189729 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6189729 : Nat := 118140960795 + 6189729 * 2 ^ 59
def prefixEnd_6189729 : Nat := 4983230072969 + 3 ^ 40 * 6189729 * 2
def baseEnd_6189729 : Nat := 3178306098073518390521461

theorem tailTrace_6189729 : CollatzResearch.WordTrace tailWord_6189729 prefixEnd_6189729 3178306098073518390521461 := by
  unfold tailWord_6189729
  simp only [CollatzResearch.WordTrace]
  refine ⟨225757963392676429396564241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150505308928450952931042827 225757963392676429396564241)
  ·
    refine ⟨169318472544507322047423181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225757963392676429396564241 169318472544507322047423181)
    ·
      refine ⟨63494427204190245767783693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169318472544507322047423181 63494427204190245767783693)
      ·
        refine ⟨23810410201571342162918885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63494427204190245767783693 23810410201571342162918885)
        ·
          refine ⟨4464451912794626655547291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23810410201571342162918885 4464451912794626655547291)
          ·
            refine ⟨6696677869191939983320937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464451912794626655547291 6696677869191939983320937)
            ·
              refine ⟨5022508401893954987490703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696677869191939983320937 5022508401893954987490703)
              ·
                refine ⟨7533762602840932481236055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022508401893954987490703 7533762602840932481236055)
                ·
                  refine ⟨11300643904261398721854083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533762602840932481236055 11300643904261398721854083)
                  ·
                    refine ⟨16950965856392098082781125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11300643904261398721854083 16950965856392098082781125)
                    ·
                      refine ⟨3178306098073518390521461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16950965856392098082781125 3178306098073518390521461)
                      ·
                        rfl

theorem cell23_6189729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6189729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189729 prefixEnd_6189729 := by exact prefixLift 6189729
  have htrace : WordTrace (prefixWord ++ tailWord_6189729) baseStart_6189729 baseEnd_6189729 := by
    simpa [prefixWord, tailWord_6189729, baseEnd_6189729] using wordTrace_append hprefix tailTrace_6189729
  have hstable : (prefixWord ++ tailWord_6189729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189729).length < 2 ^ (prefixWord ++ tailWord_6189729).sum := by decide
  have hdescent : baseEnd_6189729 < baseStart_6189729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189766 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6189766 : Nat := 118140960795 + 6189766 * 2 ^ 59
def prefixEnd_6189766 : Nat := 4983230072969 + 3 ^ 40 * 6189766 * 2
def baseEnd_6189766 : Nat := 3178325096857734745758791

theorem tailTrace_6189766 : CollatzResearch.WordTrace tailWord_6189766 prefixEnd_6189766 3178325096857734745758791 := by
  unfold tailWord_6189766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054978527923199522364411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150506208595694923143774101 7054978527923199522364411)
  ·
    refine ⟨10582467791884799283546617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7054978527923199522364411 10582467791884799283546617)
    ·
      refine ⟨7936850843913599462659963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10582467791884799283546617 7936850843913599462659963)
      ·
        refine ⟨11905276265870399193989945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936850843913599462659963 11905276265870399193989945)
        ·
          refine ⟨8928957199402799395492459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11905276265870399193989945 8928957199402799395492459)
          ·
            refine ⟨13393435799104199093238689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928957199402799395492459 13393435799104199093238689)
            ·
              refine ⟨10045076849328149319929017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13393435799104199093238689 10045076849328149319929017)
              ·
                refine ⟨7533807636996111989946763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10045076849328149319929017 7533807636996111989946763)
                ·
                  refine ⟨11300711455494167984920145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533807636996111989946763 11300711455494167984920145)
                  ·
                    refine ⟨8475533591620625988690109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11300711455494167984920145 8475533591620625988690109)
                    ·
                      refine ⟨3178325096857734745758791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475533591620625988690109 3178325096857734745758791)
                      ·
                        rfl

theorem cell23_6189766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6189766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189766 prefixEnd_6189766 := by exact prefixLift 6189766
  have htrace : WordTrace (prefixWord ++ tailWord_6189766) baseStart_6189766 baseEnd_6189766 := by
    simpa [prefixWord, tailWord_6189766, baseEnd_6189766] using wordTrace_append hprefix tailTrace_6189766
  have hstable : (prefixWord ++ tailWord_6189766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189766).length < 2 ^ (prefixWord ++ tailWord_6189766).sum := by decide
  have hdescent : baseEnd_6189766 < baseStart_6189766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189772 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6189772 : Nat := 118140960795 + 6189772 * 2 ^ 59
def prefixEnd_6189772 : Nat := 4983230072969 + 3 ^ 40 * 6189772 * 2
def baseEnd_6189772 : Nat := 3178328177741661722283763

theorem tailTrace_6189772 : CollatzResearch.WordTrace tailWord_6189772 prefixEnd_6189772 3178328177741661722283763 := by
  unfold tailWord_6189772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112879765865760323870189785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150506354487680431826919713 112879765865760323870189785)
  ·
    refine ⟨84659824399320242902642339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112879765865760323870189785 84659824399320242902642339)
    ·
      refine ⟨126989736598980364353963509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84659824399320242902642339 126989736598980364353963509)
      ·
        refine ⟨11905287806154409158184079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126989736598980364353963509 11905287806154409158184079)
        ·
          refine ⟨17857931709231613737276119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905287806154409158184079 17857931709231613737276119)
          ·
            refine ⟨26786897563847420605914179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17857931709231613737276119 26786897563847420605914179)
            ·
              refine ⟨40180346345771130908871269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26786897563847420605914179 40180346345771130908871269)
              ·
                refine ⟨7533814939832087045413363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40180346345771130908871269 7533814939832087045413363)
                ·
                  refine ⟨11300722409748130568120045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533814939832087045413363 11300722409748130568120045)
                  ·
                    refine ⟨4237770903655548963045017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11300722409748130568120045 4237770903655548963045017)
                    ·
                      refine ⟨3178328177741661722283763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237770903655548963045017 3178328177741661722283763)
                      ·
                        rfl

theorem cell23_6189772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6189772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189772 prefixEnd_6189772 := by exact prefixLift 6189772
  have htrace : WordTrace (prefixWord ++ tailWord_6189772) baseStart_6189772 baseEnd_6189772 := by
    simpa [prefixWord, tailWord_6189772, baseEnd_6189772] using wordTrace_append hprefix tailTrace_6189772
  have hstable : (prefixWord ++ tailWord_6189772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189772).length < 2 ^ (prefixWord ++ tailWord_6189772).sum := by decide
  have hdescent : baseEnd_6189772 < baseStart_6189772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189785 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 6, 2, 2]
def baseStart_6189785 : Nat := 118140960795 + 6189785 * 2 ^ 59
def prefixEnd_6189785 : Nat := 4983230072969 + 3 ^ 40 * 6189785 * 2
def baseEnd_6189785 : Nat := 3178334852990170171421203

theorem tailTrace_6189785 : CollatzResearch.WordTrace tailWord_6189785 prefixEnd_6189785 3178334852990170171421203 := by
  unfold tailWord_6189785
  simp only [CollatzResearch.WordTrace]
  refine ⟨225760005880473550960602809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150506670586982367307068539 225760005880473550960602809)
  ·
    refine ⟨169320004410355163220452107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225760005880473550960602809 169320004410355163220452107)
    ·
      refine ⟨253980006615532744830678161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169320004410355163220452107 253980006615532744830678161)
      ·
        refine ⟨190485004961649558623008621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253980006615532744830678161 190485004961649558623008621)
        ·
          refine ⟨71431876860618584483628233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190485004961649558623008621 71431876860618584483628233)
          ·
            refine ⟨53573907645463938362721175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71431876860618584483628233 53573907645463938362721175)
            ·
              refine ⟨80360861468195907544081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53573907645463938362721175 80360861468195907544081763)
              ·
                refine ⟨120541292202293861316122645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80360861468195907544081763 120541292202293861316122645)
                ·
                  refine ⟨5650373071982524749193249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120541292202293861316122645 5650373071982524749193249)
                  ·
                    refine ⟨4237779803986893561894937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5650373071982524749193249 4237779803986893561894937)
                    ·
                      refine ⟨3178334852990170171421203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237779803986893561894937 3178334852990170171421203)
                      ·
                        rfl

theorem cell23_6189785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_6189785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189785 prefixEnd_6189785 := by exact prefixLift 6189785
  have htrace : WordTrace (prefixWord ++ tailWord_6189785) baseStart_6189785 baseEnd_6189785 := by
    simpa [prefixWord, tailWord_6189785, baseEnd_6189785] using wordTrace_append hprefix tailTrace_6189785
  have hstable : (prefixWord ++ tailWord_6189785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189785).length < 2 ^ (prefixWord ++ tailWord_6189785).sum := by decide
  have hdescent : baseEnd_6189785 < baseStart_6189785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189802 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_6189802 : Nat := 118140960795 + 6189802 * 2 ^ 59
def prefixEnd_6189802 : Nat := 4983230072969 + 3 ^ 40 * 6189802 * 2
def baseEnd_6189802 : Nat := 3178343582161296604908625

theorem tailTrace_6189802 : CollatzResearch.WordTrace tailWord_6189802 prefixEnd_6189802 3178343582161296604908625 := by
  unfold tailWord_6189802
  simp only [CollatzResearch.WordTrace]
  refine ⟨56440156480352990715992915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150507083947607975242647773 56440156480352990715992915)
  ·
    refine ⟨84660234720529486073989373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56440156480352990715992915 84660234720529486073989373)
    ·
      refine ⟨31747588020198557277746015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84660234720529486073989373 31747588020198557277746015)
      ·
        refine ⟨47621382030297835916619023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31747588020198557277746015 47621382030297835916619023)
        ·
          refine ⟨71432073045446753874928535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47621382030297835916619023 71432073045446753874928535)
          ·
            refine ⟨107148109568170130812392803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71432073045446753874928535 107148109568170130812392803)
            ·
              refine ⟨160722164352255196218589205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107148109568170130812392803 160722164352255196218589205)
              ·
                refine ⟨7533851454011962322746369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160722164352255196218589205 7533851454011962322746369)
                ·
                  refine ⟨5650388590508971742059777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7533851454011962322746369 5650388590508971742059777)
                  ·
                    refine ⟨4237791442881728806544833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5650388590508971742059777 4237791442881728806544833)
                    ·
                      refine ⟨3178343582161296604908625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237791442881728806544833 3178343582161296604908625)
                      ·
                        rfl

theorem cell23_6189802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_6189802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189802 prefixEnd_6189802 := by exact prefixLift 6189802
  have htrace : WordTrace (prefixWord ++ tailWord_6189802) baseStart_6189802 baseEnd_6189802 := by
    simpa [prefixWord, tailWord_6189802, baseEnd_6189802] using wordTrace_append hprefix tailTrace_6189802
  have hstable : (prefixWord ++ tailWord_6189802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189802).length < 2 ^ (prefixWord ++ tailWord_6189802).sum := by decide
  have hdescent : baseEnd_6189802 < baseStart_6189802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189818 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_6189818 : Nat := 118140960795 + 6189818 * 2 ^ 59
def prefixEnd_6189818 : Nat := 4983230072969 + 3 ^ 40 * 6189818 * 2
def baseEnd_6189818 : Nat := 3178351797851768542308551

theorem tailTrace_6189818 : CollatzResearch.WordTrace tailWord_6189818 prefixEnd_6189818 3178351797851768542308551 := by
  unfold tailWord_6189818
  simp only [CollatzResearch.WordTrace]
  refine ⟨56440302372338499399138527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150507472992902665064369405 56440302372338499399138527)
  ·
    refine ⟨84660453558507749098707791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56440302372338499399138527 84660453558507749098707791)
    ·
      refine ⟨126990680337761623648061687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84660453558507749098707791 126990680337761623648061687)
      ·
        refine ⟨190486020506642435472092531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126990680337761623648061687 190486020506642435472092531)
        ·
          refine ⟨285729030759963653208138797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190486020506642435472092531 285729030759963653208138797)
          ·
            refine ⟨107148386534986369953052049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285729030759963653208138797 107148386534986369953052049)
            ·
              refine ⟨80361289901239777464789037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107148386534986369953052049 80361289901239777464789037)
              ·
                refine ⟨30135483712964916549295889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80361289901239777464789037 30135483712964916549295889)
                ·
                  refine ⟨22601612784723687411971917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30135483712964916549295889 22601612784723687411971917)
                  ·
                    refine ⟨8475604794271382779489469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22601612784723687411971917 8475604794271382779489469)
                    ·
                      refine ⟨3178351797851768542308551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475604794271382779489469 3178351797851768542308551)
                      ·
                        rfl

theorem cell23_6189818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_6189818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189818 prefixEnd_6189818 := by exact prefixLift 6189818
  have htrace : WordTrace (prefixWord ++ tailWord_6189818) baseStart_6189818 baseEnd_6189818 := by
    simpa [prefixWord, tailWord_6189818, baseEnd_6189818] using wordTrace_append hprefix tailTrace_6189818
  have hstable : (prefixWord ++ tailWord_6189818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189818).length < 2 ^ (prefixWord ++ tailWord_6189818).sum := by decide
  have hdescent : baseEnd_6189818 < baseStart_6189818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189869 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6189869 : Nat := 118140960795 + 6189869 * 2 ^ 59
def prefixEnd_6189869 : Nat := 4983230072969 + 3 ^ 40 * 6189869 * 2
def baseEnd_6189869 : Nat := 3178377985365147842770817

theorem tailTrace_6189869 : CollatzResearch.WordTrace tailWord_6189869 prefixEnd_6189869 3178377985365147842770817 := by
  unfold tailWord_6189869
  simp only [CollatzResearch.WordTrace]
  refine ⟨225763069612169233306660661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150508713074779488871107107 225763069612169233306660661)
  ·
    refine ⟨21165287776140865622499437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225763069612169233306660661 21165287776140865622499437)
    ·
      refine ⟨7936982916052824608437289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21165287776140865622499437 7936982916052824608437289)
      ·
        refine ⟨5952737187039618456327967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7936982916052824608437289 5952737187039618456327967)
        ·
          refine ⟨8929105780559427684491951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952737187039618456327967 8929105780559427684491951)
          ·
            refine ⟨13393658670839141526737927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929105780559427684491951 13393658670839141526737927)
            ·
              refine ⟨20090488006258712290106891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13393658670839141526737927 20090488006258712290106891)
              ·
                refine ⟨30135732009388068435160337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20090488006258712290106891 30135732009388068435160337)
                ·
                  refine ⟨22601799007041051326370253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30135732009388068435160337 22601799007041051326370253)
                  ·
                    refine ⟨8475674627640394247388845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22601799007041051326370253 8475674627640394247388845)
                    ·
                      refine ⟨3178377985365147842770817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8475674627640394247388845 3178377985365147842770817)
                      ·
                        rfl

theorem cell23_6189869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6189869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189869 prefixEnd_6189869 := by exact prefixLift 6189869
  have htrace : WordTrace (prefixWord ++ tailWord_6189869) baseStart_6189869 baseEnd_6189869 := by
    simpa [prefixWord, tailWord_6189869, baseEnd_6189869] using wordTrace_append hprefix tailTrace_6189869
  have hstable : (prefixWord ++ tailWord_6189869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189869).length < 2 ^ (prefixWord ++ tailWord_6189869).sum := by decide
  have hdescent : baseEnd_6189869 < baseStart_6189869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189875 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 6, 2]
def baseStart_6189875 : Nat := 118140960795 + 6189875 * 2 ^ 59
def prefixEnd_6189875 : Nat := 4983230072969 + 3 ^ 40 * 6189875 * 2
def baseEnd_6189875 : Nat := 3178381066249074819295789

theorem tailTrace_6189875 : CollatzResearch.WordTrace tailWord_6189875 prefixEnd_6189875 3178381066249074819295789 := by
  unfold tailWord_6189875
  simp only [CollatzResearch.WordTrace]
  refine ⟨225763288450147496331379079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150508858966764997554252719 225763288450147496331379079)
  ·
    refine ⟨338644932675221244497068619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225763288450147496331379079 338644932675221244497068619)
    ·
      refine ⟨507967399012831866745602929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338644932675221244497068619 507967399012831866745602929)
      ·
        refine ⟨380975549259623900059202197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507967399012831866745602929 380975549259623900059202197)
        ·
          refine ⟨17858228871544870315275103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380975549259623900059202197 17858228871544870315275103)
          ·
            refine ⟨26787343307317305472912655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858228871544870315275103 26787343307317305472912655)
            ·
              refine ⟨40181014960975958209368983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26787343307317305472912655 40181014960975958209368983)
              ·
                refine ⟨60271522441463937314053475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40181014960975958209368983 60271522441463937314053475)
                ·
                  refine ⟨90407283662195905971080213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60271522441463937314053475 90407283662195905971080213)
                  ·
                    refine ⟨4237841421665433092394385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90407283662195905971080213 4237841421665433092394385)
                    ·
                      refine ⟨3178381066249074819295789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237841421665433092394385 3178381066249074819295789)
                      ·
                        rfl

theorem cell23_6189875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6, 2].length) (baseStart_6189875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189875 prefixEnd_6189875 := by exact prefixLift 6189875
  have htrace : WordTrace (prefixWord ++ tailWord_6189875) baseStart_6189875 baseEnd_6189875 := by
    simpa [prefixWord, tailWord_6189875, baseEnd_6189875] using wordTrace_append hprefix tailTrace_6189875
  have hstable : (prefixWord ++ tailWord_6189875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189875).length < 2 ^ (prefixWord ++ tailWord_6189875).sum := by decide
  have hdescent : baseEnd_6189875 < baseStart_6189875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189889 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6189889 : Nat := 118140960795 + 6189889 * 2 ^ 59
def prefixEnd_6189889 : Nat := 4983230072969 + 3 ^ 40 * 6189889 * 2
def baseEnd_6189889 : Nat := 1059462751659412588173575

theorem tailTrace_6189889 : CollatzResearch.WordTrace tailWord_6189889 prefixEnd_6189889 1059462751659412588173575 := by
  unfold tailWord_6189889
  simp only [CollatzResearch.WordTrace]
  refine ⟨225763799072096776722388721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150509199381397851148259147 225763799072096776722388721)
  ·
    refine ⟨169322849304072582541791541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225763799072096776722388721 169322849304072582541791541)
    ·
      refine ⟨15874017122256804613292957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169322849304072582541791541 15874017122256804613292957)
      ·
        refine ⟨5952756420846301729984859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15874017122256804613292957 5952756420846301729984859)
        ·
          refine ⟨8929134631269452594977289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952756420846301729984859 8929134631269452594977289)
          ·
            refine ⟨6696850973452089446232967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929134631269452594977289 6696850973452089446232967)
            ·
              refine ⟨10045276460178134169349451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696850973452089446232967 10045276460178134169349451)
              ·
                refine ⟨15067914690267201254024177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045276460178134169349451 15067914690267201254024177)
                ·
                  refine ⟨11300936017700400940518133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15067914690267201254024177 11300936017700400940518133)
                  ·
                    refine ⟨1059462751659412588173575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11300936017700400940518133 1059462751659412588173575)
                    ·
                      rfl

theorem cell23_6189889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6189889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189889 prefixEnd_6189889 := by exact prefixLift 6189889
  have htrace : WordTrace (prefixWord ++ tailWord_6189889) baseStart_6189889 baseEnd_6189889 := by
    simpa [prefixWord, tailWord_6189889, baseEnd_6189889] using wordTrace_append hprefix tailTrace_6189889
  have hstable : (prefixWord ++ tailWord_6189889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189889).length < 2 ^ (prefixWord ++ tailWord_6189889).sum := by decide
  have hdescent : baseEnd_6189889 < baseStart_6189889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189938 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6189938 : Nat := 118140960795 + 6189938 * 2 ^ 59
def prefixEnd_6189938 : Nat := 4983230072969 + 3 ^ 40 * 6189938 * 2
def baseEnd_6189938 : Nat := 3178413415530308072807999

theorem tailTrace_6189938 : CollatzResearch.WordTrace tailWord_6189938 prefixEnd_6189938 3178413415530308072807999 := by
  unfold tailWord_6189938
  simp only [CollatzResearch.WordTrace]
  refine ⟨56441396562229814522730617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150510390832612838727281645 56441396562229814522730617)
  ·
    refine ⟨42331047421672360892047963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56441396562229814522730617 42331047421672360892047963)
    ·
      refine ⟨63496571132508541338071945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42331047421672360892047963 63496571132508541338071945)
      ·
        refine ⟨47622428349381406003553959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63496571132508541338071945 47622428349381406003553959)
        ·
          refine ⟨71433642524072109005330939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47622428349381406003553959 71433642524072109005330939)
          ·
            refine ⟨107150463786108163507996409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71433642524072109005330939 107150463786108163507996409)
            ·
              refine ⟨80362847839581122630997307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107150463786108163507996409 80362847839581122630997307)
              ·
                refine ⟨120544271759371683946495961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80362847839581122630997307 120544271759371683946495961)
                ·
                  refine ⟨90408203819528762959871971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120544271759371683946495961 90408203819528762959871971)
                  ·
                    refine ⟨135612305729293144439807957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90408203819528762959871971 135612305729293144439807957)
                    ·
                      refine ⟨3178413415530308072807999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135612305729293144439807957 3178413415530308072807999)
                      ·
                        rfl

theorem cell23_6189938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6189938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189938 prefixEnd_6189938 := by exact prefixLift 6189938
  have htrace : WordTrace (prefixWord ++ tailWord_6189938) baseStart_6189938 baseEnd_6189938 := by
    simpa [prefixWord, tailWord_6189938, baseEnd_6189938] using wordTrace_append hprefix tailTrace_6189938
  have hstable : (prefixWord ++ tailWord_6189938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189938).length < 2 ^ (prefixWord ++ tailWord_6189938).sum := by decide
  have hdescent : baseEnd_6189938 < baseStart_6189938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189945 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_6189945 : Nat := 118140960795 + 6189945 * 2 ^ 59
def prefixEnd_6189945 : Nat := 4983230072969 + 3 ^ 40 * 6189945 * 2
def baseEnd_6189945 : Nat := 1059472336631629848473489

theorem tailTrace_6189945 : CollatzResearch.WordTrace tailWord_6189945 prefixEnd_6189945 1059472336631629848473489 := by
  unfold tailWord_6189945
  simp only [CollatzResearch.WordTrace]
  refine ⟨225765841559893898286427289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150510561039929265524284859 225765841559893898286427289)
  ·
    refine ⟨169324381169920423714820467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225765841559893898286427289 169324381169920423714820467)
    ·
      refine ⟨253986571754880635572230701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169324381169920423714820467 253986571754880635572230701)
      ·
        refine ⟨95244964408080238339586513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253986571754880635572230701 95244964408080238339586513)
        ·
          refine ⟨71433723306060178754689885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95244964408080238339586513 71433723306060178754689885)
          ·
            refine ⟨26787646239772567033008707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71433723306060178754689885 26787646239772567033008707)
            ·
              refine ⟨40181469359658850549513061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26787646239772567033008707 40181469359658850549513061)
              ·
                refine ⟨7534025504936034478033699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40181469359658850549513061 7534025504936034478033699)
                ·
                  refine ⟨11301038257404051717050549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534025504936034478033699 11301038257404051717050549)
                  ·
                    refine ⟨1059472336631629848473489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11301038257404051717050549 1059472336631629848473489)
                    ·
                      rfl

theorem cell23_6189945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_6189945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189945 prefixEnd_6189945 := by exact prefixLift 6189945
  have htrace : WordTrace (prefixWord ++ tailWord_6189945) baseStart_6189945 baseEnd_6189945 := by
    simpa [prefixWord, tailWord_6189945, baseEnd_6189945] using wordTrace_append hprefix tailTrace_6189945
  have hstable : (prefixWord ++ tailWord_6189945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189945).length < 2 ^ (prefixWord ++ tailWord_6189945).sum := by decide
  have hdescent : baseEnd_6189945 < baseStart_6189945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189948 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_6189948 : Nat := 118140960795 + 6189948 * 2 ^ 59
def prefixEnd_6189948 : Nat := 4983230072969 + 3 ^ 40 * 6189948 * 2
def baseEnd_6189948 : Nat := 3178418550336853033682953

theorem tailTrace_6189948 : CollatzResearch.WordTrace tailWord_6189948 prefixEnd_6189948 3178418550336853033682953 := by
  unfold tailWord_6189948
  simp only [CollatzResearch.WordTrace]
  refine ⟨112882975489441514899393249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150510633985922019865857665 112882975489441514899393249)
  ·
    refine ⟨84662231617081136174544937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112882975489441514899393249 84662231617081136174544937)
    ·
      refine ⟨63496673712810852130908703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84662231617081136174544937 63496673712810852130908703)
      ·
        refine ⟨95245010569216278196363055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63496673712810852130908703 95245010569216278196363055)
        ·
          refine ⟨142867515853824417294544583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95245010569216278196363055 142867515853824417294544583)
          ·
            refine ⟨214301273780736625941816875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142867515853824417294544583 214301273780736625941816875)
            ·
              refine ⟨321451910671104938912725313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214301273780736625941816875 321451910671104938912725313)
              ·
                refine ⟨241088933003328704184543985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321451910671104938912725313 241088933003328704184543985)
                ·
                  refine ⟨180816699752496528138407989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241088933003328704184543985 180816699752496528138407989)
                  ·
                    refine ⟨16951565601796549512975749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180816699752496528138407989 16951565601796549512975749)
                    ·
                      refine ⟨3178418550336853033682953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16951565601796549512975749 3178418550336853033682953)
                      ·
                        rfl

theorem cell23_6189948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_6189948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189948 prefixEnd_6189948 := by exact prefixLift 6189948
  have htrace : WordTrace (prefixWord ++ tailWord_6189948) baseStart_6189948 baseEnd_6189948 := by
    simpa [prefixWord, tailWord_6189948, baseEnd_6189948] using wordTrace_append hprefix tailTrace_6189948
  have hstable : (prefixWord ++ tailWord_6189948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189948).length < 2 ^ (prefixWord ++ tailWord_6189948).sum := by decide
  have hdescent : baseEnd_6189948 < baseStart_6189948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189962 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_6189962 : Nat := 118140960795 + 6189962 * 2 ^ 59
def prefixEnd_6189962 : Nat := 4983230072969 + 3 ^ 40 * 6189962 * 2
def baseEnd_6189962 : Nat := 1059475246355338659635963

theorem tailTrace_6189962 : CollatzResearch.WordTrace tailWord_6189962 prefixEnd_6189962 1059475246355338659635963 := by
  unfold tailWord_6189962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56441615400208077547449035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150510974400554873459864093 56441615400208077547449035)
  ·
    refine ⟨84662423100312116321173553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56441615400208077547449035 84662423100312116321173553)
    ·
      refine ⟨63496817325234087240880165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84662423100312116321173553 63496817325234087240880165)
      ·
        refine ⟨11905653248481391357665031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63496817325234087240880165 11905653248481391357665031)
        ·
          refine ⟨17858479872722087036497547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905653248481391357665031 17858479872722087036497547)
          ·
            refine ⟨26787719809083130554746321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858479872722087036497547 26787719809083130554746321)
            ·
              refine ⟨20090789856812347916059741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26787719809083130554746321 20090789856812347916059741)
              ·
                refine ⟨7534046196304630468522403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20090789856812347916059741 7534046196304630468522403)
                ·
                  refine ⟨11301069294456945702783605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534046196304630468522403 11301069294456945702783605)
                  ·
                    refine ⟨1059475246355338659635963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11301069294456945702783605 1059475246355338659635963)
                    ·
                      rfl

theorem cell23_6189962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_6189962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189962 prefixEnd_6189962 := by exact prefixLift 6189962
  have htrace : WordTrace (prefixWord ++ tailWord_6189962) baseStart_6189962 baseEnd_6189962 := by
    simpa [prefixWord, tailWord_6189962, baseEnd_6189962] using wordTrace_append hprefix tailTrace_6189962
  have hstable : (prefixWord ++ tailWord_6189962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189962).length < 2 ^ (prefixWord ++ tailWord_6189962).sum := by decide
  have hdescent : baseEnd_6189962 < baseStart_6189962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6189975 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 4, 4]
def baseStart_6189975 : Nat := 118140960795 + 6189975 * 2 ^ 59
def prefixEnd_6189975 : Nat := 4983230072969 + 3 ^ 40 * 6189975 * 2
def baseEnd_6189975 : Nat := 1059477471438174809348443

theorem tailTrace_6189975 : CollatzResearch.WordTrace tailWord_6189975 prefixEnd_6189975 1059477471438174809348443 := by
  unfold tailWord_6189975
  simp only [CollatzResearch.WordTrace]
  refine ⟨225766935749785213410019379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150511290499856808940012919 225766935749785213410019379)
  ·
    refine ⟨338650403624677820115029069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225766935749785213410019379 338650403624677820115029069)
    ·
      refine ⟨126993901359254182543135901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338650403624677820115029069 126993901359254182543135901)
      ·
        refine ⟨47622713009720318453675963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126993901359254182543135901 47622713009720318453675963)
        ·
          refine ⟨71434069514580477680513945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47622713009720318453675963 71434069514580477680513945)
          ·
            refine ⟨53575552135935358260385459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71434069514580477680513945 53575552135935358260385459)
            ·
              refine ⟨80363328203903037390578189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53575552135935358260385459 80363328203903037390578189)
              ·
                refine ⟨30136248076463639021466821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80363328203903037390578189 30136248076463639021466821)
                ·
                  refine ⟨5650546514336932316525029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30136248076463639021466821 5650546514336932316525029)
                  ·
                    refine ⟨1059477471438174809348443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5650546514336932316525029 1059477471438174809348443)
                    ·
                      rfl

theorem cell23_6189975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_6189975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6189975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6189975 prefixEnd_6189975 := by exact prefixLift 6189975
  have htrace : WordTrace (prefixWord ++ tailWord_6189975) baseStart_6189975 baseEnd_6189975 := by
    simpa [prefixWord, tailWord_6189975, baseEnd_6189975] using wordTrace_append hprefix tailTrace_6189975
  have hstable : (prefixWord ++ tailWord_6189975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6189975).length < 2 ^ (prefixWord ++ tailWord_6189975).sum := by decide
  have hdescent : baseEnd_6189975 < baseStart_6189975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6189975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190076 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_6190076 : Nat := 118140960795 + 6190076 * 2 ^ 59
def prefixEnd_6190076 : Nat := 4983230072969 + 3 ^ 40 * 6190076 * 2
def baseEnd_6190076 : Nat := 3178484275860628532882365

theorem tailTrace_6190076 : CollatzResearch.WordTrace tailWord_6190076 prefixEnd_6190076 3178484275860628532882365 := by
  unfold tailWord_6190076
  simp only [CollatzResearch.WordTrace]
  refine ⟨112885309761209653829723041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150513746348279538439630721 112885309761209653829723041)
  ·
    refine ⟨84663982320907240372292281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112885309761209653829723041 84663982320907240372292281)
    ·
      refine ⟨63497986740680430279219211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84663982320907240372292281 63497986740680430279219211)
      ·
        refine ⟨95246980111020645418828817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63497986740680430279219211 95246980111020645418828817)
        ·
          refine ⟨71435235083265484064121613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95246980111020645418828817 71435235083265484064121613)
          ·
            refine ⟨26788213156224556524045605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71435235083265484064121613 26788213156224556524045605)
            ·
              refine ⟨5022789966792104348258551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26788213156224556524045605 5022789966792104348258551)
              ·
                refine ⟨7534184950188156522387827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022789966792104348258551 7534184950188156522387827)
                ·
                  refine ⟨11301277425282234783581741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534184950188156522387827 11301277425282234783581741)
                  ·
                    refine ⟨4237979034480838043843153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11301277425282234783581741 4237979034480838043843153)
                    ·
                      refine ⟨3178484275860628532882365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4237979034480838043843153 3178484275860628532882365)
                      ·
                        rfl

theorem cell23_6190076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_6190076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190076 prefixEnd_6190076 := by exact prefixLift 6190076
  have htrace : WordTrace (prefixWord ++ tailWord_6190076) baseStart_6190076 baseEnd_6190076 := by
    simpa [prefixWord, tailWord_6190076, baseEnd_6190076] using wordTrace_append hprefix tailTrace_6190076
  have hstable : (prefixWord ++ tailWord_6190076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190076).length < 2 ^ (prefixWord ++ tailWord_6190076).sum := by decide
  have hdescent : baseEnd_6190076 < baseStart_6190076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190085 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_6190085 : Nat := 118140960795 + 6190085 * 2 ^ 59
def prefixEnd_6190085 : Nat := 4983230072969 + 3 ^ 40 * 6190085 * 2
def baseEnd_6190085 : Nat := 3178488897186518997669823

theorem tailTrace_6190085 : CollatzResearch.WordTrace tailWord_6190085 prefixEnd_6190085 3178488897186518997669823 := by
  unfold tailWord_6190085
  simp only [CollatzResearch.WordTrace]
  refine ⟨225770947779386702196523709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150513965186257801464349139 225770947779386702196523709)
  ·
    refine ⟨84664105417270013323696391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225770947779386702196523709 84664105417270013323696391)
    ·
      refine ⟨126996158125905019985544587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84664105417270013323696391 126996158125905019985544587)
      ·
        refine ⟨190494237188857529978316881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126996158125905019985544587 190494237188857529978316881)
        ·
          refine ⟨142870677891643147483737661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190494237188857529978316881 142870677891643147483737661)
          ·
            refine ⟨53576504209366180306401623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142870677891643147483737661 53576504209366180306401623)
            ·
              refine ⟨80364756314049270459602435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53576504209366180306401623 80364756314049270459602435)
              ·
                refine ⟨120547134471073905689403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80364756314049270459602435 120547134471073905689403653)
                ·
                  refine ⟨22602587713326357316763185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120547134471073905689403653 22602587713326357316763185)
                  ·
                    refine ⟨16951940784994767987572389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22602587713326357316763185 16951940784994767987572389)
                    ·
                      refine ⟨3178488897186518997669823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16951940784994767987572389 3178488897186518997669823)
                      ·
                        rfl

theorem cell23_6190085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_6190085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190085 prefixEnd_6190085 := by exact prefixLift 6190085
  have htrace : WordTrace (prefixWord ++ tailWord_6190085) baseStart_6190085 baseEnd_6190085 := by
    simpa [prefixWord, tailWord_6190085, baseEnd_6190085] using wordTrace_append hprefix tailTrace_6190085
  have hstable : (prefixWord ++ tailWord_6190085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190085).length < 2 ^ (prefixWord ++ tailWord_6190085).sum := by decide
  have hdescent : baseEnd_6190085 < baseStart_6190085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190135 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_6190135 : Nat := 118140960795 + 6190135 * 2 ^ 59
def prefixEnd_6190135 : Nat := 4983230072969 + 3 ^ 40 * 6190135 * 2
def baseEnd_6190135 : Nat := 3178514571219243802044593

theorem tailTrace_6190135 : CollatzResearch.WordTrace tailWord_6190135 prefixEnd_6190135 3178514571219243802044593 := by
  unfold tailWord_6190135
  simp only [CollatzResearch.WordTrace]
  refine ⟨225772771429205560735843859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150515180952803707157229239 225772771429205560735843859)
  ·
    refine ⟨338659157143808341103765789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225772771429205560735843859 338659157143808341103765789)
    ·
      refine ⟨126997183928928127913912171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338659157143808341103765789 126997183928928127913912171)
      ·
        refine ⟨190495775893392191870868257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126997183928928127913912171 190495775893392191870868257)
        ·
          refine ⟨142871831920044143903151193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190495775893392191870868257 142871831920044143903151193)
          ·
            refine ⟨107153873940033107927363395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142871831920044143903151193 107153873940033107927363395)
            ·
              refine ⟨160730810910049661891045093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107153873940033107927363395 160730810910049661891045093)
              ·
                refine ⟨30137027045634311604570955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160730810910049661891045093 30137027045634311604570955)
                ·
                  refine ⟨45205540568451467406856433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30137027045634311604570955 45205540568451467406856433)
                  ·
                    refine ⟨33904155426338600555142325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45205540568451467406856433 33904155426338600555142325)
                    ·
                      refine ⟨3178514571219243802044593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33904155426338600555142325 3178514571219243802044593)
                      ·
                        rfl

theorem cell23_6190135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_6190135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190135 prefixEnd_6190135 := by exact prefixLift 6190135
  have htrace : WordTrace (prefixWord ++ tailWord_6190135) baseStart_6190135 baseEnd_6190135 := by
    simpa [prefixWord, tailWord_6190135, baseEnd_6190135] using wordTrace_append hprefix tailTrace_6190135
  have hstable : (prefixWord ++ tailWord_6190135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190135).length < 2 ^ (prefixWord ++ tailWord_6190135).sum := by decide
  have hdescent : baseEnd_6190135 < baseStart_6190135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190252 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_6190252 : Nat := 118140960795 + 6190252 * 2 ^ 59
def prefixEnd_6190252 : Nat := 4983230072969 + 3 ^ 40 * 6190252 * 2
def baseEnd_6190252 : Nat := 3178574648455819844281555

theorem tailTrace_6190252 : CollatzResearch.WordTrace tailWord_6190252 prefixEnd_6190252 3178574648455819844281555 := by
  unfold tailWord_6190252
  simp only [CollatzResearch.WordTrace]
  refine ⟨112888519384890844858926505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150518025846521126478568673 112888519384890844858926505)
  ·
    refine ⟨84666389538668133644194879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112888519384890844858926505 84666389538668133644194879)
    ·
      refine ⟨126999584308002200466292319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84666389538668133644194879 126999584308002200466292319)
      ·
        refine ⟨190499376462003300699438479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126999584308002200466292319 190499376462003300699438479)
        ·
          refine ⟨285749064693004951049157719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190499376462003300699438479 285749064693004951049157719)
          ·
            refine ⟨428623597039507426573736579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285749064693004951049157719 428623597039507426573736579)
            ·
              refine ⟨642935395559261139860604869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428623597039507426573736579 642935395559261139860604869)
              ·
                refine ⟨120550386667361463723863413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642935395559261139860604869 120550386667361463723863413)
                ·
                  refine ⟨11301598750065137224112195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120550386667361463723863413 11301598750065137224112195)
                  ·
                    refine ⟨16952398125097705836168293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11301598750065137224112195 16952398125097705836168293)
                    ·
                      refine ⟨3178574648455819844281555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16952398125097705836168293 3178574648455819844281555)
                      ·
                        rfl

theorem cell23_6190252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_6190252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190252 prefixEnd_6190252 := by exact prefixLift 6190252
  have htrace : WordTrace (prefixWord ++ tailWord_6190252) baseStart_6190252 baseEnd_6190252 := by
    simpa [prefixWord, tailWord_6190252, baseEnd_6190252] using wordTrace_append hprefix tailTrace_6190252
  have hstable : (prefixWord ++ tailWord_6190252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190252).length < 2 ^ (prefixWord ++ tailWord_6190252).sum := by decide
  have hdescent : baseEnd_6190252 < baseStart_6190252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190253 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 6]
def baseStart_6190253 : Nat := 118140960795 + 6190253 * 2 ^ 59
def prefixEnd_6190253 : Nat := 4983230072969 + 3 ^ 40 * 6190253 * 2
def baseEnd_6190253 : Nat := 353175017992941593374339

theorem tailTrace_6190253 : CollatzResearch.WordTrace tailWord_6190253 prefixEnd_6190253 353175017992941593374339 := by
  unfold tailWord_6190253
  simp only [CollatzResearch.WordTrace]
  refine ⟨225777075242778066888639413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150518050161852044592426275 225777075242778066888639413)
  ·
    refine ⟨21166600804010443770809945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225777075242778066888639413 21166600804010443770809945)
    ·
      refine ⟨15874950603007832828107459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21166600804010443770809945 15874950603007832828107459)
      ·
        refine ⟨23812425904511749242161189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15874950603007832828107459 23812425904511749242161189)
        ·
          refine ⟨4464829857095952982905223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23812425904511749242161189 4464829857095952982905223)
          ·
            refine ⟨6697244785643929474357835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464829857095952982905223 6697244785643929474357835)
            ·
              refine ⟨10045867178465894211536753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697244785643929474357835 10045867178465894211536753)
              ·
                refine ⟨7534400383849420658652565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10045867178465894211536753 7534400383849420658652565)
                ·
                  refine ⟨353175017992941593374339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7534400383849420658652565 353175017992941593374339)
                  ·
                    rfl

theorem cell23_6190253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_6190253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190253 prefixEnd_6190253 := by exact prefixLift 6190253
  have htrace : WordTrace (prefixWord ++ tailWord_6190253) baseStart_6190253 baseEnd_6190253 := by
    simpa [prefixWord, tailWord_6190253, baseEnd_6190253] using wordTrace_append hprefix tailTrace_6190253
  have hstable : (prefixWord ++ tailWord_6190253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190253).length < 2 ^ (prefixWord ++ tailWord_6190253).sum := by decide
  have hdescent : baseEnd_6190253 < baseStart_6190253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190279 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 2, 4]
def baseStart_6190279 : Nat := 118140960795 + 6190279 * 2 ^ 59
def prefixEnd_6190279 : Nat := 4983230072969 + 3 ^ 40 * 6190279 * 2
def baseEnd_6190279 : Nat := 1059529504144497079547977

theorem tailTrace_6190279 : CollatzResearch.WordTrace tailWord_6190279 prefixEnd_6190279 1059529504144497079547977 := by
  unfold tailWord_6190279
  simp only [CollatzResearch.WordTrace]
  refine ⟨225778023540683873329085891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150518682360455915552723927 225778023540683873329085891)
  ·
    refine ⟨338667035311025809993628837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225778023540683873329085891 338667035311025809993628837)
    ·
      refine ⟨63500069120817339373805407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338667035311025809993628837 63500069120817339373805407)
      ·
        refine ⟨95250103681226009060708111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63500069120817339373805407 95250103681226009060708111)
        ·
          refine ⟨142875155521839013591062167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95250103681226009060708111 142875155521839013591062167)
          ·
            refine ⟨214312733282758520386593251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142875155521839013591062167 214312733282758520386593251)
            ·
              refine ⟨321469099924137780579889877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214312733282758520386593251 321469099924137780579889877)
              ·
                refine ⟨7534432029471979232341169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 321469099924137780579889877 7534432029471979232341169)
                ·
                  refine ⟨5650824022103984424255877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7534432029471979232341169 5650824022103984424255877)
                  ·
                    refine ⟨1059529504144497079547977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5650824022103984424255877 1059529504144497079547977)
                    ·
                      rfl

theorem cell23_6190279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_6190279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190279 prefixEnd_6190279 := by exact prefixLift 6190279
  have htrace : WordTrace (prefixWord ++ tailWord_6190279) baseStart_6190279 baseEnd_6190279 := by
    simpa [prefixWord, tailWord_6190279, baseEnd_6190279] using wordTrace_append hprefix tailTrace_6190279
  have hstable : (prefixWord ++ tailWord_6190279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190279).length < 2 ^ (prefixWord ++ tailWord_6190279).sum := by decide
  have hdescent : baseEnd_6190279 < baseStart_6190279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190309 : List Nat := [1, 3, 1, 4, 3, 2, 9]
def baseStart_6190309 : Nat := 118140960795 + 6190309 * 2 ^ 59
def prefixEnd_6190309 : Nat := 4983230072969 + 3 ^ 40 * 6190309 * 2
def baseEnd_6190309 : Nat := 39242023664853408904553

theorem tailTrace_6190309 : CollatzResearch.WordTrace tailWord_6190309 prefixEnd_6190309 39242023664853408904553 := by
  unfold tailWord_6190309
  simp only [CollatzResearch.WordTrace]
  refine ⟨225779117730575188452677981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150519411820383458968451987 225779117730575188452677981)
  ·
    refine ⟨84667169148965695669754243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225779117730575188452677981 84667169148965695669754243)
    ·
      refine ⟨127000753723448543504631365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84667169148965695669754243 127000753723448543504631365)
      ·
        refine ⟨23812641323146601907118381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127000753723448543504631365 23812641323146601907118381)
        ·
          refine ⟨8929740496179975715169393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23812641323146601907118381 8929740496179975715169393)
          ·
            refine ⟨6697305372134981786377045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929740496179975715169393 6697305372134981786377045)
            ·
              refine ⟨39242023664853408904553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6697305372134981786377045 39242023664853408904553)
              ·
                rfl

theorem cell23_6190309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 9].length) (baseStart_6190309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190309 prefixEnd_6190309 := by exact prefixLift 6190309
  have htrace : WordTrace (prefixWord ++ tailWord_6190309) baseStart_6190309 baseEnd_6190309 := by
    simpa [prefixWord, tailWord_6190309, baseEnd_6190309] using wordTrace_append hprefix tailTrace_6190309
  have hstable : (prefixWord ++ tailWord_6190309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190309).length < 2 ^ (prefixWord ++ tailWord_6190309).sum := by decide
  have hdescent : baseEnd_6190309 < baseStart_6190309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190370 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_6190370 : Nat := 118140960795 + 6190370 * 2 ^ 59
def prefixEnd_6190370 : Nat := 4983230072969 + 3 ^ 40 * 6190370 * 2
def baseEnd_6190370 : Nat := 3178635239173050382606013

theorem tailTrace_6190370 : CollatzResearch.WordTrace tailWord_6190370 prefixEnd_6190370 3178635239173050382606013 := by
  unfold tailWord_6190370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56445335645838548967662141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150520895055569463913765709 56445335645838548967662141)
  ·
    refine ⟨21167000867189455862873303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56445335645838548967662141 21167000867189455862873303)
    ·
      refine ⟨31750501300784183794309955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21167000867189455862873303 31750501300784183794309955)
      ·
        refine ⟨47625751951176275691464933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31750501300784183794309955 47625751951176275691464933)
        ·
          refine ⟨8929828490845551692149675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47625751951176275691464933 8929828490845551692149675)
          ·
            refine ⟨13394742736268327538224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8929828490845551692149675 13394742736268327538224513)
            ·
              refine ⟨10046057052201245653668385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13394742736268327538224513 10046057052201245653668385)
              ·
                refine ⟨7534542789150934240251289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046057052201245653668385 7534542789150934240251289)
                ·
                  refine ⟨5650907091863200680188467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7534542789150934240251289 5650907091863200680188467)
                  ·
                    refine ⟨8476360637794801020282701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5650907091863200680188467 8476360637794801020282701)
                    ·
                      refine ⟨3178635239173050382606013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476360637794801020282701 3178635239173050382606013)
                      ·
                        rfl

theorem cell23_6190370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_6190370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190370 prefixEnd_6190370 := by exact prefixLift 6190370
  have htrace : WordTrace (prefixWord ++ tailWord_6190370) baseStart_6190370 baseEnd_6190370 := by
    simpa [prefixWord, tailWord_6190370, baseEnd_6190370] using wordTrace_append hprefix tailTrace_6190370
  have hstable : (prefixWord ++ tailWord_6190370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190370).length < 2 ^ (prefixWord ++ tailWord_6190370).sum := by decide
  have hdescent : baseEnd_6190370 < baseStart_6190370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190389 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_6190389 : Nat := 118140960795 + 6190389 * 2 ^ 59
def prefixEnd_6190389 : Nat := 4983230072969 + 3 ^ 40 * 6190389 * 2
def baseEnd_6190389 : Nat := 3178644995305485808268425

theorem tailTrace_6190389 : CollatzResearch.WordTrace tailWord_6190389 prefixEnd_6190389 3178644995305485808268425 := by
  unfold tailWord_6190389
  simp only [CollatzResearch.WordTrace]
  refine ⟨225782035570285362115590221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150521357046856908077060147 225782035570285362115590221)
  ·
    refine ⟨84668263338857010793346333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225782035570285362115590221 84668263338857010793346333)
    ·
      refine ⟨31750598752071379047504875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84668263338857010793346333 31750598752071379047504875)
      ·
        refine ⟨47625898128107068571257313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31750598752071379047504875 47625898128107068571257313)
        ·
          refine ⟨35719423596080301428442985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47625898128107068571257313 35719423596080301428442985)
          ·
            refine ⟨26789567697060226071332239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35719423596080301428442985 26789567697060226071332239)
            ·
              refine ⟨40184351545590339106998359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26789567697060226071332239 40184351545590339106998359)
              ·
                refine ⟨60276527318385508660497539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40184351545590339106998359 60276527318385508660497539)
                ·
                  refine ⟨90414790977578262990746309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60276527318385508660497539 90414790977578262990746309)
                  ·
                    refine ⟨16952773308295924310764933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90414790977578262990746309 16952773308295924310764933)
                    ·
                      refine ⟨3178644995305485808268425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16952773308295924310764933 3178644995305485808268425)
                      ·
                        rfl

theorem cell23_6190389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_6190389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190389 prefixEnd_6190389 := by exact prefixLift 6190389
  have htrace : WordTrace (prefixWord ++ tailWord_6190389) baseStart_6190389 baseEnd_6190389 := by
    simpa [prefixWord, tailWord_6190389, baseEnd_6190389] using wordTrace_append hprefix tailTrace_6190389
  have hstable : (prefixWord ++ tailWord_6190389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190389).length < 2 ^ (prefixWord ++ tailWord_6190389).sum := by decide
  have hdescent : baseEnd_6190389 < baseStart_6190389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190399 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 7]
def baseStart_6190399 : Nat := 118140960795 + 6190399 * 2 ^ 59
def prefixEnd_6190399 : Nat := 4983230072969 + 3 ^ 40 * 6190399 * 2
def baseEnd_6190399 : Nat := 353183347790225641015931

theorem tailTrace_6190399 : CollatzResearch.WordTrace tailWord_6190399 prefixEnd_6190399 353183347790225641015931 := by
  unfold tailWord_6190399
  simp only [CollatzResearch.WordTrace]
  refine ⟨225782400300249133823454251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150521600200166089215636167 225782400300249133823454251)
  ·
    refine ⟨338673600450373700735181377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225782400300249133823454251 338673600450373700735181377)
    ·
      refine ⟨254005200337780275551386033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338673600450373700735181377 254005200337780275551386033)
      ·
        refine ⟨190503900253335206663539525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254005200337780275551386033 190503900253335206663539525)
        ·
          refine ⟨35719481297500351249413661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190503900253335206663539525 35719481297500351249413661)
          ·
            refine ⟨13394805486562631718530123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35719481297500351249413661 13394805486562631718530123)
            ·
              refine ⟨20092208229843947577795185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13394805486562631718530123 20092208229843947577795185)
              ·
                refine ⟨15069156172382960683346389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20092208229843947577795185 15069156172382960683346389)
                ·
                  refine ⟨353183347790225641015931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15069156172382960683346389 353183347790225641015931)
                  ·
                    rfl

theorem cell23_6190399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 7].length) (baseStart_6190399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190399 prefixEnd_6190399 := by exact prefixLift 6190399
  have htrace : WordTrace (prefixWord ++ tailWord_6190399) baseStart_6190399 baseEnd_6190399 := by
    simpa [prefixWord, tailWord_6190399, baseEnd_6190399] using wordTrace_append hprefix tailTrace_6190399
  have hstable : (prefixWord ++ tailWord_6190399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190399).length < 2 ^ (prefixWord ++ tailWord_6190399).sum := by decide
  have hdescent : baseEnd_6190399 < baseStart_6190399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190416 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 5]
def baseStart_6190416 : Nat := 118140960795 + 6190416 * 2 ^ 59
def prefixEnd_6190416 : Nat := 4983230072969 + 3 ^ 40 * 6190416 * 2
def baseEnd_6190416 : Nat := 353184317698128578070089

theorem tailTrace_6190416 : CollatzResearch.WordTrace tailWord_6190416 prefixEnd_6190416 353184317698128578070089 := by
  unfold tailWord_6190416
  simp only [CollatzResearch.WordTrace]
  refine ⟨112891510170593772863411551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150522013560791697151215401 112891510170593772863411551)
  ·
    refine ⟨169337265255890659295117327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112891510170593772863411551 169337265255890659295117327)
    ·
      refine ⟨254005897883835988942675991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169337265255890659295117327 254005897883835988942675991)
      ·
        refine ⟨381008846825753983414013987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254005897883835988942675991 381008846825753983414013987)
        ·
          refine ⟨571513270238630975121020981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381008846825753983414013987 571513270238630975121020981)
          ·
            refine ⟨53579369084871653917595717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 571513270238630975121020981 53579369084871653917595717)
            ·
              refine ⟨10046131703413435109549197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53579369084871653917595717 10046131703413435109549197)
              ·
                refine ⟨3767299388780038166080949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10046131703413435109549197 3767299388780038166080949)
                ·
                  refine ⟨353184317698128578070089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767299388780038166080949 353184317698128578070089)
                  ·
                    rfl

theorem cell23_6190416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 5].length) (baseStart_6190416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190416 prefixEnd_6190416 := by exact prefixLift 6190416
  have htrace : WordTrace (prefixWord ++ tailWord_6190416) baseStart_6190416 baseEnd_6190416 := by
    simpa [prefixWord, tailWord_6190416, baseEnd_6190416] using wordTrace_append hprefix tailTrace_6190416
  have hstable : (prefixWord ++ tailWord_6190416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190416).length < 2 ^ (prefixWord ++ tailWord_6190416).sum := by decide
  have hdescent : baseEnd_6190416 < baseStart_6190416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190449 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_6190449 : Nat := 118140960795 + 6190449 * 2 ^ 59
def prefixEnd_6190449 : Nat := 4983230072969 + 3 ^ 40 * 6190449 * 2
def baseEnd_6190449 : Nat := 3178675804144755573518149

theorem tailTrace_6190449 : CollatzResearch.WordTrace tailWord_6190449 prefixEnd_6190449 3178675804144755573518149 := by
  unfold tailWord_6190449
  simp only [CollatzResearch.WordTrace]
  refine ⟨225784223950067992362774401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150522815966711994908516267 225784223950067992362774401)
  ·
    refine ⟨169338167962550994272080801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225784223950067992362774401 169338167962550994272080801)
    ·
      refine ⟨127003625971913245704060601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169338167962550994272080801 127003625971913245704060601)
      ·
        refine ⟨95252719478934934278045451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127003625971913245704060601 95252719478934934278045451)
        ·
          refine ⟨142879079218402401417068177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95252719478934934278045451 142879079218402401417068177)
          ·
            refine ⟨107159309413801801062801133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142879079218402401417068177 107159309413801801062801133)
            ·
              refine ⟨40184741030175675398550425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107159309413801801062801133 40184741030175675398550425)
              ·
                refine ⟨30138555772631756548912819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40184741030175675398550425 30138555772631756548912819)
                ·
                  refine ⟨45207833658947634823369229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30138555772631756548912819 45207833658947634823369229)
                  ·
                    refine ⟨16952937622105363058763461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45207833658947634823369229 16952937622105363058763461)
                    ·
                      refine ⟨3178675804144755573518149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16952937622105363058763461 3178675804144755573518149)
                      ·
                        rfl

theorem cell23_6190449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_6190449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190449 prefixEnd_6190449 := by exact prefixLift 6190449
  have htrace : WordTrace (prefixWord ++ tailWord_6190449) baseStart_6190449 baseEnd_6190449 := by
    simpa [prefixWord, tailWord_6190449, baseEnd_6190449] using wordTrace_append hprefix tailTrace_6190449
  have hstable : (prefixWord ++ tailWord_6190449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190449).length < 2 ^ (prefixWord ++ tailWord_6190449).sum := by decide
  have hdescent : baseEnd_6190449 < baseStart_6190449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190489 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 8]
def baseStart_6190489 : Nat := 118140960795 + 6190489 * 2 ^ 59
def prefixEnd_6190489 : Nat := 4983230072969 + 3 ^ 40 * 6190489 * 2
def baseEnd_6190489 : Nat := 353188482596770601890885

theorem tailTrace_6190489 : CollatzResearch.WordTrace tailWord_6190489 prefixEnd_6190489 353188482596770601890885 := by
  unfold tailWord_6190489
  simp only [CollatzResearch.WordTrace]
  refine ⟨225785682869923079194230521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150523788579948719462820347 225785682869923079194230521)
  ·
    refine ⟨169339262152442309395672891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225785682869923079194230521 169339262152442309395672891)
    ·
      refine ⟨254008893228663464093509337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169339262152442309395672891 254008893228663464093509337)
      ·
        refine ⟨190506669921497598070132003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254008893228663464093509337 190506669921497598070132003)
        ·
          refine ⟨285760004882246397105198005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190506669921497598070132003 285760004882246397105198005)
          ·
            refine ⟨26790000457710599728612313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285760004882246397105198005 26790000457710599728612313)
            ·
              refine ⟨20092500343282949796459235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26790000457710599728612313 20092500343282949796459235)
              ·
                refine ⟨30138750514924424694688853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20092500343282949796459235 30138750514924424694688853)
                ·
                  refine ⟨353188482596770601890885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30138750514924424694688853 353188482596770601890885)
                  ·
                    rfl

theorem cell23_6190489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_6190489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190489 prefixEnd_6190489 := by exact prefixLift 6190489
  have htrace : WordTrace (prefixWord ++ tailWord_6190489) baseStart_6190489 baseEnd_6190489 := by
    simpa [prefixWord, tailWord_6190489, baseEnd_6190489] using wordTrace_append hprefix tailTrace_6190489
  have hstable : (prefixWord ++ tailWord_6190489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190489).length < 2 ^ (prefixWord ++ tailWord_6190489).sum := by decide
  have hdescent : baseEnd_6190489 < baseStart_6190489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190493 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_6190493 : Nat := 118140960795 + 6190493 * 2 ^ 59
def prefixEnd_6190493 : Nat := 4983230072969 + 3 ^ 40 * 6190493 * 2
def baseEnd_6190493 : Nat := 1059566132431184467122649

theorem tailTrace_6190493 : CollatzResearch.WordTrace tailWord_6190493 prefixEnd_6190493 1059566132431184467122649 := by
  unfold tailWord_6190493
  simp only [CollatzResearch.WordTrace]
  refine ⟨225785828761908587877376133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150523885841272391918250755 225785828761908587877376133)
  ·
    refine ⟨42334842892857860227008025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225785828761908587877376133 42334842892857860227008025)
    ·
      refine ⟨31751132169643395170256019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42334842892857860227008025 31751132169643395170256019)
      ·
        refine ⟨47626698254465092755384029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31751132169643395170256019 47626698254465092755384029)
        ·
          refine ⟨17860011845424409783269011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47626698254465092755384029 17860011845424409783269011)
          ·
            refine ⟨26790017768136614674903517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17860011845424409783269011 26790017768136614674903517)
            ·
              refine ⟨10046256663051230503088819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26790017768136614674903517 10046256663051230503088819)
              ·
                refine ⟨15069384994576845754633229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046256663051230503088819 15069384994576845754633229)
                ·
                  refine ⟨5651019372966317157987461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15069384994576845754633229 5651019372966317157987461)
                  ·
                    refine ⟨1059566132431184467122649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651019372966317157987461 1059566132431184467122649)
                    ·
                      rfl

theorem cell23_6190493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_6190493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190493 prefixEnd_6190493 := by exact prefixLift 6190493
  have htrace : WordTrace (prefixWord ++ tailWord_6190493) baseStart_6190493 baseEnd_6190493 := by
    simpa [prefixWord, tailWord_6190493, baseEnd_6190493] using wordTrace_append hprefix tailTrace_6190493
  have hstable : (prefixWord ++ tailWord_6190493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190493).length < 2 ^ (prefixWord ++ tailWord_6190493).sum := by decide
  have hdescent : baseEnd_6190493 < baseStart_6190493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190543 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 2, 3, 2]
def baseStart_6190543 : Nat := 118140960795 + 6190543 * 2 ^ 59
def prefixEnd_6190543 : Nat := 4983230072969 + 3 ^ 40 * 6190543 * 2
def baseEnd_6190543 : Nat := 3178724071326278205742717

theorem tailTrace_6190543 : CollatzResearch.WordTrace tailWord_6190543 prefixEnd_6190543 3178724071326278205742717 := by
  unfold tailWord_6190543
  simp only [CollatzResearch.WordTrace]
  refine ⟨225787652411727446416696283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150525101607818297611130855 225787652411727446416696283)
  ·
    refine ⟨338681478617591169625044425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225787652411727446416696283 338681478617591169625044425)
    ·
      refine ⟨254011108963193377218783319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338681478617591169625044425 254011108963193377218783319)
      ·
        refine ⟨381016663444790065828174979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254011108963193377218783319 381016663444790065828174979)
        ·
          refine ⟨571524995167185098742262469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381016663444790065828174979 571524995167185098742262469)
          ·
            refine ⟨107160936593847206014174213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571524995167185098742262469 107160936593847206014174213)
            ·
              refine ⟨20092675611346351127657665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107160936593847206014174213 20092675611346351127657665)
              ·
                refine ⟨15069506708509763345743249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20092675611346351127657665 15069506708509763345743249)
                ·
                  refine ⟨11302130031382322509307437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15069506708509763345743249 11302130031382322509307437)
                  ·
                    refine ⟨4238298761768370940990289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11302130031382322509307437 4238298761768370940990289)
                    ·
                      refine ⟨3178724071326278205742717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238298761768370940990289 3178724071326278205742717)
                      ·
                        rfl

theorem cell23_6190543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3, 2].length) (baseStart_6190543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190543 prefixEnd_6190543 := by exact prefixLift 6190543
  have htrace : WordTrace (prefixWord ++ tailWord_6190543) baseStart_6190543 baseEnd_6190543 := by
    simpa [prefixWord, tailWord_6190543, baseEnd_6190543] using wordTrace_append hprefix tailTrace_6190543
  have hstable : (prefixWord ++ tailWord_6190543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190543).length < 2 ^ (prefixWord ++ tailWord_6190543).sum := by decide
  have hdescent : baseEnd_6190543 < baseStart_6190543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_6190569 : Nat := 118140960795 + 6190569 * 2 ^ 59
def prefixEnd_6190569 : Nat := 4983230072969 + 3 ^ 40 * 6190569 * 2
def baseEnd_6190569 : Nat := 3178737421823295104017597

theorem tailTrace_6190569 : CollatzResearch.WordTrace tailWord_6190569 prefixEnd_6190569 3178737421823295104017597 := by
  unfold tailWord_6190569
  simp only [CollatzResearch.WordTrace]
  refine ⟨225788600709633252857142761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150525733806422168571428507 225788600709633252857142761)
  ·
    refine ⟨169341450532224939642857071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225788600709633252857142761 169341450532224939642857071)
    ·
      refine ⟨254012175798337409464285607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169341450532224939642857071 254012175798337409464285607)
      ·
        refine ⟨381018263697506114196428411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254012175798337409464285607 381018263697506114196428411)
        ·
          refine ⟨571527395546259171294642617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381018263697506114196428411 571527395546259171294642617)
          ·
            refine ⟨428645546659694378470981963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571527395546259171294642617 428645546659694378470981963)
            ·
              refine ⟨642968319989541567706472945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428645546659694378470981963 642968319989541567706472945)
              ·
                refine ⟨482226239992156175779854709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642968319989541567706472945 482226239992156175779854709)
                ·
                  refine ⟨45208709999264641479361379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482226239992156175779854709 45208709999264641479361379)
                  ·
                    refine ⟨67813064998896962219042069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45208709999264641479361379 67813064998896962219042069)
                    ·
                      refine ⟨3178737421823295104017597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67813064998896962219042069 3178737421823295104017597)
                      ·
                        rfl

theorem cell23_6190569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_6190569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190569 prefixEnd_6190569 := by exact prefixLift 6190569
  have htrace : WordTrace (prefixWord ++ tailWord_6190569) baseStart_6190569 baseEnd_6190569 := by
    simpa [prefixWord, tailWord_6190569, baseEnd_6190569] using wordTrace_append hprefix tailTrace_6190569
  have hstable : (prefixWord ++ tailWord_6190569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190569).length < 2 ^ (prefixWord ++ tailWord_6190569).sum := by decide
  have hdescent : baseEnd_6190569 < baseStart_6190569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190586 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_6190586 : Nat := 118140960795 + 6190586 * 2 ^ 59
def prefixEnd_6190586 : Nat := 4983230072969 + 3 ^ 40 * 6190586 * 2
def baseEnd_6190586 : Nat := 3178746150994421537505019

theorem tailTrace_6190586 : CollatzResearch.WordTrace tailWord_6190586 prefixEnd_6190586 3178746150994421537505019 := by
  unfold tailWord_6190586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56447305187642916190127903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150526147167047776507007741 56447305187642916190127903)
  ·
    refine ⟨84670957781464374285191855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56447305187642916190127903 84670957781464374285191855)
    ·
      refine ⟨127006436672196561427787783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84670957781464374285191855 127006436672196561427787783)
      ·
        refine ⟨190509655008294842141681675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127006436672196561427787783 190509655008294842141681675)
        ·
          refine ⟨285764482512442263212522513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190509655008294842141681675 285764482512442263212522513)
          ·
            refine ⟨214323361884331697409391885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285764482512442263212522513 214323361884331697409391885)
            ·
              refine ⟨80371260706624386528521957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214323361884331697409391885 80371260706624386528521957)
              ·
                refine ⟨15069611382492072474097867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80371260706624386528521957 15069611382492072474097867)
                ·
                  refine ⟨22604417073738108711146801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15069611382492072474097867 22604417073738108711146801)
                  ·
                    refine ⟨16953312805303581533360101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22604417073738108711146801 16953312805303581533360101)
                    ·
                      refine ⟨3178746150994421537505019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16953312805303581533360101 3178746150994421537505019)
                      ·
                        rfl

theorem cell23_6190586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_6190586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190586 prefixEnd_6190586 := by exact prefixLift 6190586
  have htrace : WordTrace (prefixWord ++ tailWord_6190586) baseStart_6190586 baseEnd_6190586 := by
    simpa [prefixWord, tailWord_6190586, baseEnd_6190586] using wordTrace_append hprefix tailTrace_6190586
  have hstable : (prefixWord ++ tailWord_6190586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190586).length < 2 ^ (prefixWord ++ tailWord_6190586).sum := by decide
  have hdescent : baseEnd_6190586 < baseStart_6190586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190623 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_6190623 : Nat := 118140960795 + 6190623 * 2 ^ 59
def prefixEnd_6190623 : Nat := 4983230072969 + 3 ^ 40 * 6190623 * 2
def baseEnd_6190623 : Nat := 3178765149778637892742349

theorem tailTrace_6190623 : CollatzResearch.WordTrace tailWord_6190623 prefixEnd_6190623 3178765149778637892742349 := by
  unfold tailWord_6190623
  simp only [CollatzResearch.WordTrace]
  refine ⟨225790570251437620079608523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150527046834291746719739015 225790570251437620079608523)
  ·
    refine ⟨338685855377156430119412785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225790570251437620079608523 338685855377156430119412785)
    ·
      refine ⟨254014391532867322589559589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338685855377156430119412785 254014391532867322589559589)
      ·
        refine ⟨47627698412412622985542423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254014391532867322589559589 47627698412412622985542423)
        ·
          refine ⟨71441547618618934478313635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47627698412412622985542423 71441547618618934478313635)
          ·
            refine ⟨107162321427928401717470453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71441547618618934478313635 107162321427928401717470453)
            ·
              refine ⟨10046467633868287661012855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107162321427928401717470453 10046467633868287661012855)
              ·
                refine ⟨15069701450802431491519283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046467633868287661012855 15069701450802431491519283)
                ·
                  refine ⟨22604552176203647237278925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15069701450802431491519283 22604552176203647237278925)
                  ·
                    refine ⟨8476707066076367713979597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22604552176203647237278925 8476707066076367713979597)
                    ·
                      refine ⟨3178765149778637892742349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476707066076367713979597 3178765149778637892742349)
                      ·
                        rfl

theorem cell23_6190623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_6190623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190623 prefixEnd_6190623 := by exact prefixLift 6190623
  have htrace : WordTrace (prefixWord ++ tailWord_6190623) baseStart_6190623 baseEnd_6190623 := by
    simpa [prefixWord, tailWord_6190623, baseEnd_6190623] using wordTrace_append hprefix tailTrace_6190623
  have hstable : (prefixWord ++ tailWord_6190623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190623).length < 2 ^ (prefixWord ++ tailWord_6190623).sum := by decide
  have hdescent : baseEnd_6190623 < baseStart_6190623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190626 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6190626 : Nat := 118140960795 + 6190626 * 2 ^ 59
def prefixEnd_6190626 : Nat := 4983230072969 + 3 ^ 40 * 6190626 * 2
def baseEnd_6190626 : Nat := 1059588896740200460334945

theorem tailTrace_6190626 : CollatzResearch.WordTrace tailWord_6190626 prefixEnd_6190626 1059588896740200460334945 := by
  unfold tailWord_6190626
  simp only [CollatzResearch.WordTrace]
  refine ⟨56447669917606687897991933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150527119780284501061311821 56447669917606687897991933)
  ·
    refine ⟨21167876219102507961746975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56447669917606687897991933 21167876219102507961746975)
    ·
      refine ⟨31751814328653761942620463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21167876219102507961746975 31751814328653761942620463)
      ·
        refine ⟨47627721492980642913930695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31751814328653761942620463 47627721492980642913930695)
        ·
          refine ⟨71441582239470964370896043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47627721492980642913930695 71441582239470964370896043)
          ·
            refine ⟨107162373359206446556344065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71441582239470964370896043 107162373359206446556344065)
            ·
              refine ⟨80371780019404834917258049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107162373359206446556344065 80371780019404834917258049)
              ·
                refine ⟨60278835014553626187943537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80371780019404834917258049 60278835014553626187943537)
                ·
                  refine ⟨45209126260915219640957653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60278835014553626187943537 45209126260915219640957653)
                  ·
                    refine ⟨1059588896740200460334945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45209126260915219640957653 1059588896740200460334945)
                    ·
                      rfl

theorem cell23_6190626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6190626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190626 prefixEnd_6190626 := by exact prefixLift 6190626
  have htrace : WordTrace (prefixWord ++ tailWord_6190626) baseStart_6190626 baseEnd_6190626 := by
    simpa [prefixWord, tailWord_6190626, baseEnd_6190626] using wordTrace_append hprefix tailTrace_6190626
  have hstable : (prefixWord ++ tailWord_6190626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190626).length < 2 ^ (prefixWord ++ tailWord_6190626).sum := by decide
  have hdescent : baseEnd_6190626 < baseStart_6190626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190650 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_6190650 : Nat := 118140960795 + 6190650 * 2 ^ 59
def prefixEnd_6190650 : Nat := 4983230072969 + 3 ^ 40 * 6190650 * 2
def baseEnd_6190650 : Nat := 3178779013756309287104725

theorem tailTrace_6190650 : CollatzResearch.WordTrace tailWord_6190650 prefixEnd_6190650 3178779013756309287104725 := by
  unfold tailWord_6190650
  simp only [CollatzResearch.WordTrace]
  refine ⟨56447888755584950922710351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150527703348226535793894269 56447888755584950922710351)
  ·
    refine ⟨84671833133377426384065527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56447888755584950922710351 84671833133377426384065527)
    ·
      refine ⟨127007749700066139576098291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84671833133377426384065527 127007749700066139576098291)
      ·
        refine ⟨190511624550099209364147437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127007749700066139576098291 190511624550099209364147437)
        ·
          refine ⟨71441859206287203511555289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190511624550099209364147437 71441859206287203511555289)
          ·
            refine ⟨53581394404715402633666467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71441859206287203511555289 53581394404715402633666467)
            ·
              refine ⟨80372091607073103950499701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53581394404715402633666467 80372091607073103950499701)
              ·
                refine ⟨7534883588163103495359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80372091607073103950499701 7534883588163103495359347)
                ·
                  refine ⟨11302325382244655243039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534883588163103495359347 11302325382244655243039021)
                  ·
                    refine ⟨4238372018341745716139633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11302325382244655243039021 4238372018341745716139633)
                    ·
                      refine ⟨3178779013756309287104725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238372018341745716139633 3178779013756309287104725)
                      ·
                        rfl

theorem cell23_6190650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_6190650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190650 prefixEnd_6190650 := by exact prefixLift 6190650
  have htrace : WordTrace (prefixWord ++ tailWord_6190650) baseStart_6190650 baseEnd_6190650 := by
    simpa [prefixWord, tailWord_6190650, baseEnd_6190650] using wordTrace_append hprefix tailTrace_6190650
  have hstable : (prefixWord ++ tailWord_6190650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190650).length < 2 ^ (prefixWord ++ tailWord_6190650).sum := by decide
  have hdescent : baseEnd_6190650 < baseStart_6190650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190666 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6190666 : Nat := 118140960795 + 6190666 * 2 ^ 59
def prefixEnd_6190666 : Nat := 4983230072969 + 3 ^ 40 * 6190666 * 2
def baseEnd_6190666 : Nat := 3178787229446781224504651

theorem tailTrace_6190666 : CollatzResearch.WordTrace tailWord_6190666 prefixEnd_6190666 3178787229446781224504651 := by
  unfold tailWord_6190666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448034647570459605855963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150528092393521225615615901 56448034647570459605855963)
  ·
    refine ⟨84672051971355689408783945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56448034647570459605855963 84672051971355689408783945)
    ·
      refine ⟨63504038978516767056587959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84672051971355689408783945 63504038978516767056587959)
      ·
        refine ⟨95256058467775150584881939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63504038978516767056587959 95256058467775150584881939)
        ·
          refine ⟨142884087701662725877322909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95256058467775150584881939 142884087701662725877322909)
          ·
            refine ⟨53581532888123522203996091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142884087701662725877322909 53581532888123522203996091)
            ·
              refine ⟨80372299332185283305994137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53581532888123522203996091 80372299332185283305994137)
              ·
                refine ⟨60279224499138962479495603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80372299332185283305994137 60279224499138962479495603)
                ·
                  refine ⟨90418836748708443719243405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60279224499138962479495603 90418836748708443719243405)
                  ·
                    refine ⟨33907063780765666394716277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90418836748708443719243405 33907063780765666394716277)
                    ·
                      refine ⟨3178787229446781224504651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33907063780765666394716277 3178787229446781224504651)
                      ·
                        rfl

theorem cell23_6190666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6190666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190666 prefixEnd_6190666 := by exact prefixLift 6190666
  have htrace : WordTrace (prefixWord ++ tailWord_6190666) baseStart_6190666 baseEnd_6190666 := by
    simpa [prefixWord, tailWord_6190666, baseEnd_6190666] using wordTrace_append hprefix tailTrace_6190666
  have hstable : (prefixWord ++ tailWord_6190666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190666).length < 2 ^ (prefixWord ++ tailWord_6190666).sum := by decide
  have hdescent : baseEnd_6190666 < baseStart_6190666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190674 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_6190674 : Nat := 118140960795 + 6190674 * 2 ^ 59
def prefixEnd_6190674 : Nat := 4983230072969 + 3 ^ 40 * 6190674 * 2
def baseEnd_6190674 : Nat := 3178791337292017193204615

theorem tailTrace_6190674 : CollatzResearch.WordTrace tailWord_6190674 prefixEnd_6190674 3178791337292017193204615 := by
  unfold tailWord_6190674
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448107593563213947428769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150528286916168570526476717 56448107593563213947428769)
  ·
    refine ⟨42336080695172410460571577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56448107593563213947428769 42336080695172410460571577)
    ·
      refine ⟨31752060521379307845428683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42336080695172410460571577 31752060521379307845428683)
      ·
        refine ⟨47628090782068961768143025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31752060521379307845428683 47628090782068961768143025)
        ·
          refine ⟨35721068086551721326107269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47628090782068961768143025 35721068086551721326107269)
          ·
            refine ⟨6697700266228447748645113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35721068086551721326107269 6697700266228447748645113)
            ·
              refine ⟨5023275199671335811483835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697700266228447748645113 5023275199671335811483835)
              ·
                refine ⟨7534912799507003717225753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023275199671335811483835 7534912799507003717225753)
                ·
                  refine ⟨5651184599630252787919315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7534912799507003717225753 5651184599630252787919315)
                  ·
                    refine ⟨8476776899445379181878973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5651184599630252787919315 8476776899445379181878973)
                    ·
                      refine ⟨3178791337292017193204615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476776899445379181878973 3178791337292017193204615)
                      ·
                        rfl

theorem cell23_6190674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_6190674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190674 prefixEnd_6190674 := by exact prefixLift 6190674
  have htrace : WordTrace (prefixWord ++ tailWord_6190674) baseStart_6190674 baseEnd_6190674 := by
    simpa [prefixWord, tailWord_6190674, baseEnd_6190674] using wordTrace_append hprefix tailTrace_6190674
  have hstable : (prefixWord ++ tailWord_6190674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190674).length < 2 ^ (prefixWord ++ tailWord_6190674).sum := by decide
  have hdescent : baseEnd_6190674 < baseStart_6190674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190678 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6190678 : Nat := 118140960795 + 6190678 * 2 ^ 59
def prefixEnd_6190678 : Nat := 4983230072969 + 3 ^ 40 * 6190678 * 2
def baseEnd_6190678 : Nat := 3178793391214635177554597

theorem tailTrace_6190678 : CollatzResearch.WordTrace tailWord_6190678 prefixEnd_6190678 3178793391214635177554597 := by
  unfold tailWord_6190678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112036016639897779553793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150528384177492242981907125 14112036016639897779553793)
  ·
    refine ⟨10584027012479923334665345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14112036016639897779553793 10584027012479923334665345)
    ·
      refine ⟨7938020259359942500999009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10584027012479923334665345 7938020259359942500999009)
      ·
        refine ⟨5953515194519956875749257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938020259359942500999009 5953515194519956875749257)
        ·
          refine ⟨4465136395889967656811943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5953515194519956875749257 4465136395889967656811943)
          ·
            refine ⟨6697704593834951485217915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465136395889967656811943 6697704593834951485217915)
            ·
              refine ⟨10046556890752427227826873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697704593834951485217915 10046556890752427227826873)
              ·
                refine ⟨7534917668064320420870155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046556890752427227826873 7534917668064320420870155)
                ·
                  refine ⟨11302376502096480631305233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534917668064320420870155 11302376502096480631305233)
                  ·
                    refine ⟨8476782376572360473478925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11302376502096480631305233 8476782376572360473478925)
                    ·
                      refine ⟨3178793391214635177554597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476782376572360473478925 3178793391214635177554597)
                      ·
                        rfl

theorem cell23_6190678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6190678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190678 prefixEnd_6190678 := by exact prefixLift 6190678
  have htrace : WordTrace (prefixWord ++ tailWord_6190678) baseStart_6190678 baseEnd_6190678 := by
    simpa [prefixWord, tailWord_6190678, baseEnd_6190678] using wordTrace_append hprefix tailTrace_6190678
  have hstable : (prefixWord ++ tailWord_6190678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190678).length < 2 ^ (prefixWord ++ tailWord_6190678).sum := by decide
  have hdescent : baseEnd_6190678 < baseStart_6190678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190684 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6190684 : Nat := 118140960795 + 6190684 * 2 ^ 59
def prefixEnd_6190684 : Nat := 4983230072969 + 3 ^ 40 * 6190684 * 2
def baseEnd_6190684 : Nat := 3178796472098562154079569

theorem tailTrace_6190684 : CollatzResearch.WordTrace tailWord_6190684 prefixEnd_6190684 3178796472098562154079569 := by
  unfold tailWord_6190684
  simp only [CollatzResearch.WordTrace]
  refine ⟨112896397552108313748789553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150528530069477751665052737 112896397552108313748789553)
  ·
    refine ⟨84672298164081235311592165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112896397552108313748789553 84672298164081235311592165)
    ·
      refine ⟨15876055905765231620923531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84672298164081235311592165 15876055905765231620923531)
      ·
        refine ⟨23814083858647847431385297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15876055905765231620923531 23814083858647847431385297)
        ·
          refine ⟨17860562893985885573538973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23814083858647847431385297 17860562893985885573538973)
          ·
            refine ⟨6697711085244707090077115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17860562893985885573538973 6697711085244707090077115)
            ·
              refine ⟨10046566627867060635115673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697711085244707090077115 10046566627867060635115673)
              ·
                refine ⟨7534924970900295476336755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046566627867060635115673 7534924970900295476336755)
                ·
                  refine ⟨11302387456350443214505133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534924970900295476336755 11302387456350443214505133)
                  ·
                    refine ⟨4238395296131416205439425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11302387456350443214505133 4238395296131416205439425)
                    ·
                      refine ⟨3178796472098562154079569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238395296131416205439425 3178796472098562154079569)
                      ·
                        rfl

theorem cell23_6190684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6190684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190684 prefixEnd_6190684 := by exact prefixLift 6190684
  have htrace : WordTrace (prefixWord ++ tailWord_6190684) baseStart_6190684 baseEnd_6190684 := by
    simpa [prefixWord, tailWord_6190684, baseEnd_6190684] using wordTrace_append hprefix tailTrace_6190684
  have hstable : (prefixWord ++ tailWord_6190684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190684).length < 2 ^ (prefixWord ++ tailWord_6190684).sum := by decide
  have hdescent : baseEnd_6190684 < baseStart_6190684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190703 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 5]
def baseStart_6190703 : Nat := 118140960795 + 6190703 * 2 ^ 59
def prefixEnd_6190703 : Nat := 4983230072969 + 3 ^ 40 * 6190703 * 2
def baseEnd_6190703 : Nat := 353200692025666397749109

theorem tailTrace_6190703 : CollatzResearch.WordTrace tailWord_6190703 prefixEnd_6190703 353200692025666397749109 := by
  unfold tailWord_6190703
  simp only [CollatzResearch.WordTrace]
  refine ⟨225793488091147793742520763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150528992060765195828347175 225793488091147793742520763)
  ·
    refine ⟨338690232136721690613781145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225793488091147793742520763 338690232136721690613781145)
    ·
      refine ⟨254017674102541267960335859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338690232136721690613781145 254017674102541267960335859)
      ·
        refine ⟨381026511153811901940503789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254017674102541267960335859 381026511153811901940503789)
        ·
          refine ⟨142884941682679463227688921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381026511153811901940503789 142884941682679463227688921)
          ·
            refine ⟨107163706262009597420766691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142884941682679463227688921 107163706262009597420766691)
            ·
              refine ⟨160745559393014396131150037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107163706262009597420766691 160745559393014396131150037)
              ·
                refine ⟨3767474048273774909323829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160745559393014396131150037 3767474048273774909323829)
                ·
                  refine ⟨353200692025666397749109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767474048273774909323829 353200692025666397749109)
                  ·
                    rfl

theorem cell23_6190703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 5].length) (baseStart_6190703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190703 prefixEnd_6190703 := by exact prefixLift 6190703
  have htrace : WordTrace (prefixWord ++ tailWord_6190703) baseStart_6190703 baseEnd_6190703 := by
    simpa [prefixWord, tailWord_6190703, baseEnd_6190703] using wordTrace_append hprefix tailTrace_6190703
  have hstable : (prefixWord ++ tailWord_6190703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190703).length < 2 ^ (prefixWord ++ tailWord_6190703).sum := by decide
  have hdescent : baseEnd_6190703 < baseStart_6190703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190713 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_6190713 : Nat := 118140960795 + 6190713 * 2 ^ 59
def prefixEnd_6190713 : Nat := 4983230072969 + 3 ^ 40 * 6190713 * 2
def baseEnd_6190713 : Nat := 3178811363037542540616935

theorem tailTrace_6190713 : CollatzResearch.WordTrace tailWord_6190713 prefixEnd_6190713 3178811363037542540616935 := by
  unfold tailWord_6190713
  simp only [CollatzResearch.WordTrace]
  refine ⟨225793852821111565450384793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150529235214074376966923195 225793852821111565450384793)
  ·
    refine ⟨169345389615833674087788595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225793852821111565450384793 169345389615833674087788595)
    ·
      refine ⟨254018084423750511131682893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169345389615833674087788595 254018084423750511131682893)
      ·
        refine ⟨95256781658906441674381085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254018084423750511131682893 95256781658906441674381085)
        ·
          refine ⟨35721293122089915627892907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95256781658906441674381085 35721293122089915627892907)
          ·
            refine ⟨53581939683134873441839361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35721293122089915627892907 53581939683134873441839361)
            ·
              refine ⟨40186454762351155081379521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53581939683134873441839361 40186454762351155081379521)
              ·
                refine ⟨30139841071763366311034641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40186454762351155081379521 30139841071763366311034641)
                ·
                  refine ⟨22604880803822524733275981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30139841071763366311034641 22604880803822524733275981)
                  ·
                    refine ⟨8476830301433446774978493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22604880803822524733275981 8476830301433446774978493)
                    ·
                      refine ⟨3178811363037542540616935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476830301433446774978493 3178811363037542540616935)
                      ·
                        rfl

theorem cell23_6190713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_6190713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190713 prefixEnd_6190713 := by exact prefixLift 6190713
  have htrace : WordTrace (prefixWord ++ tailWord_6190713) baseStart_6190713 baseEnd_6190713 := by
    simpa [prefixWord, tailWord_6190713, baseEnd_6190713] using wordTrace_append hprefix tailTrace_6190713
  have hstable : (prefixWord ++ tailWord_6190713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190713).length < 2 ^ (prefixWord ++ tailWord_6190713).sum := by decide
  have hdescent : baseEnd_6190713 < baseStart_6190713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190716 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_6190716 : Nat := 118140960795 + 6190716 * 2 ^ 59
def prefixEnd_6190716 : Nat := 4983230072969 + 3 ^ 40 * 6190716 * 2
def baseEnd_6190716 : Nat := 1059604301159835342959807

theorem tailTrace_6190716 : CollatzResearch.WordTrace tailWord_6190716 prefixEnd_6190716 1059604301159835342959807 := by
  unfold tailWord_6190716
  simp only [CollatzResearch.WordTrace]
  refine ⟨112896981120050348481372001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150529308160067131308496001 112896981120050348481372001)
  ·
    refine ⟨84672735840037761361029001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112896981120050348481372001 84672735840037761361029001)
    ·
      refine ⟨63504551880028321020771751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84672735840037761361029001 63504551880028321020771751)
      ·
        refine ⟨95256827820042481531157627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63504551880028321020771751 95256827820042481531157627)
        ·
          refine ⟨142885241730063722296736441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95256827820042481531157627 142885241730063722296736441)
          ·
            refine ⟨107163931297547791722552331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142885241730063722296736441 107163931297547791722552331)
            ·
              refine ⟨160745896946321687583828497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107163931297547791722552331 160745896946321687583828497)
              ·
                refine ⟨120559422709741265687871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160745896946321687583828497 120559422709741265687871373)
                ·
                  refine ⟨45209783516152974632951765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120559422709741265687871373 45209783516152974632951765)
                  ·
                    refine ⟨1059604301159835342959807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45209783516152974632951765 1059604301159835342959807)
                    ·
                      rfl

theorem cell23_6190716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_6190716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190716 prefixEnd_6190716 := by exact prefixLift 6190716
  have htrace : WordTrace (prefixWord ++ tailWord_6190716) baseStart_6190716 baseEnd_6190716 := by
    simpa [prefixWord, tailWord_6190716, baseEnd_6190716] using wordTrace_append hprefix tailTrace_6190716
  have hstable : (prefixWord ++ tailWord_6190716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190716).length < 2 ^ (prefixWord ++ tailWord_6190716).sum := by decide
  have hdescent : baseEnd_6190716 < baseStart_6190716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190730 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6190730 : Nat := 118140960795 + 6190730 * 2 ^ 59
def prefixEnd_6190730 : Nat := 4983230072969 + 3 ^ 40 * 6190730 * 2
def baseEnd_6190730 : Nat := 3178820092208668974104357

theorem tailTrace_6190730 : CollatzResearch.WordTrace tailWord_6190730 prefixEnd_6190730 3178820092208668974104357 := by
  unfold tailWord_6190730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448618215512494338438411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150529648574699984902502429 56448618215512494338438411)
  ·
    refine ⟨84672927323268741507657617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56448618215512494338438411 84672927323268741507657617)
    ·
      refine ⟨63504695492451556130743213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84672927323268741507657617 63504695492451556130743213)
      ·
        refine ⟨23814260809669333549028705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63504695492451556130743213 23814260809669333549028705)
        ·
          refine ⟨17860695607252000161771529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23814260809669333549028705 17860695607252000161771529)
          ·
            refine ⟨13395521705439000121328647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17860695607252000161771529 13395521705439000121328647)
            ·
              refine ⟨20093282558158500181992971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13395521705439000121328647 20093282558158500181992971)
              ·
                refine ⟨30139923837237750272989457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20093282558158500181992971 30139923837237750272989457)
                ·
                  refine ⟨22604942877928312704742093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30139923837237750272989457 22604942877928312704742093)
                  ·
                    refine ⟨8476853579223117264278285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22604942877928312704742093 8476853579223117264278285)
                    ·
                      refine ⟨3178820092208668974104357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8476853579223117264278285 3178820092208668974104357)
                      ·
                        rfl

theorem cell23_6190730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6190730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190730 prefixEnd_6190730 := by exact prefixLift 6190730
  have htrace : WordTrace (prefixWord ++ tailWord_6190730) baseStart_6190730 baseEnd_6190730 := by
    simpa [prefixWord, tailWord_6190730, baseEnd_6190730] using wordTrace_append hprefix tailTrace_6190730
  have hstable : (prefixWord ++ tailWord_6190730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190730).length < 2 ^ (prefixWord ++ tailWord_6190730).sum := by decide
  have hdescent : baseEnd_6190730 < baseStart_6190730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190750 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6190750 : Nat := 118140960795 + 6190750 * 2 ^ 59
def prefixEnd_6190750 : Nat := 4983230072969 + 3 ^ 40 * 6190750 * 2
def baseEnd_6190750 : Nat := 1059610120607252965284755

theorem tailTrace_6190750 : CollatzResearch.WordTrace tailWord_6190750 prefixEnd_6190750 1059610120607252965284755 := by
  unfold tailWord_6190750
  simp only [CollatzResearch.WordTrace]
  refine ⟨28224400290247190096185213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150530134881318347179654469 28224400290247190096185213)
  ·
    refine ⟨10584150108842696286069455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28224400290247190096185213 10584150108842696286069455)
    ·
      refine ⟨15876225163264044429104183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10584150108842696286069455 15876225163264044429104183)
      ·
        refine ⟨23814337744896066643656275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15876225163264044429104183 23814337744896066643656275)
        ·
          refine ⟨35721506617344099965484413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23814337744896066643656275 35721506617344099965484413)
          ·
            refine ⟨13395564981504037487056655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35721506617344099965484413 13395564981504037487056655)
            ·
              refine ⟨20093347472256056230584983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13395564981504037487056655 20093347472256056230584983)
              ·
                refine ⟨30140021208384084345877475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20093347472256056230584983 30140021208384084345877475)
                ·
                  refine ⟨45210031812576126518816213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30140021208384084345877475 45210031812576126518816213)
                  ·
                    refine ⟨1059610120607252965284755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45210031812576126518816213 1059610120607252965284755)
                    ·
                      rfl

theorem cell23_6190750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6190750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190750 prefixEnd_6190750 := by exact prefixLift 6190750
  have htrace : WordTrace (prefixWord ++ tailWord_6190750) baseStart_6190750 baseEnd_6190750 := by
    simpa [prefixWord, tailWord_6190750, baseEnd_6190750] using wordTrace_append hprefix tailTrace_6190750
  have hstable : (prefixWord ++ tailWord_6190750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190750).length < 2 ^ (prefixWord ++ tailWord_6190750).sum := by decide
  have hdescent : baseEnd_6190750 < baseStart_6190750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190754 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_6190754 : Nat := 118140960795 + 6190754 * 2 ^ 59
def prefixEnd_6190754 : Nat := 4983230072969 + 3 ^ 40 * 6190754 * 2
def baseEnd_6190754 : Nat := 353203601749375208911583

theorem tailTrace_6190754 : CollatzResearch.WordTrace tailWord_6190754 prefixEnd_6190754 353203601749375208911583 := by
  unfold tailWord_6190754
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448837053490757363156829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150530232142642019635084877 56448837053490757363156829)
  ·
    refine ⟨21168313895059034011183811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56448837053490757363156829 21168313895059034011183811)
    ·
      refine ⟨31752470842588551016775717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21168313895059034011183811 31752470842588551016775717)
      ·
        refine ⟨5953588282985353315645447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31752470842588551016775717 5953588282985353315645447)
        ·
          refine ⟨8930382424478029973468171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953588282985353315645447 8930382424478029973468171)
          ·
            refine ⟨13395573636717044960202257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8930382424478029973468171 13395573636717044960202257)
            ·
              refine ⟨10046680227537783720151693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13395573636717044960202257 10046680227537783720151693)
              ·
                refine ⟨3767505085326668895056885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10046680227537783720151693 3767505085326668895056885)
                ·
                  refine ⟨353203601749375208911583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767505085326668895056885 353203601749375208911583)
                  ·
                    rfl

theorem cell23_6190754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_6190754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190754 prefixEnd_6190754 := by exact prefixLift 6190754
  have htrace : WordTrace (prefixWord ++ tailWord_6190754) baseStart_6190754 baseEnd_6190754 := by
    simpa [prefixWord, tailWord_6190754, baseEnd_6190754] using wordTrace_append hprefix tailTrace_6190754
  have hstable : (prefixWord ++ tailWord_6190754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190754).length < 2 ^ (prefixWord ++ tailWord_6190754).sum := by decide
  have hdescent : baseEnd_6190754 < baseStart_6190754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190770 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_6190770 : Nat := 118140960795 + 6190770 * 2 ^ 59
def prefixEnd_6190770 : Nat := 4983230072969 + 3 ^ 40 * 6190770 * 2
def baseEnd_6190770 : Nat := 3178840631434848817604173

theorem tailTrace_6190770 : CollatzResearch.WordTrace tailWord_6190770 prefixEnd_6190770 3178840631434848817604173 := by
  unfold tailWord_6190770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448982945476266046302441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150530621187936709456806509 56448982945476266046302441)
  ·
    refine ⟨42336737209107199534726831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56448982945476266046302441 42336737209107199534726831)
    ·
      refine ⟨63505105813660799302090247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42336737209107199534726831 63505105813660799302090247)
      ·
        refine ⟨95257658720491198953135371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63505105813660799302090247 95257658720491198953135371)
        ·
          refine ⟨142886488080736798429703057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95257658720491198953135371 142886488080736798429703057)
          ·
            refine ⟨107164866060552598822277293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142886488080736798429703057 107164866060552598822277293)
            ·
              refine ⟨40186824772707224558353985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107164866060552598822277293 40186824772707224558353985)
              ·
                refine ⟨30140118579530418418765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40186824772707224558353985 30140118579530418418765489)
                ·
                  refine ⟨22605088934647813814074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30140118579530418418765489 22605088934647813814074117)
                  ·
                    refine ⟨4238454175246465090138897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22605088934647813814074117 4238454175246465090138897)
                    ·
                      refine ⟨3178840631434848817604173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238454175246465090138897 3178840631434848817604173)
                      ·
                        rfl

theorem cell23_6190770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_6190770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190770 prefixEnd_6190770 := by exact prefixLift 6190770
  have htrace : WordTrace (prefixWord ++ tailWord_6190770) baseStart_6190770 baseEnd_6190770 := by
    simpa [prefixWord, tailWord_6190770, baseEnd_6190770] using wordTrace_append hprefix tailTrace_6190770
  have hstable : (prefixWord ++ tailWord_6190770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190770).length < 2 ^ (prefixWord ++ tailWord_6190770).sum := by decide
  have hdescent : baseEnd_6190770 < baseStart_6190770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190780 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_6190780 : Nat := 118140960795 + 6190780 * 2 ^ 59
def prefixEnd_6190780 : Nat := 4983230072969 + 3 ^ 40 * 6190780 * 2
def baseEnd_6190780 : Nat := 1059615255413797926159709

theorem tailTrace_6190780 : CollatzResearch.WordTrace tailWord_6190780 prefixEnd_6190780 1059615255413797926159709 := by
  unfold tailWord_6190780
  simp only [CollatzResearch.WordTrace]
  refine ⟨112898148255934417946536897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150530864341245890595382529 112898148255934417946536897)
  ·
    refine ⟨84673611191950813459902673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112898148255934417946536897 84673611191950813459902673)
    ·
      refine ⟨63505208393963110094927005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84673611191950813459902673 63505208393963110094927005)
      ·
        refine ⟨23814453147736166285597627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63505208393963110094927005 23814453147736166285597627)
        ·
          refine ⟨35721679721604249428396441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23814453147736166285597627 35721679721604249428396441)
          ·
            refine ⟨26791259791203187071297331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35721679721604249428396441 26791259791203187071297331)
            ·
              refine ⟨40186889686804780606945997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26791259791203187071297331 40186889686804780606945997)
              ·
                refine ⟨15070083632551792727604749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40186889686804780606945997 15070083632551792727604749)
                ·
                  refine ⟨5651281362206922272851781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15070083632551792727604749 5651281362206922272851781)
                  ·
                    refine ⟨1059615255413797926159709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651281362206922272851781 1059615255413797926159709)
                    ·
                      rfl

theorem cell23_6190780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_6190780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190780 prefixEnd_6190780 := by exact prefixLift 6190780
  have htrace : WordTrace (prefixWord ++ tailWord_6190780) baseStart_6190780 baseEnd_6190780 := by
    simpa [prefixWord, tailWord_6190780, baseEnd_6190780] using wordTrace_append hprefix tailTrace_6190780
  have hstable : (prefixWord ++ tailWord_6190780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190780).length < 2 ^ (prefixWord ++ tailWord_6190780).sum := by decide
  have hdescent : baseEnd_6190780 < baseStart_6190780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190860 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_6190860 : Nat := 118140960795 + 6190860 * 2 ^ 59
def prefixEnd_6190860 : Nat := 4983230072969 + 3 ^ 40 * 6190860 * 2
def baseEnd_6190860 : Nat := 3178886844693753465478759

theorem tailTrace_6190860 : CollatzResearch.WordTrace tailWord_6190860 prefixEnd_6190860 3178886844693753465478759 := by
  unfold tailWord_6190860
  simp only [CollatzResearch.WordTrace]
  refine ⟨112899607175789504777993017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150532809567719339703990689 112899607175789504777993017)
  ·
    refine ⟨84674705381842128583494763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112899607175789504777993017 84674705381842128583494763)
    ·
      refine ⟨127012058072763192875242145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84674705381842128583494763 127012058072763192875242145)
      ·
        refine ⟨95259043554572394656431609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127012058072763192875242145 95259043554572394656431609)
        ·
          refine ⟨71444282665929295992323707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95259043554572394656431609 71444282665929295992323707)
          ·
            refine ⟨107166423998893943988485561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71444282665929295992323707 107166423998893943988485561)
            ·
              refine ⟨80374817999170457991364171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107166423998893943988485561 80374817999170457991364171)
              ·
                refine ⟨120562226998755686987046257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80374817999170457991364171 120562226998755686987046257)
                ·
                  refine ⟨90421670249066765240284693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120562226998755686987046257 90421670249066765240284693)
                  ·
                    refine ⟨4238515792925004620638345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90421670249066765240284693 4238515792925004620638345)
                    ·
                      refine ⟨3178886844693753465478759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238515792925004620638345 3178886844693753465478759)
                      ·
                        rfl

theorem cell23_6190860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_6190860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190860 prefixEnd_6190860 := by exact prefixLift 6190860
  have htrace : WordTrace (prefixWord ++ tailWord_6190860) baseStart_6190860 baseEnd_6190860 := by
    simpa [prefixWord, tailWord_6190860, baseEnd_6190860] using wordTrace_append hprefix tailTrace_6190860
  have hstable : (prefixWord ++ tailWord_6190860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190860).length < 2 ^ (prefixWord ++ tailWord_6190860).sum := by decide
  have hdescent : baseEnd_6190860 < baseStart_6190860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190888 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6190888 : Nat := 118140960795 + 6190888 * 2 ^ 59
def prefixEnd_6190888 : Nat := 4983230072969 + 3 ^ 40 * 6190888 * 2
def baseEnd_6190888 : Nat := 3178901222152079355928631

theorem tailTrace_6190888 : CollatzResearch.WordTrace tailWord_6190888 prefixEnd_6190888 3178901222152079355928631 := by
  unfold tailWord_6190888
  simp only [CollatzResearch.WordTrace]
  refine ⟨112900117797738785169002659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150533490396985046892003545 112900117797738785169002659)
  ·
    refine ⟨169350176696608177753503989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112900117797738785169002659 169350176696608177753503989)
    ·
      refine ⟨15876579065307016664390999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169350176696608177753503989 15876579065307016664390999)
      ·
        refine ⟨23814868597960524996586499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15876579065307016664390999 23814868597960524996586499)
        ·
          refine ⟨35722302896940787494879749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23814868597960524996586499 35722302896940787494879749)
          ·
            refine ⟨6697931793176397655289953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35722302896940787494879749 6697931793176397655289953)
            ·
              refine ⟨5023448844882298241467465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697931793176397655289953 5023448844882298241467465)
              ·
                refine ⟨3767586633661723681100599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5023448844882298241467465 3767586633661723681100599)
                ·
                  refine ⟨5651379950492585521650899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767586633661723681100599 5651379950492585521650899)
                  ·
                    refine ⟨8477069925738878282476349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5651379950492585521650899 8477069925738878282476349)
                    ·
                      refine ⟨3178901222152079355928631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477069925738878282476349 3178901222152079355928631)
                      ·
                        rfl

theorem cell23_6190888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6190888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190888 prefixEnd_6190888 := by exact prefixLift 6190888
  have htrace : WordTrace (prefixWord ++ tailWord_6190888) baseStart_6190888 baseEnd_6190888 := by
    simpa [prefixWord, tailWord_6190888, baseEnd_6190888] using wordTrace_append hprefix tailTrace_6190888
  have hstable : (prefixWord ++ tailWord_6190888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190888).length < 2 ^ (prefixWord ++ tailWord_6190888).sum := by decide
  have hdescent : baseEnd_6190888 < baseStart_6190888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190944 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_6190944 : Nat := 118140960795 + 6190944 * 2 ^ 59
def prefixEnd_6190944 : Nat := 4983230072969 + 3 ^ 40 * 6190944 * 2
def baseEnd_6190944 : Nat := 3178929977068731136828373

theorem tailTrace_6190944 : CollatzResearch.WordTrace tailWord_6190944 prefixEnd_6190944 3178929977068731136828373 := by
  unfold tailWord_6190944
  simp only [CollatzResearch.WordTrace]
  refine ⟨112901139041637345951021943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150534852055516461268029257 112901139041637345951021943)
  ·
    refine ⟨169351708562456018926532915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112901139041637345951021943 169351708562456018926532915)
    ·
      refine ⟨254027562843684028389799373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169351708562456018926532915 254027562843684028389799373)
      ·
        refine ⟨95260336066381510646174765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254027562843684028389799373 95260336066381510646174765)
        ·
          refine ⟨35722626024893066492315537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95260336066381510646174765 35722626024893066492315537)
          ·
            refine ⟨26791969518669799869236653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35722626024893066492315537 26791969518669799869236653)
            ·
              refine ⟨10046988569501174950963745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26791969518669799869236653 10046988569501174950963745)
              ·
                refine ⟨7535241427125881213222809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10046988569501174950963745 7535241427125881213222809)
                ·
                  refine ⟨5651431070344410909917107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535241427125881213222809 5651431070344410909917107)
                  ·
                    refine ⟨8477146605516616364875661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5651431070344410909917107 8477146605516616364875661)
                    ·
                      refine ⟨3178929977068731136828373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477146605516616364875661 3178929977068731136828373)
                      ·
                        rfl

theorem cell23_6190944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_6190944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190944 prefixEnd_6190944 := by exact prefixLift 6190944
  have htrace : WordTrace (prefixWord ++ tailWord_6190944) baseStart_6190944 baseEnd_6190944 := by
    simpa [prefixWord, tailWord_6190944, baseEnd_6190944] using wordTrace_append hprefix tailTrace_6190944
  have hstable : (prefixWord ++ tailWord_6190944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190944).length < 2 ^ (prefixWord ++ tailWord_6190944).sum := by decide
  have hdescent : baseEnd_6190944 < baseStart_6190944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190970 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_6190970 : Nat := 118140960795 + 6190970 * 2 ^ 59
def prefixEnd_6190970 : Nat := 4983230072969 + 3 ^ 40 * 6190970 * 2
def baseEnd_6190970 : Nat := 3178943327565748035103253

theorem tailTrace_6190970 : CollatzResearch.WordTrace tailWord_6190970 prefixEnd_6190970 3178943327565748035103253 := by
  unfold tailWord_6190970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56450806595295124585622591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150535484254120332228326909 56450806595295124585622591)
  ·
    refine ⟨84676209892942686878433887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56450806595295124585622591 84676209892942686878433887)
    ·
      refine ⟨127014314839414030317650831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84676209892942686878433887 127014314839414030317650831)
      ·
        refine ⟨190521472259121045476476247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127014314839414030317650831 190521472259121045476476247)
        ·
          refine ⟨285782208388681568214714371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190521472259121045476476247 285782208388681568214714371)
          ·
            refine ⟨428673312583022352322071557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285782208388681568214714371 428673312583022352322071557)
            ·
              refine ⟨80376246109316691060388417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 428673312583022352322071557 80376246109316691060388417)
              ·
                refine ⟨60282184581987518295291313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80376246109316691060388417 60282184581987518295291313)
                ·
                  refine ⟨45211638436490638721468485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60282184581987518295291313 45211638436490638721468485)
                  ·
                    refine ⟨8477182206841994760275341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45211638436490638721468485 8477182206841994760275341)
                    ·
                      refine ⟨3178943327565748035103253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477182206841994760275341 3178943327565748035103253)
                      ·
                        rfl

theorem cell23_6190970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_6190970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190970 prefixEnd_6190970 := by exact prefixLift 6190970
  have htrace : WordTrace (prefixWord ++ tailWord_6190970) baseStart_6190970 baseEnd_6190970 := by
    simpa [prefixWord, tailWord_6190970, baseEnd_6190970] using wordTrace_append hprefix tailTrace_6190970
  have hstable : (prefixWord ++ tailWord_6190970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190970).length < 2 ^ (prefixWord ++ tailWord_6190970).sum := by decide
  have hdescent : baseEnd_6190970 < baseStart_6190970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190980 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6190980 : Nat := 118140960795 + 6190980 * 2 ^ 59
def prefixEnd_6190980 : Nat := 4983230072969 + 3 ^ 40 * 6190980 * 2
def baseEnd_6190980 : Nat := 3178948462372292995978207

theorem tailTrace_6190980 : CollatzResearch.WordTrace tailWord_6190980 prefixEnd_6190980 3178948462372292995978207 := by
  unfold tailWord_6190980
  simp only [CollatzResearch.WordTrace]
  refine ⟨112901795555572135025177197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150535727407429513366902929 112901795555572135025177197)
  ·
    refine ⟨42338173333339550634441449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112901795555572135025177197 42338173333339550634441449)
    ·
      refine ⟨31753630000004662975831087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42338173333339550634441449 31753630000004662975831087)
      ·
        refine ⟨47630445000006994463746631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31753630000004662975831087 47630445000006994463746631)
        ·
          refine ⟨71445667500010491695619947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47630445000006994463746631 71445667500010491695619947)
          ·
            refine ⟨107168501250015737543429921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71445667500010491695619947 107168501250015737543429921)
            ·
              refine ⟨80376375937511803157572441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107168501250015737543429921 80376375937511803157572441)
              ·
                refine ⟨60282281953133852368179331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80376375937511803157572441 60282281953133852368179331)
                ·
                  refine ⟨90423422929700778552268997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60282281953133852368179331 90423422929700778552268997)
                  ·
                    refine ⟨16954391799318895978550437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90423422929700778552268997 16954391799318895978550437)
                    ·
                      refine ⟨3178948462372292995978207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16954391799318895978550437 3178948462372292995978207)
                      ·
                        rfl

theorem cell23_6190980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6190980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190980 prefixEnd_6190980 := by exact prefixLift 6190980
  have htrace : WordTrace (prefixWord ++ tailWord_6190980) baseStart_6190980 baseEnd_6190980 := by
    simpa [prefixWord, tailWord_6190980, baseEnd_6190980] using wordTrace_append hprefix tailTrace_6190980
  have hstable : (prefixWord ++ tailWord_6190980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190980).length < 2 ^ (prefixWord ++ tailWord_6190980).sum := by decide
  have hdescent : baseEnd_6190980 < baseStart_6190980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191022 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6191022 : Nat := 118140960795 + 6191022 * 2 ^ 59
def prefixEnd_6191022 : Nat := 4983230072969 + 3 ^ 40 * 6191022 * 2
def baseEnd_6191022 : Nat := 3178970028559781831653015

theorem tailTrace_6191022 : CollatzResearch.WordTrace tailWord_6191022 prefixEnd_6191022 3178970028559781831653015 := by
  unfold tailWord_6191022
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225640372124013902922915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150536748651328074148922213 28225640372124013902922915)
  ·
    refine ⟨42338460558186020854384373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28225640372124013902922915 42338460558186020854384373)
    ·
      refine ⟨3969230677329939455098535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42338460558186020854384373 3969230677329939455098535)
      ·
        refine ⟨5953846015994909182647803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3969230677329939455098535 5953846015994909182647803)
        ·
          refine ⟨8930769023992363773971705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953846015994909182647803 8930769023992363773971705)
          ·
            refine ⟨6698076767994272830478779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8930769023992363773971705 6698076767994272830478779)
            ·
              refine ⟨10047115151991409245718169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698076767994272830478779 10047115151991409245718169)
              ·
                refine ⟨7535336363993556934288627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047115151991409245718169 7535336363993556934288627)
                ·
                  refine ⟨11303004545990335401432941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535336363993556934288627 11303004545990335401432941)
                  ·
                    refine ⟨4238626704746375775537353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303004545990335401432941 4238626704746375775537353)
                    ·
                      refine ⟨3178970028559781831653015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238626704746375775537353 3178970028559781831653015)
                      ·
                        rfl

theorem cell23_6191022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6191022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191022 prefixEnd_6191022 := by exact prefixLift 6191022
  have htrace : WordTrace (prefixWord ++ tailWord_6191022) baseStart_6191022 baseEnd_6191022 := by
    simpa [prefixWord, tailWord_6191022, baseEnd_6191022] using wordTrace_append hprefix tailTrace_6191022
  have hstable : (prefixWord ++ tailWord_6191022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191022).length < 2 ^ (prefixWord ++ tailWord_6191022).sum := by decide
  have hdescent : baseEnd_6191022 < baseStart_6191022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191037 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_6191037 : Nat := 118140960795 + 6191037 * 2 ^ 59
def prefixEnd_6191037 : Nat := 4983230072969 + 3 ^ 40 * 6191037 * 2
def baseEnd_6191037 : Nat := 1059659243589866424321815

theorem tailTrace_6191037 : CollatzResearch.WordTrace tailWord_6191037 prefixEnd_6191037 1059659243589866424321815 := by
  unfold tailWord_6191037
  simp only [CollatzResearch.WordTrace]
  refine ⟨225805670071937768785179365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150537113381291845856786243 225805670071937768785179365)
  ·
    refine ⟨42338563138488331647221131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225805670071937768785179365 42338563138488331647221131)
    ·
      refine ⟨63507844707732497470831697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42338563138488331647221131 63507844707732497470831697)
      ·
        refine ⟨47630883530799373103123773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63507844707732497470831697 47630883530799373103123773)
        ·
          refine ⟨17861581324049764913671415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47630883530799373103123773 17861581324049764913671415)
          ·
            refine ⟨26792371986074647370507123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17861581324049764913671415 26792371986074647370507123)
            ·
              refine ⟨40188557979111971055760685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26792371986074647370507123 40188557979111971055760685)
              ·
                refine ⟨15070709242166989145910257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40188557979111971055760685 15070709242166989145910257)
                ·
                  refine ⟨11303031931625241859432693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15070709242166989145910257 11303031931625241859432693)
                  ·
                    refine ⟨1059659243589866424321815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11303031931625241859432693 1059659243589866424321815)
                    ·
                      rfl

theorem cell23_6191037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_6191037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191037 prefixEnd_6191037 := by exact prefixLift 6191037
  have htrace : WordTrace (prefixWord ++ tailWord_6191037) baseStart_6191037 baseEnd_6191037 := by
    simpa [prefixWord, tailWord_6191037, baseEnd_6191037] using wordTrace_append hprefix tailTrace_6191037
  have hstable : (prefixWord ++ tailWord_6191037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191037).length < 2 ^ (prefixWord ++ tailWord_6191037).sum := by decide
  have hdescent : baseEnd_6191037 < baseStart_6191037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191058 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_6191058 : Nat := 118140960795 + 6191058 * 2 ^ 59
def prefixEnd_6191058 : Nat := 4983230072969 + 3 ^ 40 * 6191058 * 2
def baseEnd_6191058 : Nat := 353220945984815965644761

theorem tailTrace_6191058 : CollatzResearch.WordTrace tailWord_6191058 prefixEnd_6191058 353220945984815965644761 := by
  unfold tailWord_6191058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56451609001215422342923457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150537624003241126247795885 56451609001215422342923457)
  ·
    refine ⟨42338706750911566757192593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56451609001215422342923457 42338706750911566757192593)
    ·
      refine ⟨31754030063183675067894445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42338706750911566757192593 31754030063183675067894445)
      ·
        refine ⟨11907761273693878150460417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31754030063183675067894445 11907761273693878150460417)
        ·
          refine ⟨8930820955270408612845313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11907761273693878150460417 8930820955270408612845313)
          ·
            refine ⟨6698115716452806459633985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8930820955270408612845313 6698115716452806459633985)
            ·
              refine ⟨5023586787339604844725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698115716452806459633985 5023586787339604844725489)
              ·
                refine ⟨3767690090504703633544117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5023586787339604844725489 3767690090504703633544117)
                ·
                  refine ⟨353220945984815965644761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767690090504703633544117 353220945984815965644761)
                  ·
                    rfl

theorem cell23_6191058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_6191058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191058 prefixEnd_6191058 := by exact prefixLift 6191058
  have htrace : WordTrace (prefixWord ++ tailWord_6191058) baseStart_6191058 baseEnd_6191058 := by
    simpa [prefixWord, tailWord_6191058, baseEnd_6191058] using wordTrace_append hprefix tailTrace_6191058
  have hstable : (prefixWord ++ tailWord_6191058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191058).length < 2 ^ (prefixWord ++ tailWord_6191058).sum := by decide
  have hdescent : baseEnd_6191058 < baseStart_6191058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191068 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6191068 : Nat := 118140960795 + 6191068 * 2 ^ 59
def prefixEnd_6191068 : Nat := 4983230072969 + 3 ^ 40 * 6191068 * 2
def baseEnd_6191068 : Nat := 3178993648669888651677803

theorem tailTrace_6191068 : CollatzResearch.WordTrace tailWord_6191068 prefixEnd_6191068 3178993648669888651677803 := by
  unfold tailWord_6191068
  simp only [CollatzResearch.WordTrace]
  refine ⟨112903400367412730539778929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150537867156550307386371905 112903400367412730539778929)
  ·
    refine ⟨84677550275559547904834197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112903400367412730539778929 84677550275559547904834197)
    ·
      refine ⟨3969260169166853808039103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84677550275559547904834197 3969260169166853808039103)
      ·
        refine ⟨5953890253750280712058655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3969260169166853808039103 5953890253750280712058655)
        ·
          refine ⟨8930835380625421068087983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953890253750280712058655 8930835380625421068087983)
          ·
            refine ⟨13396253070938131602131975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8930835380625421068087983 13396253070938131602131975)
            ·
              refine ⟨20094379606407197403197963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396253070938131602131975 20094379606407197403197963)
              ·
                refine ⟨30141569409610796104796945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20094379606407197403197963 30141569409610796104796945)
                ·
                  refine ⟨22606177057208097078597709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30141569409610796104796945 22606177057208097078597709)
                  ·
                    refine ⟨8477316396453036404474141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22606177057208097078597709 8477316396453036404474141)
                    ·
                      refine ⟨3178993648669888651677803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477316396453036404474141 3178993648669888651677803)
                      ·
                        rfl

theorem cell23_6191068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6191068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191068 prefixEnd_6191068 := by exact prefixLift 6191068
  have htrace : WordTrace (prefixWord ++ tailWord_6191068) baseStart_6191068 baseEnd_6191068 := by
    simpa [prefixWord, tailWord_6191068, baseEnd_6191068] using wordTrace_append hprefix tailTrace_6191068
  have hstable : (prefixWord ++ tailWord_6191068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191068).length < 2 ^ (prefixWord ++ tailWord_6191068).sum := by decide
  have hdescent : baseEnd_6191068 < baseStart_6191068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191080 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 10]
def baseStart_6191080 : Nat := 118140960795 + 6191080 * 2 ^ 59
def prefixEnd_6191080 : Nat := 4983230072969 + 3 ^ 40 * 6191080 * 2
def baseEnd_6191080 : Nat := 353222201159749178303083

theorem tailTrace_6191080 : CollatzResearch.WordTrace tailWord_6191080 prefixEnd_6191080 353222201159749178303083 := by
  unfold tailWord_6191080
  simp only [CollatzResearch.WordTrace]
  refine ⟨112903619205390993564497347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150538158940521324752663129 112903619205390993564497347)
  ·
    refine ⟨169355428808086490346746021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112903619205390993564497347 169355428808086490346746021)
    ·
      refine ⟨31754142901516216940014879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169355428808086490346746021 31754142901516216940014879)
      ·
        refine ⟨47631214352274325410022319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31754142901516216940014879 47631214352274325410022319)
        ·
          refine ⟨71446821528411488115033479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47631214352274325410022319 71446821528411488115033479)
          ·
            refine ⟨107170232292617232172550219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71446821528411488115033479 107170232292617232172550219)
            ·
              refine ⟨160755348438925848258825329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107170232292617232172550219 160755348438925848258825329)
              ·
                refine ⟨120566511329194386194118997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160755348438925848258825329 120566511329194386194118997)
                ·
                  refine ⟨353222201159749178303083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120566511329194386194118997 353222201159749178303083)
                  ·
                    rfl

theorem cell23_6191080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_6191080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191080 prefixEnd_6191080 := by exact prefixLift 6191080
  have htrace : WordTrace (prefixWord ++ tailWord_6191080) baseStart_6191080 baseEnd_6191080 := by
    simpa [prefixWord, tailWord_6191080, baseEnd_6191080] using wordTrace_append hprefix tailTrace_6191080
  have hstable : (prefixWord ++ tailWord_6191080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191080).length < 2 ^ (prefixWord ++ tailWord_6191080).sum := by decide
  have hdescent : baseEnd_6191080 < baseStart_6191080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191120 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_6191120 : Nat := 118140960795 + 6191120 * 2 ^ 59
def prefixEnd_6191120 : Nat := 4983230072969 + 3 ^ 40 * 6191120 * 2
def baseEnd_6191120 : Nat := 3179020349663922448227563

theorem tailTrace_6191120 : CollatzResearch.WordTrace tailWord_6191120 prefixEnd_6191120 3179020349663922448227563 := by
  unfold tailWord_6191120
  simp only [CollatzResearch.WordTrace]
  refine ⟨112904348665318536980225407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150539131553758049306967209 112904348665318536980225407)
  ·
    refine ⟨169356522997977805470338111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112904348665318536980225407 169356522997977805470338111)
    ·
      refine ⟨254034784496966708205507167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169356522997977805470338111 254034784496966708205507167)
      ·
        refine ⟨381052176745450062308260751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254034784496966708205507167 381052176745450062308260751)
        ·
          refine ⟨571578265118175093462391127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381052176745450062308260751 571578265118175093462391127)
          ·
            refine ⟨857367397677262640193586691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571578265118175093462391127 857367397677262640193586691)
            ·
              refine ⟨1286051096515893960290380037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857367397677262640193586691 1286051096515893960290380037)
              ·
                refine ⟨241134580596730117554446257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1286051096515893960290380037 241134580596730117554446257)
                ·
                  refine ⟨180850935447547588165834693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241134580596730117554446257 180850935447547588165834693)
                  ·
                    refine ⟨33909550396415172781094005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180850935447547588165834693 33909550396415172781094005)
                    ·
                      refine ⟨3179020349663922448227563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33909550396415172781094005 3179020349663922448227563)
                      ·
                        rfl

theorem cell23_6191120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_6191120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191120 prefixEnd_6191120 := by exact prefixLift 6191120
  have htrace : WordTrace (prefixWord ++ tailWord_6191120) baseStart_6191120 baseEnd_6191120 := by
    simpa [prefixWord, tailWord_6191120, baseEnd_6191120] using wordTrace_append hprefix tailTrace_6191120
  have hstable : (prefixWord ++ tailWord_6191120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191120).length < 2 ^ (prefixWord ++ tailWord_6191120).sum := by decide
  have hdescent : baseEnd_6191120 < baseStart_6191120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191157 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6191157 : Nat := 118140960795 + 6191157 * 2 ^ 59
def prefixEnd_6191157 : Nat := 4983230072969 + 3 ^ 40 * 6191157 * 2
def baseEnd_6191157 : Nat := 1059679782816046267821631

theorem tailTrace_6191157 : CollatzResearch.WordTrace tailWord_6191157 prefixEnd_6191157 1059679782816046267821631 := by
  unfold tailWord_6191157
  simp only [CollatzResearch.WordTrace]
  refine ⟨225810046831503029279547725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150540031221002019519698483 225810046831503029279547725)
  ·
    refine ⟨84678767561813635979830397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225810046831503029279547725 84678767561813635979830397)
    ·
      refine ⟨31754537835680113492436399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84678767561813635979830397 31754537835680113492436399)
      ·
        refine ⟨47631806753520170238654599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31754537835680113492436399 47631806753520170238654599)
        ·
          refine ⟨71447710130280255357981899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47631806753520170238654599 71447710130280255357981899)
          ·
            refine ⟨107171565195420383036972849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71447710130280255357981899 107171565195420383036972849)
            ·
              refine ⟨80378673896565287277729637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107171565195420383036972849 80378673896565287277729637)
              ·
                refine ⟨15071001355605991364574307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80378673896565287277729637 15071001355605991364574307)
                ·
                  refine ⟨22606502033408987046861461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15071001355605991364574307 22606502033408987046861461)
                  ·
                    refine ⟨1059679782816046267821631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22606502033408987046861461 1059679782816046267821631)
                    ·
                      rfl

theorem cell23_6191157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6191157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191157 prefixEnd_6191157 := by exact prefixLift 6191157
  have htrace : WordTrace (prefixWord ++ tailWord_6191157) baseStart_6191157 baseEnd_6191157 := by
    simpa [prefixWord, tailWord_6191157, baseEnd_6191157] using wordTrace_append hprefix tailTrace_6191157
  have hstable : (prefixWord ++ tailWord_6191157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191157).length < 2 ^ (prefixWord ++ tailWord_6191157).sum := by decide
  have hdescent : baseEnd_6191157 < baseStart_6191157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191164 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_6191164 : Nat := 118140960795 + 6191164 * 2 ^ 59
def prefixEnd_6191164 : Nat := 4983230072969 + 3 ^ 40 * 6191164 * 2
def baseEnd_6191164 : Nat := 3179042942812720276077361

theorem tailTrace_6191164 : CollatzResearch.WordTrace tailWord_6191164 prefixEnd_6191164 3179042942812720276077361 := by
  unfold tailWord_6191164
  simp only [CollatzResearch.WordTrace]
  refine ⟨112905151071238834737526273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150540201428318446316701697 112905151071238834737526273)
  ·
    refine ⟨84678863303429126053144705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112905151071238834737526273 84678863303429126053144705)
    ·
      refine ⟨63509147477571844539858529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84678863303429126053144705 63509147477571844539858529)
      ·
        refine ⟨47631860608178883404893897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63509147477571844539858529 47631860608178883404893897)
        ·
          refine ⟨35723895456134162553670423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47631860608178883404893897 35723895456134162553670423)
          ·
            refine ⟨53585843184201243830505635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35723895456134162553670423 53585843184201243830505635)
            ·
              refine ⟨80378764776301865745758453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53585843184201243830505635 80378764776301865745758453)
              ·
                refine ⟨7535509197778299913664855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80378764776301865745758453 7535509197778299913664855)
                ·
                  refine ⟨11303263796667449870497283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535509197778299913664855 11303263796667449870497283)
                  ·
                    refine ⟨16954895695001174805745925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11303263796667449870497283 16954895695001174805745925)
                    ·
                      refine ⟨3179042942812720276077361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16954895695001174805745925 3179042942812720276077361)
                      ·
                        rfl

theorem cell23_6191164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_6191164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191164 prefixEnd_6191164 := by exact prefixLift 6191164
  have htrace : WordTrace (prefixWord ++ tailWord_6191164) baseStart_6191164 baseEnd_6191164 := by
    simpa [prefixWord, tailWord_6191164, baseEnd_6191164] using wordTrace_append hprefix tailTrace_6191164
  have hstable : (prefixWord ++ tailWord_6191164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191164).length < 2 ^ (prefixWord ++ tailWord_6191164).sum := by decide
  have hdescent : baseEnd_6191164 < baseStart_6191164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191167 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_6191167 : Nat := 118140960795 + 6191167 * 2 ^ 59
def prefixEnd_6191167 : Nat := 4983230072969 + 3 ^ 40 * 6191167 * 2
def baseEnd_6191167 : Nat := 3179044483254683764339847

theorem tailTrace_6191167 : CollatzResearch.WordTrace tailWord_6191167 prefixEnd_6191167 3179044483254683764339847 := by
  unfold tailWord_6191167
  simp only [CollatzResearch.WordTrace]
  refine ⟨225810411561466800987411755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150540274374311200658274503 225810411561466800987411755)
  ·
    refine ⟨338715617342200201481117633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225810411561466800987411755 338715617342200201481117633)
    ·
      refine ⟨254036713006650151110838225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338715617342200201481117633 254036713006650151110838225)
      ·
        refine ⟨190527534754987613333128669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254036713006650151110838225 190527534754987613333128669)
        ·
          refine ⟨71447825533120354999923251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190527534754987613333128669 71447825533120354999923251)
          ·
            refine ⟨107171738299680532499884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71447825533120354999923251 107171738299680532499884877)
            ·
              refine ⟨40189401862380199687456829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107171738299680532499884877 40189401862380199687456829)
              ·
                refine ⟨15071025698392574882796311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40189401862380199687456829 15071025698392574882796311)
                ·
                  refine ⟨22606538547588862324194467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15071025698392574882796311 22606538547588862324194467)
                  ·
                    refine ⟨33909807821383293486291701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22606538547588862324194467 33909807821383293486291701)
                    ·
                      refine ⟨3179044483254683764339847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33909807821383293486291701 3179044483254683764339847)
                      ·
                        rfl

theorem cell23_6191167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_6191167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191167 prefixEnd_6191167 := by exact prefixLift 6191167
  have htrace : WordTrace (prefixWord ++ tailWord_6191167) baseStart_6191167 baseEnd_6191167 := by
    simpa [prefixWord, tailWord_6191167, baseEnd_6191167] using wordTrace_append hprefix tailTrace_6191167
  have hstable : (prefixWord ++ tailWord_6191167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191167).length < 2 ^ (prefixWord ++ tailWord_6191167).sum := by decide
  have hdescent : baseEnd_6191167 < baseStart_6191167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191191 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 2, 4]
def baseStart_6191191 : Nat := 118140960795 + 6191191 * 2 ^ 59
def prefixEnd_6191191 : Nat := 4983230072969 + 3 ^ 40 * 6191191 * 2
def baseEnd_6191191 : Nat := 1059685602263463890146579

theorem tailTrace_6191191 : CollatzResearch.WordTrace tailWord_6191191 prefixEnd_6191191 1059685602263463890146579 := by
  unfold tailWord_6191191
  simp only [CollatzResearch.WordTrace]
  refine ⟨225811286913379853086285427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150540857942253235390856951 225811286913379853086285427)
  ·
    refine ⟨338716930370069779629428141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225811286913379853086285427 338716930370069779629428141)
    ·
      refine ⟨127018848888776167361035553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338716930370069779629428141 127018848888776167361035553)
      ·
        refine ⟨95264136666582125520776665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127018848888776167361035553 95264136666582125520776665)
        ·
          refine ⟨71448102499936594140582499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95264136666582125520776665 71448102499936594140582499)
          ·
            refine ⟨107172153749904891210873749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71448102499936594140582499 107172153749904891210873749)
            ·
              refine ⟨5023694707026791775509707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107172153749904891210873749 5023694707026791775509707)
              ·
                refine ⟨7535542060540187663264561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023694707026791775509707 7535542060540187663264561)
                ·
                  refine ⟨5651656545405140747448421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535542060540187663264561 5651656545405140747448421)
                  ·
                    refine ⟨1059685602263463890146579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651656545405140747448421 1059685602263463890146579)
                    ·
                      rfl

theorem cell23_6191191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_6191191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191191 prefixEnd_6191191 := by exact prefixLift 6191191
  have htrace : WordTrace (prefixWord ++ tailWord_6191191) baseStart_6191191 baseEnd_6191191 := by
    simpa [prefixWord, tailWord_6191191, baseEnd_6191191] using wordTrace_append hprefix tailTrace_6191191
  have hstable : (prefixWord ++ tailWord_6191191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191191).length < 2 ^ (prefixWord ++ tailWord_6191191).sum := by decide
  have hdescent : baseEnd_6191191 < baseStart_6191191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191218 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6191218 : Nat := 118140960795 + 6191218 * 2 ^ 59
def prefixEnd_6191218 : Nat := 4983230072969 + 3 ^ 40 * 6191218 * 2
def baseEnd_6191218 : Nat := 3179070670768063064802113

theorem tailTrace_6191218 : CollatzResearch.WordTrace tailWord_6191218 prefixEnd_6191218 3179070670768063064802113 := by
  unfold tailWord_6191218
  simp only [CollatzResearch.WordTrace]
  refine ⟨56453067921070509174379577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150541514456188024465012205 56453067921070509174379577)
  ·
    refine ⟨42339800940802881880784683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56453067921070509174379577 42339800940802881880784683)
    ·
      refine ⟨63509701411204322821177025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42339800940802881880784683 63509701411204322821177025)
      ·
        refine ⟨47632276058403242115882769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63509701411204322821177025 47632276058403242115882769)
        ·
          refine ⟨35724207043802431586912077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47632276058403242115882769 35724207043802431586912077)
          ·
            refine ⟨13396577641425911845092029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35724207043802431586912077 13396577641425911845092029)
            ·
              refine ⟨5023716615534716941909511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13396577641425911845092029 5023716615534716941909511)
              ·
                refine ⟨7535574923302075412864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023716615534716941909511 7535574923302075412864267)
                ·
                  refine ⟨11303362384953113119296401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535574923302075412864267 11303362384953113119296401)
                  ·
                    refine ⟨8477521788714834839472301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11303362384953113119296401 8477521788714834839472301)
                    ·
                      refine ⟨3179070670768063064802113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477521788714834839472301 3179070670768063064802113)
                      ·
                        rfl

theorem cell23_6191218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6191218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191218 prefixEnd_6191218 := by exact prefixLift 6191218
  have htrace : WordTrace (prefixWord ++ tailWord_6191218) baseStart_6191218 baseEnd_6191218 := by
    simpa [prefixWord, tailWord_6191218, baseEnd_6191218] using wordTrace_append hprefix tailTrace_6191218
  have hstable : (prefixWord ++ tailWord_6191218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191218).length < 2 ^ (prefixWord ++ tailWord_6191218).sum := by decide
  have hdescent : baseEnd_6191218 < baseStart_6191218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_6191257 : Nat := 118140960795 + 6191257 * 2 ^ 59
def prefixEnd_6191257 : Nat := 4983230072969 + 3 ^ 40 * 6191257 * 2
def baseEnd_6191257 : Nat := 3179090696513588412214433

theorem tailTrace_6191257 : CollatzResearch.WordTrace tailWord_6191257 prefixEnd_6191257 3179090696513588412214433 := by
  unfold tailWord_6191257
  simp only [CollatzResearch.WordTrace]
  refine ⟨225813694131140746358188025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150542462754093830905458683 225813694131140746358188025)
  ·
    refine ⟨169360270598355559768641019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225813694131140746358188025 169360270598355559768641019)
    ·
      refine ⟨254040405897533339652961529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169360270598355559768641019 254040405897533339652961529)
      ·
        refine ⟨190530304423150004739721147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254040405897533339652961529 190530304423150004739721147)
        ·
          refine ⟨285795456634725007109581721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190530304423150004739721147 285795456634725007109581721)
          ·
            refine ⟨214346592476043755332186291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285795456634725007109581721 214346592476043755332186291)
            ·
              refine ⟨321519888714065632998279437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214346592476043755332186291 321519888714065632998279437)
              ·
                refine ⟨120569958267774612374354789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321519888714065632998279437 120569958267774612374354789)
                ·
                  refine ⟨22606867175207739820191523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120569958267774612374354789 22606867175207739820191523)
                  ·
                    refine ⟨33910300762811609730287285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22606867175207739820191523 33910300762811609730287285)
                    ·
                      refine ⟨3179090696513588412214433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33910300762811609730287285 3179090696513588412214433)
                      ·
                        rfl

theorem cell23_6191257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_6191257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191257 prefixEnd_6191257 := by exact prefixLift 6191257
  have htrace : WordTrace (prefixWord ++ tailWord_6191257) baseStart_6191257 baseEnd_6191257 := by
    simpa [prefixWord, tailWord_6191257, baseEnd_6191257] using wordTrace_append hprefix tailTrace_6191257
  have hstable : (prefixWord ++ tailWord_6191257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191257).length < 2 ^ (prefixWord ++ tailWord_6191257).sum := by decide
  have hdescent : baseEnd_6191257 < baseStart_6191257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191298 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6191298 : Nat := 118140960795 + 6191298 * 2 ^ 59
def prefixEnd_6191298 : Nat := 4983230072969 + 3 ^ 40 * 6191298 * 2
def baseEnd_6191298 : Nat := 1059703916406807583933915

theorem tailTrace_6191298 : CollatzResearch.WordTrace tailWord_6191298 prefixEnd_6191298 1059703916406807583933915 := by
  unfold tailWord_6191298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56453797380998052590107637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150543459682661473573620365 56453797380998052590107637)
  ·
    refine ⟨5292543504468567430322591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56453797380998052590107637 5292543504468567430322591)
    ·
      refine ⟨7938815256702851145483887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292543504468567430322591 7938815256702851145483887)
      ·
        refine ⟨11908222885054276718225831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938815256702851145483887 11908222885054276718225831)
        ·
          refine ⟨17862334327581415077338747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11908222885054276718225831 17862334327581415077338747)
          ·
            refine ⟨26793501491372122616008121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17862334327581415077338747 26793501491372122616008121)
            ·
              refine ⟨20095126118529091962006091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26793501491372122616008121 20095126118529091962006091)
              ·
                refine ⟨30142689177793637943009137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20095126118529091962006091 30142689177793637943009137)
                ·
                  refine ⟨22607016883345228457256853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30142689177793637943009137 22607016883345228457256853)
                  ·
                    refine ⟨1059703916406807583933915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22607016883345228457256853 1059703916406807583933915)
                    ·
                      rfl

theorem cell23_6191298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6191298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191298 prefixEnd_6191298 := by exact prefixLift 6191298
  have htrace : WordTrace (prefixWord ++ tailWord_6191298) baseStart_6191298 baseEnd_6191298 := by
    simpa [prefixWord, tailWord_6191298, baseEnd_6191298] using wordTrace_append hprefix tailTrace_6191298
  have hstable : (prefixWord ++ tailWord_6191298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191298).length < 2 ^ (prefixWord ++ tailWord_6191298).sum := by decide
  have hdescent : baseEnd_6191298 < baseStart_6191298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191307 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 7]
def baseStart_6191307 : Nat := 118140960795 + 6191307 * 2 ^ 59
def prefixEnd_6191307 : Nat := 4983230072969 + 3 ^ 40 * 6191307 * 2
def baseEnd_6191307 : Nat := 1059705456848771072196401

theorem tailTrace_6191307 : CollatzResearch.WordTrace tailWord_6191307 prefixEnd_6191307 1059705456848771072196401 := by
  unfold tailWord_6191307
  simp only [CollatzResearch.WordTrace]
  refine ⟨225815517780959604897508175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150543678520639736598338783 225815517780959604897508175)
  ·
    refine ⟨338723276671439407346262263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225815517780959604897508175 338723276671439407346262263)
    ·
      refine ⟨508084915007159111019393395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338723276671439407346262263 508084915007159111019393395)
      ·
        refine ⟨762127372510738666529090093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508084915007159111019393395 762127372510738666529090093)
        ·
          refine ⟨285797764691526999948408785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762127372510738666529090093 285797764691526999948408785)
          ·
            refine ⟨214348323518645249961306589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285797764691526999948408785 214348323518645249961306589)
            ·
              refine ⟨80380621319491968735489971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214348323518645249961306589 80380621319491968735489971)
              ·
                refine ⟨120570931979237953103234957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80380621319491968735489971 120570931979237953103234957)
                ·
                  refine ⟨45214099492214232413713109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120570931979237953103234957 45214099492214232413713109)
                  ·
                    refine ⟨1059705456848771072196401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45214099492214232413713109 1059705456848771072196401)
                    ·
                      rfl

theorem cell23_6191307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_6191307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191307 prefixEnd_6191307 := by exact prefixLift 6191307
  have htrace : WordTrace (prefixWord ++ tailWord_6191307) baseStart_6191307 baseEnd_6191307 := by
    simpa [prefixWord, tailWord_6191307, baseEnd_6191307] using wordTrace_append hprefix tailTrace_6191307
  have hstable : (prefixWord ++ tailWord_6191307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191307).length < 2 ^ (prefixWord ++ tailWord_6191307).sum := by decide
  have hdescent : baseEnd_6191307 < baseStart_6191307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191337 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_6191337 : Nat := 118140960795 + 6191337 * 2 ^ 59
def prefixEnd_6191337 : Nat := 4983230072969 + 3 ^ 40 * 6191337 * 2
def baseEnd_6191337 : Nat := 1059710591655316033071355

theorem tailTrace_6191337 : CollatzResearch.WordTrace tailWord_6191337 prefixEnd_6191337 1059710591655316033071355 := by
  unfold tailWord_6191337
  simp only [CollatzResearch.WordTrace]
  refine ⟨225816611970850920021100265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150544407980567280014066843 225816611970850920021100265)
  ·
    refine ⟨169362458978138190015825199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225816611970850920021100265 169362458978138190015825199)
    ·
      refine ⟨254043688467207285023737799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169362458978138190015825199 254043688467207285023737799)
      ·
        refine ⟨381065532700810927535606699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254043688467207285023737799 381065532700810927535606699)
        ·
          refine ⟨571598299051216391303410049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381065532700810927535606699 571598299051216391303410049)
          ·
            refine ⟨428698724288412293477557537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571598299051216391303410049 428698724288412293477557537)
            ·
              refine ⟨321524043216309220108168153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428698724288412293477557537 321524043216309220108168153)
              ·
                refine ⟨241143032412231915081126115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321524043216309220108168153 241143032412231915081126115)
                ·
                  refine ⟨361714548618347872621689173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241143032412231915081126115 361714548618347872621689173)
                  ·
                    refine ⟨1059710591655316033071355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 361714548618347872621689173 1059710591655316033071355)
                    ·
                      rfl

theorem cell23_6191337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_6191337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191337 prefixEnd_6191337 := by exact prefixLift 6191337
  have htrace : WordTrace (prefixWord ++ tailWord_6191337) baseStart_6191337 baseEnd_6191337 := by
    simpa [prefixWord, tailWord_6191337, baseEnd_6191337] using wordTrace_append hprefix tailTrace_6191337
  have hstable : (prefixWord ++ tailWord_6191337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191337).length < 2 ^ (prefixWord ++ tailWord_6191337).sum := by decide
  have hdescent : baseEnd_6191337 < baseStart_6191337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191361 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6191361 : Nat := 118140960795 + 6191361 * 2 ^ 59
def prefixEnd_6191361 : Nat := 4983230072969 + 3 ^ 40 * 6191361 * 2
def baseEnd_6191361 : Nat := 3179144098501656005313955

theorem tailTrace_6191361 : CollatzResearch.WordTrace tailWord_6191361 prefixEnd_6191361 3179144098501656005313955 := by
  unfold tailWord_6191361
  simp only [CollatzResearch.WordTrace]
  refine ⟨225817487322763972119973937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150544991548509314746649291 225817487322763972119973937)
  ·
    refine ⟨169363115492072979089980453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225817487322763972119973937 169363115492072979089980453)
    ·
      refine ⟨31755584154763683579371335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169363115492072979089980453 31755584154763683579371335)
      ·
        refine ⟨47633376232145525369057003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31755584154763683579371335 47633376232145525369057003)
        ·
          refine ⟨71450064348218288053585505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47633376232145525369057003 71450064348218288053585505)
          ·
            refine ⟨53587548261163716040189129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71450064348218288053585505 53587548261163716040189129)
            ·
              refine ⟨40190661195872787030141847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53587548261163716040189129 40190661195872787030141847)
              ·
                refine ⟨60285991793809180545212771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40190661195872787030141847 60285991793809180545212771)
                ·
                  refine ⟨90428987690713770817819157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60285991793809180545212771 90428987690713770817819157)
                  ·
                    refine ⟨4238858798002208007085273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90428987690713770817819157 4238858798002208007085273)
                    ·
                      refine ⟨3179144098501656005313955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238858798002208007085273 3179144098501656005313955)
                      ·
                        rfl

theorem cell23_6191361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6191361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191361 prefixEnd_6191361 := by exact prefixLift 6191361
  have htrace : WordTrace (prefixWord ++ tailWord_6191361) baseStart_6191361 baseEnd_6191361 := by
    simpa [prefixWord, tailWord_6191361, baseEnd_6191361] using wordTrace_append hprefix tailTrace_6191361
  have hstable : (prefixWord ++ tailWord_6191361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191361).length < 2 ^ (prefixWord ++ tailWord_6191361).sum := by decide
  have hdescent : baseEnd_6191361 < baseStart_6191361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191381 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_6191381 : Nat := 118140960795 + 6191381 * 2 ^ 59
def prefixEnd_6191381 : Nat := 4983230072969 + 3 ^ 40 * 6191381 * 2
def baseEnd_6191381 : Nat := 3179154368114745927063863

theorem tailTrace_6191381 : CollatzResearch.WordTrace tailWord_6191381 prefixEnd_6191381 3179154368114745927063863 := by
  unfold tailWord_6191381
  simp only [CollatzResearch.WordTrace]
  refine ⟨225818216782691515535701997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150545477855127677023801331 225818216782691515535701997)
  ·
    refine ⟨84681831293509318325888249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225818216782691515535701997 84681831293509318325888249)
    ·
      refine ⟨63511373470131988744416187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84681831293509318325888249 63511373470131988744416187)
      ·
        refine ⟨95267060205197983116624281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63511373470131988744416187 95267060205197983116624281)
        ·
          refine ⟨71450295153898487337468211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95267060205197983116624281 71450295153898487337468211)
          ·
            refine ⟨107175442730847731006202317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71450295153898487337468211 107175442730847731006202317)
            ·
              refine ⟨40190791024067899127325869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107175442730847731006202317 40190791024067899127325869)
              ·
                refine ⟨15071546634025462172747201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40190791024067899127325869 15071546634025462172747201)
                ·
                  refine ⟨11303659975519096629560401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15071546634025462172747201 11303659975519096629560401)
                  ·
                    refine ⟨8477744981639322472170301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11303659975519096629560401 8477744981639322472170301)
                    ·
                      refine ⟨3179154368114745927063863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477744981639322472170301 3179154368114745927063863)
                      ·
                        rfl

theorem cell23_6191381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_6191381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191381 prefixEnd_6191381 := by exact prefixLift 6191381
  have htrace : WordTrace (prefixWord ++ tailWord_6191381) baseStart_6191381 baseEnd_6191381 := by
    simpa [prefixWord, tailWord_6191381, baseEnd_6191381] using wordTrace_append hprefix tailTrace_6191381
  have hstable : (prefixWord ++ tailWord_6191381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191381).length < 2 ^ (prefixWord ++ tailWord_6191381).sum := by decide
  have hdescent : baseEnd_6191381 < baseStart_6191381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191388 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6191388 : Nat := 118140960795 + 6191388 * 2 ^ 59
def prefixEnd_6191388 : Nat := 4983230072969 + 3 ^ 40 * 6191388 * 2
def baseEnd_6191388 : Nat := 1059719320826442466558777

theorem tailTrace_6191388 : CollatzResearch.WordTrace tailWord_6191388 prefixEnd_6191388 1059719320826442466558777 := by
  unfold tailWord_6191388
  simp only [CollatzResearch.WordTrace]
  refine ⟨112909236046833077865603409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150545648062444103820804545 112909236046833077865603409)
  ·
    refine ⟨84681927035124808399202557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112909236046833077865603409 84681927035124808399202557)
    ·
      refine ⟨31755722638171803149700959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84681927035124808399202557 31755722638171803149700959)
      ·
        refine ⟨47633583957257704724551439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31755722638171803149700959 47633583957257704724551439)
        ·
          refine ⟨71450375935886557086827159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47633583957257704724551439 71450375935886557086827159)
          ·
            refine ⟨107175563903829835630240739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71450375935886557086827159 107175563903829835630240739)
            ·
              refine ⟨160763345855744753445361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107175563903829835630240739 160763345855744753445361109)
              ·
                refine ⟨3767890918494017658875651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160763345855744753445361109 3767890918494017658875651)
                ·
                  refine ⟨5651836377741026488313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767890918494017658875651 5651836377741026488313477)
                  ·
                    refine ⟨1059719320826442466558777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651836377741026488313477 1059719320826442466558777)
                    ·
                      rfl

theorem cell23_6191388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6191388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191388 prefixEnd_6191388 := by exact prefixLift 6191388
  have htrace : WordTrace (prefixWord ++ tailWord_6191388) baseStart_6191388 baseEnd_6191388 := by
    simpa [prefixWord, tailWord_6191388, baseEnd_6191388] using wordTrace_append hprefix tailTrace_6191388
  have hstable : (prefixWord ++ tailWord_6191388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191388).length < 2 ^ (prefixWord ++ tailWord_6191388).sum := by decide
  have hdescent : baseEnd_6191388 < baseStart_6191388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191431 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 1, 5]
def baseStart_6191431 : Nat := 118140960795 + 6191431 * 2 ^ 59
def prefixEnd_6191431 : Nat := 4983230072969 + 3 ^ 40 * 6191431 * 2
def baseEnd_6191431 : Nat := 1059726680715823577146211

theorem tailTrace_6191431 : CollatzResearch.WordTrace tailWord_6191431 prefixEnd_6191431 1059726680715823577146211 := by
  unfold tailWord_6191431
  simp only [CollatzResearch.WordTrace]
  refine ⟨225820040432510374075022147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150546693621673582716681431 225820040432510374075022147)
  ·
    refine ⟨338730060648765561112533221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225820040432510374075022147 338730060648765561112533221)
    ·
      refine ⟨63511886371643542708599979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338730060648765561112533221 63511886371643542708599979)
      ·
        refine ⟨95267829557465314062899969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63511886371643542708599979 95267829557465314062899969)
        ·
          refine ⟨71450872168098985547174977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95267829557465314062899969 71450872168098985547174977)
          ·
            refine ⟨53588154126074239160381233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71450872168098985547174977 53588154126074239160381233)
            ·
              refine ⟨40191115594555679370285925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53588154126074239160381233 40191115594555679370285925)
              ·
                refine ⟨7535834173979189881928611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40191115594555679370285925 7535834173979189881928611)
                ·
                  refine ⟨11303751260968784822892917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535834173979189881928611 11303751260968784822892917)
                  ·
                    refine ⟨1059726680715823577146211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11303751260968784822892917 1059726680715823577146211)
                    ·
                      rfl

theorem cell23_6191431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_6191431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191431 prefixEnd_6191431 := by exact prefixLift 6191431
  have htrace : WordTrace (prefixWord ++ tailWord_6191431) baseStart_6191431 baseEnd_6191431 := by
    simpa [prefixWord, tailWord_6191431, baseEnd_6191431] using wordTrace_append hprefix tailTrace_6191431
  have hstable : (prefixWord ++ tailWord_6191431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191431).length < 2 ^ (prefixWord ++ tailWord_6191431).sum := by decide
  have hdescent : baseEnd_6191431 < baseStart_6191431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191438 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_6191438 : Nat := 118140960795 + 6191438 * 2 ^ 59
def prefixEnd_6191438 : Nat := 4983230072969 + 3 ^ 40 * 6191438 * 2
def baseEnd_6191438 : Nat := 3179183636512052204051101

theorem tailTrace_6191438 : CollatzResearch.WordTrace tailWord_6191438 prefixEnd_6191438 3179183636512052204051101 := by
  unfold tailWord_6191438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28227536967935626783815871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150546863828990009513684645 28227536967935626783815871)
  ·
    refine ⟨42341305451903440175723807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28227536967935626783815871 42341305451903440175723807)
    ·
      refine ⟨63511958177855160263585711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42341305451903440175723807 63511958177855160263585711)
      ·
        refine ⟨95267937266782740395378567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63511958177855160263585711 95267937266782740395378567)
        ·
          refine ⟨142901905900174110593067851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95267937266782740395378567 142901905900174110593067851)
          ·
            refine ⟨214352858850261165889601777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142901905900174110593067851 214352858850261165889601777)
            ·
              refine ⟨160764644137695874417201333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214352858850261165889601777 160764644137695874417201333)
              ·
                refine ⟨15071685387908988226612625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160764644137695874417201333 15071685387908988226612625)
                ·
                  refine ⟨11303764040931741169959469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15071685387908988226612625 11303764040931741169959469)
                  ·
                    refine ⟨4238911515349402938734801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303764040931741169959469 4238911515349402938734801)
                    ·
                      refine ⟨3179183636512052204051101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238911515349402938734801 3179183636512052204051101)
                      ·
                        rfl

theorem cell23_6191438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_6191438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191438 prefixEnd_6191438 := by exact prefixLift 6191438
  have htrace : WordTrace (prefixWord ++ tailWord_6191438) baseStart_6191438 baseEnd_6191438 := by
    simpa [prefixWord, tailWord_6191438, baseEnd_6191438] using wordTrace_append hprefix tailTrace_6191438
  have hstable : (prefixWord ++ tailWord_6191438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191438).length < 2 ^ (prefixWord ++ tailWord_6191438).sum := by decide
  have hdescent : baseEnd_6191438 < baseStart_6191438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191452 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 6]
def baseStart_6191452 : Nat := 118140960795 + 6191452 * 2 ^ 59
def prefixEnd_6191452 : Nat := 4983230072969 + 3 ^ 40 * 6191452 * 2
def baseEnd_6191452 : Nat := 353243425026801683252893

theorem tailTrace_6191452 : CollatzResearch.WordTrace tailWord_6191452 prefixEnd_6191452 353243425026801683252893 := by
  unfold tailWord_6191452
  simp only [CollatzResearch.WordTrace]
  refine ⟨112910403182717147330768305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150547204243622863107691073 112910403182717147330768305)
  ·
    refine ⟨84682802387037860498076229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112910403182717147330768305 84682802387037860498076229)
    ·
      refine ⟨15878025447569598843389293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84682802387037860498076229 15878025447569598843389293)
      ·
        refine ⟨5954259542838599566270985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15878025447569598843389293 5954259542838599566270985)
        ·
          refine ⟨4465694657128949674703239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954259542838599566270985 4465694657128949674703239)
          ·
            refine ⟨6698541985693424512054859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465694657128949674703239 6698541985693424512054859)
            ·
              refine ⟨10047812978540136768082289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698541985693424512054859 10047812978540136768082289)
              ·
                refine ⟨7535859733905102576061717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047812978540136768082289 7535859733905102576061717)
                ·
                  refine ⟨353243425026801683252893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7535859733905102576061717 353243425026801683252893)
                  ·
                    rfl

theorem cell23_6191452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_6191452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191452 prefixEnd_6191452 := by exact prefixLift 6191452
  have htrace : WordTrace (prefixWord ++ tailWord_6191452) baseStart_6191452 baseEnd_6191452 := by
    simpa [prefixWord, tailWord_6191452, baseEnd_6191452] using wordTrace_append hprefix tailTrace_6191452
  have hstable : (prefixWord ++ tailWord_6191452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191452).length < 2 ^ (prefixWord ++ tailWord_6191452).sum := by decide
  have hdescent : baseEnd_6191452 < baseStart_6191452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191471 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_6191471 : Nat := 118140960795 + 6191471 * 2 ^ 59
def prefixEnd_6191471 : Nat := 4983230072969 + 3 ^ 40 * 6191471 * 2
def baseEnd_6191471 : Nat := 3179200581373650574938449

theorem tailTrace_6191471 : CollatzResearch.WordTrace tailWord_6191471 prefixEnd_6191471 3179200581373650574938449 := by
  unfold tailWord_6191471
  simp only [CollatzResearch.WordTrace]
  refine ⟨225821499352365460906478267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150547666234910307270985511 225821499352365460906478267)
  ·
    refine ⟨338732249028548191359717401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225821499352365460906478267 338732249028548191359717401)
    ·
      refine ⟨254049186771411143519788051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338732249028548191359717401 254049186771411143519788051)
      ·
        refine ⟨381073780157116715279682077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254049186771411143519788051 381073780157116715279682077)
        ·
          refine ⟨142902667558918768229880779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381073780157116715279682077 142902667558918768229880779)
          ·
            refine ⟨214354001338378152344821169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142902667558918768229880779 214354001338378152344821169)
            ·
              refine ⟨160765501003783614258615877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214354001338378152344821169 160765501003783614258615877)
              ·
                refine ⟨30143531438209427673490477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160765501003783614258615877 30143531438209427673490477)
                ·
                  refine ⟨11303824289328535377558929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30143531438209427673490477 11303824289328535377558929)
                  ·
                    refine ⟨8477868216996401533169197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11303824289328535377558929 8477868216996401533169197)
                    ·
                      refine ⟨3179200581373650574938449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8477868216996401533169197 3179200581373650574938449)
                      ·
                        rfl

theorem cell23_6191471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_6191471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191471 prefixEnd_6191471 := by exact prefixLift 6191471
  have htrace : WordTrace (prefixWord ++ tailWord_6191471) baseStart_6191471 baseEnd_6191471 := by
    simpa [prefixWord, tailWord_6191471, baseEnd_6191471] using wordTrace_append hprefix tailTrace_6191471
  have hstable : (prefixWord ++ tailWord_6191471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191471).length < 2 ^ (prefixWord ++ tailWord_6191471).sum := by decide
  have hdescent : baseEnd_6191471 < baseStart_6191471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191485 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_6191485 : Nat := 118140960795 + 6191485 * 2 ^ 59
def prefixEnd_6191485 : Nat := 4983230072969 + 3 ^ 40 * 6191485 * 2
def baseEnd_6191485 : Nat := 3179207770102813520163385

theorem tailTrace_6191485 : CollatzResearch.WordTrace tailWord_6191485 prefixEnd_6191485 3179207770102813520163385 := by
  unfold tailWord_6191485
  simp only [CollatzResearch.WordTrace]
  refine ⟨225822009974314741297487909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150548006649543160864991939 225822009974314741297487909)
  ·
    refine ⟨42341626870184013993278983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225822009974314741297487909 42341626870184013993278983)
    ·
      refine ⟨63512440305276020989918475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42341626870184013993278983 63512440305276020989918475)
      ·
        refine ⟨95268660457914031484877713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63512440305276020989918475 95268660457914031484877713)
        ·
          refine ⟨71451495343435523613658285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95268660457914031484877713 71451495343435523613658285)
          ·
            refine ⟨26794310753788321355121857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71451495343435523613658285 26794310753788321355121857)
            ·
              refine ⟨20095733065341241016341393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26794310753788321355121857 20095733065341241016341393)
              ·
                refine ⟨15071799799005930762256045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20095733065341241016341393 15071799799005930762256045)
                ·
                  refine ⟨5651924924627224035846017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15071799799005930762256045 5651924924627224035846017)
                  ·
                    refine ⟨4238943693470418026884513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5651924924627224035846017 4238943693470418026884513)
                    ·
                      refine ⟨3179207770102813520163385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238943693470418026884513 3179207770102813520163385)
                      ·
                        rfl

theorem cell23_6191485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_6191485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191485 prefixEnd_6191485 := by exact prefixLift 6191485
  have htrace : WordTrace (prefixWord ++ tailWord_6191485) baseStart_6191485 baseEnd_6191485 := by
    simpa [prefixWord, tailWord_6191485, baseEnd_6191485] using wordTrace_append hprefix tailTrace_6191485
  have hstable : (prefixWord ++ tailWord_6191485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191485).length < 2 ^ (prefixWord ++ tailWord_6191485).sum := by decide
  have hdescent : baseEnd_6191485 < baseStart_6191485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191491 : List Nat := [1, 1, 1, 3, 6, 1, 1, 9]
def baseStart_6191491 : Nat := 118140960795 + 6191491 * 2 ^ 59
def prefixEnd_6191491 : Nat := 4983230072969 + 3 ^ 40 * 6191491 * 2
def baseEnd_6191491 : Nat := 117748550036545944321791

theorem tailTrace_6191491 : CollatzResearch.WordTrace tailWord_6191491 prefixEnd_6191491 117748550036545944321791 := by
  unfold tailWord_6191491
  simp only [CollatzResearch.WordTrace]
  refine ⟨225822228812293004322206327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150548152541528669548137551 225822228812293004322206327)
  ·
    refine ⟨338733343218439506483309491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225822228812293004322206327 338733343218439506483309491)
    ·
      refine ⟨508100014827659259724964237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338733343218439506483309491 508100014827659259724964237)
      ·
        refine ⟨190537505560372222396861589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508100014827659259724964237 190537505560372222396861589)
        ·
          refine ⟨8931445573142447924852887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190537505560372222396861589 8931445573142447924852887)
          ·
            refine ⟨13397168359713671887279331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931445573142447924852887 13397168359713671887279331)
            ·
              refine ⟨20095752539570507830918997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397168359713671887279331 20095752539570507830918997)
              ·
                refine ⟨117748550036545944321791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20095752539570507830918997 117748550036545944321791)
                ·
                  rfl

theorem cell23_6191491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 9].length) (baseStart_6191491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191491 prefixEnd_6191491 := by exact prefixLift 6191491
  have htrace : WordTrace (prefixWord ++ tailWord_6191491) baseStart_6191491 baseEnd_6191491 := by
    simpa [prefixWord, tailWord_6191491, baseEnd_6191491] using wordTrace_append hprefix tailTrace_6191491
  have hstable : (prefixWord ++ tailWord_6191491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191491).length < 2 ^ (prefixWord ++ tailWord_6191491).sum := by decide
  have hdescent : baseEnd_6191491 < baseStart_6191491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191504 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_6191504 : Nat := 118140960795 + 6191504 * 2 ^ 59
def prefixEnd_6191504 : Nat := 4983230072969 + 3 ^ 40 * 6191504 * 2
def baseEnd_6191504 : Nat := 1059739175411749648608599

theorem tailTrace_6191504 : CollatzResearch.WordTrace tailWord_6191504 prefixEnd_6191504 1059739175411749648608599 := by
  unfold tailWord_6191504
  simp only [CollatzResearch.WordTrace]
  refine ⟨112911351480622953771214783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150548468640830605028286377 112911351480622953771214783)
  ·
    refine ⟨169367027220934430656822175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112911351480622953771214783 169367027220934430656822175)
    ·
      refine ⟨254050540831401645985233263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169367027220934430656822175 254050540831401645985233263)
      ·
        refine ⟨381075811247102468977849895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254050540831401645985233263 381075811247102468977849895)
        ·
          refine ⟨571613716870653703466774843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381075811247102468977849895 571613716870653703466774843)
          ·
            refine ⟨857420575305980555200162265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571613716870653703466774843 857420575305980555200162265)
            ·
              refine ⟨643065431479485416400121699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857420575305980555200162265 643065431479485416400121699)
              ·
                refine ⟨964598147219228124600182549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643065431479485416400121699 964598147219228124600182549)
                ·
                  refine ⟨45215538150901318340633557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964598147219228124600182549 45215538150901318340633557)
                  ·
                    refine ⟨1059739175411749648608599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45215538150901318340633557 1059739175411749648608599)
                    ·
                      rfl

theorem cell23_6191504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_6191504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191504 prefixEnd_6191504 := by exact prefixLift 6191504
  have htrace : WordTrace (prefixWord ++ tailWord_6191504) baseStart_6191504 baseEnd_6191504 := by
    simpa [prefixWord, tailWord_6191504, baseEnd_6191504] using wordTrace_append hprefix tailTrace_6191504
  have hstable : (prefixWord ++ tailWord_6191504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191504).length < 2 ^ (prefixWord ++ tailWord_6191504).sum := by decide
  have hdescent : baseEnd_6191504 < baseStart_6191504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191508 : List Nat := [2, 4, 2, 1, 3, 2, 9]
def baseStart_6191508 : Nat := 118140960795 + 6191508 * 2 ^ 59
def prefixEnd_6191508 : Nat := 4983230072969 + 3 ^ 40 * 6191508 * 2
def baseEnd_6191508 : Nat := 39249624446393418891059

theorem tailTrace_6191508 : CollatzResearch.WordTrace tailWord_6191508 prefixEnd_6191508 39249624446393418891059 := by
  unfold tailWord_6191508
  simp only [CollatzResearch.WordTrace]
  refine ⟨112911424426615708112787589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150548565902154277483716785 112911424426615708112787589)
  ·
    refine ⟨21170892079990445271147673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112911424426615708112787589 21170892079990445271147673)
    ·
      refine ⟨15878169059992833953360755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21170892079990445271147673 15878169059992833953360755)
      ·
        refine ⟨23817253589989250930041133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878169059992833953360755 23817253589989250930041133)
        ·
          refine ⟨8931470096245969098765425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23817253589989250930041133 8931470096245969098765425)
          ·
            refine ⟨6698602572184476824074069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931470096245969098765425 6698602572184476824074069)
            ·
              refine ⟨39249624446393418891059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6698602572184476824074069 39249624446393418891059)
              ·
                rfl

theorem cell23_6191508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 9].length) (baseStart_6191508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191508 prefixEnd_6191508 := by exact prefixLift 6191508
  have htrace : WordTrace (prefixWord ++ tailWord_6191508) baseStart_6191508 baseEnd_6191508 := by
    simpa [prefixWord, tailWord_6191508, baseEnd_6191508] using wordTrace_append hprefix tailTrace_6191508
  have hstable : (prefixWord ++ tailWord_6191508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191508).length < 2 ^ (prefixWord ++ tailWord_6191508).sum := by decide
  have hdescent : baseEnd_6191508 < baseStart_6191508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191519 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6191519 : Nat := 118140960795 + 6191519 * 2 ^ 59
def prefixEnd_6191519 : Nat := 4983230072969 + 3 ^ 40 * 6191519 * 2
def baseEnd_6191519 : Nat := 3179225228445066387138229

theorem tailTrace_6191519 : CollatzResearch.WordTrace tailWord_6191519 prefixEnd_6191519 3179225228445066387138229 := by
  unfold tailWord_6191519
  simp only [CollatzResearch.WordTrace]
  refine ⟨225823250056191565104225611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150548833370794376736150407 225823250056191565104225611)
  ·
    refine ⟨338734875084287347656338417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225823250056191565104225611 338734875084287347656338417)
    ·
      refine ⟨254051156313215510742253813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338734875084287347656338417 254051156313215510742253813)
      ·
        refine ⟨23817295904363954132086295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254051156313215510742253813 23817295904363954132086295)
        ·
          refine ⟨35725943856545931198129443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23817295904363954132086295 35725943856545931198129443)
          ·
            refine ⟨53588915784818896797194165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35725943856545931198129443 53588915784818896797194165)
            ·
              refine ⟨5023960854826771574736953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53588915784818896797194165 5023960854826771574736953)
              ·
                refine ⟨3767970641120078681052715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5023960854826771574736953 3767970641120078681052715)
                ·
                  refine ⟨5651955961680118021579073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767970641120078681052715 5651955961680118021579073)
                  ·
                    refine ⟨4238966971260088516184305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5651955961680118021579073 4238966971260088516184305)
                    ·
                      refine ⟨3179225228445066387138229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238966971260088516184305 3179225228445066387138229)
                      ·
                        rfl

theorem cell23_6191519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6191519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191519 prefixEnd_6191519 := by exact prefixLift 6191519
  have htrace : WordTrace (prefixWord ++ tailWord_6191519) baseStart_6191519 baseEnd_6191519 := by
    simpa [prefixWord, tailWord_6191519, baseEnd_6191519] using wordTrace_append hprefix tailTrace_6191519
  have hstable : (prefixWord ++ tailWord_6191519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191519).length < 2 ^ (prefixWord ++ tailWord_6191519).sum := by decide
  have hdescent : baseEnd_6191519 < baseStart_6191519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191545 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6191545 : Nat := 118140960795 + 6191545 * 2 ^ 59
def prefixEnd_6191545 : Nat := 4983230072969 + 3 ^ 40 * 6191545 * 2
def baseEnd_6191545 : Nat := 3179238578942083285413109

theorem tailTrace_6191545 : CollatzResearch.WordTrace tailWord_6191545 prefixEnd_6191545 3179238578942083285413109 := by
  unfold tailWord_6191545
  simp only [CollatzResearch.WordTrace]
  refine ⟨225824198354097371544672089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150549465569398247696448059 225824198354097371544672089)
  ·
    refine ⟨169368148765573028658504067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225824198354097371544672089 169368148765573028658504067)
    ·
      refine ⟨254052223148359542987756101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169368148765573028658504067 254052223148359542987756101)
      ·
        refine ⟨47634791840317414310204269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254052223148359542987756101 47634791840317414310204269)
        ·
          refine ⟨17863046940119030366326601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47634791840317414310204269 17863046940119030366326601)
          ·
            refine ⟨13397285205089272774744951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17863046940119030366326601 13397285205089272774744951)
            ·
              refine ⟨20095927807633909162117427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397285205089272774744951 20095927807633909162117427)
              ·
                refine ⟨30143891711450863743176141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20095927807633909162117427 30143891711450863743176141)
                ·
                  refine ⟨11303959391794073903691053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30143891711450863743176141 11303959391794073903691053)
                  ·
                    refine ⟨4238984771922777713884145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303959391794073903691053 4238984771922777713884145)
                    ·
                      refine ⟨3179238578942083285413109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238984771922777713884145 3179238578942083285413109)
                      ·
                        rfl

theorem cell23_6191545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6191545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191545 prefixEnd_6191545 := by exact prefixLift 6191545
  have htrace : WordTrace (prefixWord ++ tailWord_6191545) baseStart_6191545 baseEnd_6191545 := by
    simpa [prefixWord, tailWord_6191545, baseEnd_6191545] using wordTrace_append hprefix tailTrace_6191545
  have hstable : (prefixWord ++ tailWord_6191545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191545).length < 2 ^ (prefixWord ++ tailWord_6191545).sum := by decide
  have hdescent : baseEnd_6191545 < baseStart_6191545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191561 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_6191561 : Nat := 118140960795 + 6191561 * 2 ^ 59
def prefixEnd_6191561 : Nat := 4983230072969 + 3 ^ 40 * 6191561 * 2
def baseEnd_6191561 : Nat := 3179246794632555222813035

theorem tailTrace_6191561 : CollatzResearch.WordTrace tailWord_6191561 prefixEnd_6191561 3179246794632555222813035 := by
  unfold tailWord_6191561
  simp only [CollatzResearch.WordTrace]
  refine ⟨225824781922039406277254537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150549854614692937518169691 225824781922039406277254537)
  ·
    refine ⟨169368586441529554707940903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225824781922039406277254537 169368586441529554707940903)
    ·
      refine ⟨254052879662294332061911355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169368586441529554707940903 254052879662294332061911355)
      ·
        refine ⟨381079319493441498092867033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254052879662294332061911355 381079319493441498092867033)
        ·
          refine ⟨285809489620081123569650275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381079319493441498092867033 285809489620081123569650275)
          ·
            refine ⟨428714234430121685354475413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285809489620081123569650275 428714234430121685354475413)
            ·
              refine ⟨20095979738911954000991035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 428714234430121685354475413 20095979738911954000991035)
              ·
                refine ⟨30143969608367931001486553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20095979738911954000991035 30143969608367931001486553)
                ·
                  refine ⟨22607977206275948251114915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30143969608367931001486553 22607977206275948251114915)
                  ·
                    refine ⟨33911965809413922376672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22607977206275948251114915 33911965809413922376672373)
                    ·
                      refine ⟨3179246794632555222813035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33911965809413922376672373 3179246794632555222813035)
                      ·
                        rfl

theorem cell23_6191561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_6191561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191561 prefixEnd_6191561 := by exact prefixLift 6191561
  have htrace : WordTrace (prefixWord ++ tailWord_6191561) baseStart_6191561 baseEnd_6191561 := by
    simpa [prefixWord, tailWord_6191561, baseEnd_6191561] using wordTrace_append hprefix tailTrace_6191561
  have hstable : (prefixWord ++ tailWord_6191561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191561).length < 2 ^ (prefixWord ++ tailWord_6191561).sum := by decide
  have hdescent : baseEnd_6191561 < baseStart_6191561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191562 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_6191562 : Nat := 118140960795 + 6191562 * 2 ^ 59
def prefixEnd_6191562 : Nat := 4983230072969 + 3 ^ 40 * 6191562 * 2
def baseEnd_6191562 : Nat := 3179247308113209718900531

theorem tailTrace_6191562 : CollatzResearch.WordTrace tailWord_6191562 prefixEnd_6191562 3179247308113209718900531 := by
  unfold tailWord_6191562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56456204598758945862010235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150549878930023855632027293 56456204598758945862010235)
  ·
    refine ⟨84684306898138418793015353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56456204598758945862010235 84684306898138418793015353)
    ·
      refine ⟨63513230173603814094761515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84684306898138418793015353 63513230173603814094761515)
      ·
        refine ⟨95269845260405721142142273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63513230173603814094761515 95269845260405721142142273)
        ·
          refine ⟨71452383945304290856606705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95269845260405721142142273 71452383945304290856606705)
          ·
            refine ⟨53589287958978218142455029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71452383945304290856606705 53589287958978218142455029)
            ·
              refine ⟨5023995746154207950855159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53589287958978218142455029 5023995746154207950855159)
              ·
                refine ⟨7535993619231311926282739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023995746154207950855159 7535993619231311926282739)
                ·
                  refine ⟨11303990428846967889424109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535993619231311926282739 11303990428846967889424109)
                  ·
                    refine ⟨4238996410817612958534041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303990428846967889424109 4238996410817612958534041)
                    ·
                      refine ⟨3179247308113209718900531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4238996410817612958534041 3179247308113209718900531)
                      ·
                        rfl

theorem cell23_6191562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_6191562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191562 prefixEnd_6191562 := by exact prefixLift 6191562
  have htrace : WordTrace (prefixWord ++ tailWord_6191562) baseStart_6191562 baseEnd_6191562 := by
    simpa [prefixWord, tailWord_6191562, baseEnd_6191562] using wordTrace_append hprefix tailTrace_6191562
  have hstable : (prefixWord ++ tailWord_6191562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191562).length < 2 ^ (prefixWord ++ tailWord_6191562).sum := by decide
  have hdescent : baseEnd_6191562 < baseStart_6191562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191570 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6191570 : Nat := 118140960795 + 6191570 * 2 ^ 59
def prefixEnd_6191570 : Nat := 4983230072969 + 3 ^ 40 * 6191570 * 2
def baseEnd_6191570 : Nat := 3179251415958445687600495

theorem tailTrace_6191570 : CollatzResearch.WordTrace tailWord_6191570 prefixEnd_6191570 3179251415958445687600495 := by
  unfold tailWord_6191570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56456277544751700203583041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150550073452671200542888109 56456277544751700203583041)
  ·
    refine ⟨42342208158563775152687281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56456277544751700203583041 42342208158563775152687281)
    ·
      refine ⟨31756656118922831364515461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42342208158563775152687281 31756656118922831364515461)
      ·
        refine ⟨5954373022298030880846649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31756656118922831364515461 5954373022298030880846649)
        ·
          refine ⟨4465779766723523160634987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954373022298030880846649 4465779766723523160634987)
          ·
            refine ⟨6698669650085284740952481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465779766723523160634987 6698669650085284740952481)
            ·
              refine ⟨5024002237563963555714361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698669650085284740952481 5024002237563963555714361)
              ·
                refine ⟨3768001678172972666785771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024002237563963555714361 3768001678172972666785771)
                ·
                  refine ⟨5652002517259459000178657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768001678172972666785771 5652002517259459000178657)
                  ·
                    refine ⟨4239001887944594250133993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652002517259459000178657 4239001887944594250133993)
                    ·
                      refine ⟨3179251415958445687600495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239001887944594250133993 3179251415958445687600495)
                      ·
                        rfl

theorem cell23_6191570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6191570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191570 prefixEnd_6191570 := by exact prefixLift 6191570
  have htrace : WordTrace (prefixWord ++ tailWord_6191570) baseStart_6191570 baseEnd_6191570 := by
    simpa [prefixWord, tailWord_6191570, baseEnd_6191570] using wordTrace_append hprefix tailTrace_6191570
  have hstable : (prefixWord ++ tailWord_6191570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191570).length < 2 ^ (prefixWord ++ tailWord_6191570).sum := by decide
  have hdescent : baseEnd_6191570 < baseStart_6191570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191592 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6191592 : Nat := 118140960795 + 6191592 * 2 ^ 59
def prefixEnd_6191592 : Nat := 4983230072969 + 3 ^ 40 * 6191592 * 2
def baseEnd_6191592 : Nat := 3179262712532844601525393

theorem tailTrace_6191592 : CollatzResearch.WordTrace tailWord_6191592 prefixEnd_6191592 3179262712532844601525393 := by
  unfold tailWord_6191592
  simp only [CollatzResearch.WordTrace]
  refine ⟨112912956292463549285816515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150550608389951399047755353 112912956292463549285816515)
  ·
    refine ⟨169369434438695323928724773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112912956292463549285816515 169369434438695323928724773)
    ·
      refine ⟨31756768957255373236635895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169369434438695323928724773 31756768957255373236635895)
      ·
        refine ⟨47635153435883059854953843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31756768957255373236635895 47635153435883059854953843)
        ·
          refine ⟨71452730153824589782430765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47635153435883059854953843 71452730153824589782430765)
          ·
            refine ⟨26794773807684221168411537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71452730153824589782430765 26794773807684221168411537)
            ·
              refine ⟨20096080355763165876308653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26794773807684221168411537 20096080355763165876308653)
              ·
                refine ⟨7536030133411187203615745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20096080355763165876308653 7536030133411187203615745)
                ·
                  refine ⟨5652022600058390402711809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7536030133411187203615745 5652022600058390402711809)
                  ·
                    refine ⟨4239016950043792802033857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652022600058390402711809 4239016950043792802033857)
                    ·
                      refine ⟨3179262712532844601525393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239016950043792802033857 3179262712532844601525393)
                      ·
                        rfl

theorem cell23_6191592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6191592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191592 prefixEnd_6191592 := by exact prefixLift 6191592
  have htrace : WordTrace (prefixWord ++ tailWord_6191592) baseStart_6191592 baseEnd_6191592 := by
    simpa [prefixWord, tailWord_6191592, baseEnd_6191592] using wordTrace_append hprefix tailTrace_6191592
  have hstable : (prefixWord ++ tailWord_6191592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191592).length < 2 ^ (prefixWord ++ tailWord_6191592).sum := by decide
  have hdescent : baseEnd_6191592 < baseStart_6191592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191598 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_6191598 : Nat := 118140960795 + 6191598 * 2 ^ 59
def prefixEnd_6191598 : Nat := 4983230072969 + 3 ^ 40 * 6191598 * 2
def baseEnd_6191598 : Nat := 353251754824085730894485

theorem tailTrace_6191598 : CollatzResearch.WordTrace tailWord_6191598 prefixEnd_6191598 353251754824085730894485 := by
  unfold tailWord_6191598
  simp only [CollatzResearch.WordTrace]
  refine ⟨28228266427863170199543931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150550754281936907730900965 28228266427863170199543931)
  ·
    refine ⟨42342399641794755299315897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28228266427863170199543931 42342399641794755299315897)
    ·
      refine ⟨31756799731346066474486923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42342399641794755299315897 31756799731346066474486923)
      ·
        refine ⟨47635199597019099711730385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31756799731346066474486923 47635199597019099711730385)
        ·
          refine ⟨35726399697764324783797789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47635199597019099711730385 35726399697764324783797789)
          ·
            refine ⟨13397399886661621793924171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35726399697764324783797789 13397399886661621793924171)
            ·
              refine ⟨20096099829992432690886257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397399886661621793924171 20096099829992432690886257)
              ·
                refine ⟨15072074872494324518164693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096099829992432690886257 15072074872494324518164693)
                ·
                  refine ⟨353251754824085730894485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15072074872494324518164693 353251754824085730894485)
                  ·
                    rfl

theorem cell23_6191598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_6191598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191598 prefixEnd_6191598 := by exact prefixLift 6191598
  have htrace : WordTrace (prefixWord ++ tailWord_6191598) baseStart_6191598 baseEnd_6191598 := by
    simpa [prefixWord, tailWord_6191598, baseEnd_6191598] using wordTrace_append hprefix tailTrace_6191598
  have hstable : (prefixWord ++ tailWord_6191598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191598).length < 2 ^ (prefixWord ++ tailWord_6191598).sum := by decide
  have hdescent : baseEnd_6191598 < baseStart_6191598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191621 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_6191621 : Nat := 118140960795 + 6191621 * 2 ^ 59
def prefixEnd_6191621 : Nat := 4983230072969 + 3 ^ 40 * 6191621 * 2
def baseEnd_6191621 : Nat := 3179277603471824988062759

theorem tailTrace_6191621 : CollatzResearch.WordTrace tailWord_6191621 prefixEnd_6191621 3179277603471824988062759 := by
  unfold tailWord_6191621
  simp only [CollatzResearch.WordTrace]
  refine ⟨225826970301822036524438717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150551313534548024349625811 225826970301822036524438717)
  ·
    refine ⟨84685113863183263696664519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225826970301822036524438717 84685113863183263696664519)
    ·
      refine ⟨127027670794774895544996779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84685113863183263696664519 127027670794774895544996779)
      ·
        refine ⟨190541506192162343317495169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127027670794774895544996779 190541506192162343317495169)
        ·
          refine ⟨142906129644121757488121377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190541506192162343317495169 142906129644121757488121377)
          ·
            refine ⟨107179597233091318116091033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142906129644121757488121377 107179597233091318116091033)
            ·
              refine ⟨80384697924818488587068275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107179597233091318116091033 80384697924818488587068275)
              ·
                refine ⟨120577046887227732880602413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80384697924818488587068275 120577046887227732880602413)
                ·
                  refine ⟨45216392582710399830225905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120577046887227732880602413 45216392582710399830225905)
                  ·
                    refine ⟨33912294437032799872669429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45216392582710399830225905 33912294437032799872669429)
                    ·
                      refine ⟨3179277603471824988062759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33912294437032799872669429 3179277603471824988062759)
                      ·
                        rfl

theorem cell23_6191621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_6191621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191621 prefixEnd_6191621 := by exact prefixLift 6191621
  have htrace : WordTrace (prefixWord ++ tailWord_6191621) baseStart_6191621 baseEnd_6191621 := by
    simpa [prefixWord, tailWord_6191621, baseEnd_6191621] using wordTrace_append hprefix tailTrace_6191621
  have hstable : (prefixWord ++ tailWord_6191621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191621).length < 2 ^ (prefixWord ++ tailWord_6191621).sum := by decide
  have hdescent : baseEnd_6191621 < baseStart_6191621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191631 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_6191631 : Nat := 118140960795 + 6191631 * 2 ^ 59
def prefixEnd_6191631 : Nat := 4983230072969 + 3 ^ 40 * 6191631 * 2
def baseEnd_6191631 : Nat := 3179282738278369948937713

theorem tailTrace_6191631 : CollatzResearch.WordTrace tailWord_6191631 prefixEnd_6191631 3179282738278369948937713 := by
  unfold tailWord_6191631
  simp only [CollatzResearch.WordTrace]
  refine ⟨225827335031785808232302747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150551556687857205488201831 225827335031785808232302747)
  ·
    refine ⟨338741002547678712348454121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225827335031785808232302747 338741002547678712348454121)
    ·
      refine ⟨254055751910759034261340591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338741002547678712348454121 254055751910759034261340591)
      ·
        refine ⟨381083627866138551392010887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254055751910759034261340591 381083627866138551392010887)
        ·
          refine ⟨571625441799207827088016331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381083627866138551392010887 571625441799207827088016331)
          ·
            refine ⟨857438162698811740632024497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571625441799207827088016331 857438162698811740632024497)
            ·
              refine ⟨643078622024108805474018373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857438162698811740632024497 643078622024108805474018373)
              ·
                refine ⟨120577241629520401026378445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643078622024108805474018373 120577241629520401026378445)
                ·
                  refine ⟨45216465611070150384891917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120577241629520401026378445 45216465611070150384891917)
                  ·
                    refine ⟨16956174604151306394334469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45216465611070150384891917 16956174604151306394334469)
                    ·
                      refine ⟨3179282738278369948937713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16956174604151306394334469 3179282738278369948937713)
                      ·
                        rfl

theorem cell23_6191631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_6191631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191631 prefixEnd_6191631 := by exact prefixLift 6191631
  have htrace : WordTrace (prefixWord ++ tailWord_6191631) baseStart_6191631 baseEnd_6191631 := by
    simpa [prefixWord, tailWord_6191631, baseEnd_6191631] using wordTrace_append hprefix tailTrace_6191631
  have hstable : (prefixWord ++ tailWord_6191631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191631).length < 2 ^ (prefixWord ++ tailWord_6191631).sum := by decide
  have hdescent : baseEnd_6191631 < baseStart_6191631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191671 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 10]
def baseStart_6191671 : Nat := 118140960795 + 6191671 * 2 ^ 59
def prefixEnd_6191671 : Nat := 4983230072969 + 3 ^ 40 * 6191671 * 2
def baseEnd_6191671 : Nat := 353255919722727754715281

theorem tailTrace_6191671 : CollatzResearch.WordTrace tailWord_6191671 prefixEnd_6191671 353255919722727754715281 := by
  unfold tailWord_6191671
  simp only [CollatzResearch.WordTrace]
  refine ⟨225828793951640895063758867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150552529301093930042505911 225828793951640895063758867)
  ·
    refine ⟨338743190927461342595638301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225828793951640895063758867 338743190927461342595638301)
    ·
      refine ⟨127028696597798003473364363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338743190927461342595638301 127028696597798003473364363)
      ·
        refine ⟨190543044896697005210046545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127028696597798003473364363 190543044896697005210046545)
        ·
          refine ⟨142907283672522753907534909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190543044896697005210046545 142907283672522753907534909)
          ·
            refine ⟨53590231377196032715325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142907283672522753907534909 53590231377196032715325591)
            ·
              refine ⟨80385347065794049072988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53590231377196032715325591 80385347065794049072988387)
              ·
                refine ⟨120578020598691073609482581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80385347065794049072988387 120578020598691073609482581)
                ·
                  refine ⟨353255919722727754715281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120578020598691073609482581 353255919722727754715281)
                  ·
                    rfl

theorem cell23_6191671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 10].length) (baseStart_6191671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191671 prefixEnd_6191671 := by exact prefixLift 6191671
  have htrace : WordTrace (prefixWord ++ tailWord_6191671) baseStart_6191671 baseEnd_6191671 := by
    simpa [prefixWord, tailWord_6191671, baseEnd_6191671] using wordTrace_append hprefix tailTrace_6191671
  have hstable : (prefixWord ++ tailWord_6191671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191671).length < 2 ^ (prefixWord ++ tailWord_6191671).sum := by decide
  have hdescent : baseEnd_6191671 < baseStart_6191671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191685 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_6191685 : Nat := 118140960795 + 6191685 * 2 ^ 59
def prefixEnd_6191685 : Nat := 4983230072969 + 3 ^ 40 * 6191685 * 2
def baseEnd_6191685 : Nat := 3179310466233712737662465

theorem tailTrace_6191685 : CollatzResearch.WordTrace tailWord_6191685 prefixEnd_6191685 3179310466233712737662465 := by
  unfold tailWord_6191685
  simp only [CollatzResearch.WordTrace]
  refine ⟨225829304573590175454768509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150552869715726783636512339 225829304573590175454768509)
  ·
    refine ⟨84685989215096315795538191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225829304573590175454768509 84685989215096315795538191)
    ·
      refine ⟨127028983822644473693307287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84685989215096315795538191 127028983822644473693307287)
      ·
        refine ⟨190543475733966710539960931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127028983822644473693307287 190543475733966710539960931)
        ·
          refine ⟨285815213600950065809941397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190543475733966710539960931 285815213600950065809941397)
          ·
            refine ⟨13397588137544534334841003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285815213600950065809941397 13397588137544534334841003)
            ·
              refine ⟨20096382206316801502261505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397588137544534334841003 20096382206316801502261505)
              ·
                refine ⟨15072286654737601126696129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096382206316801502261505 15072286654737601126696129)
                ·
                  refine ⟨11304214991053200845022097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15072286654737601126696129 11304214991053200845022097)
                  ·
                    refine ⟨8478161243289900633766573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11304214991053200845022097 8478161243289900633766573)
                    ·
                      refine ⟨3179310466233712737662465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478161243289900633766573 3179310466233712737662465)
                      ·
                        rfl

theorem cell23_6191685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_6191685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191685 prefixEnd_6191685 := by exact prefixLift 6191685
  have htrace : WordTrace (prefixWord ++ tailWord_6191685) baseStart_6191685 baseEnd_6191685 := by
    simpa [prefixWord, tailWord_6191685, baseEnd_6191685] using wordTrace_append hprefix tailTrace_6191685
  have hstable : (prefixWord ++ tailWord_6191685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191685).length < 2 ^ (prefixWord ++ tailWord_6191685).sum := by decide
  have hdescent : baseEnd_6191685 < baseStart_6191685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191691 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_6191691 : Nat := 118140960795 + 6191691 * 2 ^ 59
def prefixEnd_6191691 : Nat := 4983230072969 + 3 ^ 40 * 6191691 * 2
def baseEnd_6191691 : Nat := 3179313547117639714187437

theorem tailTrace_6191691 : CollatzResearch.WordTrace tailWord_6191691 prefixEnd_6191691 3179313547117639714187437 := by
  unfold tailWord_6191691
  simp only [CollatzResearch.WordTrace]
  refine ⟨225829523411568438479486927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150553015607712292319657951 225829523411568438479486927)
  ·
    refine ⟨338744285117352657719230391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225829523411568438479486927 338744285117352657719230391)
    ·
      refine ⟨508116427676028986578845587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338744285117352657719230391 508116427676028986578845587)
      ·
        refine ⟨762174641514043479868268381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508116427676028986578845587 762174641514043479868268381)
        ·
          refine ⟨285815490567766304950600643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762174641514043479868268381 285815490567766304950600643)
          ·
            refine ⟨428723235851649457425900965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285815490567766304950600643 428723235851649457425900965)
            ·
              refine ⟨80385606722184273267356431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 428723235851649457425900965 80385606722184273267356431)
              ·
                refine ⟨120578410083276409901034647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80385606722184273267356431 120578410083276409901034647)
                ·
                  refine ⟨180867615124914614851551971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120578410083276409901034647 180867615124914614851551971)
                  ·
                    refine ⟨271301422687371922277327957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180867615124914614851551971 271301422687371922277327957)
                    ·
                      refine ⟨3179313547117639714187437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271301422687371922277327957 3179313547117639714187437)
                      ·
                        rfl

theorem cell23_6191691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_6191691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191691 prefixEnd_6191691 := by exact prefixLift 6191691
  have htrace : WordTrace (prefixWord ++ tailWord_6191691) baseStart_6191691 baseEnd_6191691 := by
    simpa [prefixWord, tailWord_6191691, baseEnd_6191691] using wordTrace_append hprefix tailTrace_6191691
  have hstable : (prefixWord ++ tailWord_6191691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191691).length < 2 ^ (prefixWord ++ tailWord_6191691).sum := by decide
  have hdescent : baseEnd_6191691 < baseStart_6191691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191715 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 3]
def baseStart_6191715 : Nat := 118140960795 + 6191715 * 2 ^ 59
def prefixEnd_6191715 : Nat := 4983230072969 + 3 ^ 40 * 6191715 * 2
def baseEnd_6191715 : Nat := 3179325870653347620287327

theorem tailTrace_6191715 : CollatzResearch.WordTrace tailWord_6191715 prefixEnd_6191715 3179325870653347620287327 := by
  unfold tailWord_6191715
  simp only [CollatzResearch.WordTrace]
  refine ⟨225830398763481490578360599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150553599175654327052240399 225830398763481490578360599)
  ·
    refine ⟨338745598145222235867540899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225830398763481490578360599 338745598145222235867540899)
    ·
      refine ⟨508118397217833353801311349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338745598145222235867540899 508118397217833353801311349)
      ·
        refine ⟨47636099739171876918872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 508118397217833353801311349 47636099739171876918872939)
        ·
          refine ⟨71454149608757815378309409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47636099739171876918872939 71454149608757815378309409)
          ·
            refine ⟨53590612206568361533732057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71454149608757815378309409 53590612206568361533732057)
            ·
              refine ⟨40192959154926271150299043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53590612206568361533732057 40192959154926271150299043)
              ·
                refine ⟨60289438732389406725448565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40192959154926271150299043 60289438732389406725448565)
                ·
                  refine ⟨5652134881161506880510803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60289438732389406725448565 5652134881161506880510803)
                  ·
                    refine ⟨8478202321742260320766205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5652134881161506880510803 8478202321742260320766205)
                    ·
                      refine ⟨3179325870653347620287327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478202321742260320766205 3179325870653347620287327)
                      ·
                        rfl

theorem cell23_6191715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_6191715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191715 prefixEnd_6191715 := by exact prefixLift 6191715
  have htrace : WordTrace (prefixWord ++ tailWord_6191715) baseStart_6191715 baseEnd_6191715 := by
    simpa [prefixWord, tailWord_6191715, baseEnd_6191715] using wordTrace_append hprefix tailTrace_6191715
  have hstable : (prefixWord ++ tailWord_6191715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191715).length < 2 ^ (prefixWord ++ tailWord_6191715).sum := by decide
  have hdescent : baseEnd_6191715 < baseStart_6191715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191749 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_6191749 : Nat := 118140960795 + 6191749 * 2 ^ 59
def prefixEnd_6191749 : Nat := 4983230072969 + 3 ^ 40 * 6191749 * 2
def baseEnd_6191749 : Nat := 3179343328995600487262171

theorem tailTrace_6191749 : CollatzResearch.WordTrace tailWord_6191749 prefixEnd_6191749 3179343328995600487262171 := by
  unfold tailWord_6191749
  simp only [CollatzResearch.WordTrace]
  refine ⟨225831638845358314385098301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150554425896905542923398867 225831638845358314385098301)
  ·
    refine ⟨84686864567009367894411863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225831638845358314385098301 84686864567009367894411863)
    ·
      refine ⟨127030296850514051841617795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84686864567009367894411863 127030296850514051841617795)
      ·
        refine ⟨190545445275771077762426693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127030296850514051841617795 190545445275771077762426693)
        ·
          refine ⟨35727270989207077080455005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190545445275771077762426693 35727270989207077080455005)
          ·
            refine ⟨13397726620952653905170627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35727270989207077080455005 13397726620952653905170627)
            ·
              refine ⟨20096589931428980857755941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397726620952653905170627 20096589931428980857755941)
              ·
                refine ⟨3768110612142933910829239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20096589931428980857755941 3768110612142933910829239)
                ·
                  refine ⟨5652165918214400866243859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768110612142933910829239 5652165918214400866243859)
                  ·
                    refine ⟨8478248877321601299365789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5652165918214400866243859 8478248877321601299365789)
                    ·
                      refine ⟨3179343328995600487262171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478248877321601299365789 3179343328995600487262171)
                      ·
                        rfl

theorem cell23_6191749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_6191749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191749 prefixEnd_6191749 := by exact prefixLift 6191749
  have htrace : WordTrace (prefixWord ++ tailWord_6191749) baseStart_6191749 baseEnd_6191749 := by
    simpa [prefixWord, tailWord_6191749, baseEnd_6191749] using wordTrace_append hprefix tailTrace_6191749
  have hstable : (prefixWord ++ tailWord_6191749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191749).length < 2 ^ (prefixWord ++ tailWord_6191749).sum := by decide
  have hdescent : baseEnd_6191749 < baseStart_6191749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191776 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2]
def baseStart_6191776 : Nat := 118140960795 + 6191776 * 2 ^ 59
def prefixEnd_6191776 : Nat := 4983230072969 + 3 ^ 40 * 6191776 * 2
def baseEnd_6191776 : Nat := 3179357192973271881624547

theorem tailTrace_6191776 : CollatzResearch.WordTrace tailWord_6191776 prefixEnd_6191776 3179357192973271881624547 := by
  unfold tailWord_6191776
  simp only [CollatzResearch.WordTrace]
  refine ⟨112916311808130248998165591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150555082410840331997554121 112916311808130248998165591)
  ·
    refine ⟨169374467712195373497248387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112916311808130248998165591 169374467712195373497248387)
    ·
      refine ⟨254061701568293060245872581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169374467712195373497248387 254061701568293060245872581)
      ·
        refine ⟨47636569044054948796101109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254061701568293060245872581 47636569044054948796101109)
        ·
          refine ⟨4465928347880151449634479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47636569044054948796101109 4465928347880151449634479)
          ·
            refine ⟨6698892521820227174451719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465928347880151449634479 6698892521820227174451719)
            ·
              refine ⟨10048338782730340761677579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698892521820227174451719 10048338782730340761677579)
              ·
                refine ⟨15072508174095511142516369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048338782730340761677579 15072508174095511142516369)
                ·
                  refine ⟨11304381130571633356887277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15072508174095511142516369 11304381130571633356887277)
                  ·
                    refine ⟨4239142923964362508832729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11304381130571633356887277 4239142923964362508832729)
                    ·
                      refine ⟨3179357192973271881624547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239142923964362508832729 3179357192973271881624547)
                      ·
                        rfl

theorem cell23_6191776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_6191776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191776 prefixEnd_6191776 := by exact prefixLift 6191776
  have htrace : WordTrace (prefixWord ++ tailWord_6191776) baseStart_6191776 baseEnd_6191776 := by
    simpa [prefixWord, tailWord_6191776, baseEnd_6191776] using wordTrace_append hprefix tailTrace_6191776
  have hstable : (prefixWord ++ tailWord_6191776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191776).length < 2 ^ (prefixWord ++ tailWord_6191776).sum := by decide
  have hdescent : baseEnd_6191776 < baseStart_6191776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191783 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6191783 : Nat := 118140960795 + 6191783 * 2 ^ 59
def prefixEnd_6191783 : Nat := 4983230072969 + 3 ^ 40 * 6191783 * 2
def baseEnd_6191783 : Nat := 3179360787337853354237015

theorem tailTrace_6191783 : CollatzResearch.WordTrace tailWord_6191783 prefixEnd_6191783 3179360787337853354237015 := by
  unfold tailWord_6191783
  simp only [CollatzResearch.WordTrace]
  refine ⟨225832878927235138191836003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150555252618156758794557335 225832878927235138191836003)
  ·
    refine ⟨338749318390852707287754005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225832878927235138191836003 338749318390852707287754005)
    ·
      refine ⟨15878874299571220654113469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 338749318390852707287754005 15878874299571220654113469)
      ·
        refine ⟨5954577862339207745292551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15878874299571220654113469 5954577862339207745292551)
        ·
          refine ⟨8931866793508811617938827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954577862339207745292551 8931866793508811617938827)
          ·
            refine ⟨13397800190263217426908241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931866793508811617938827 13397800190263217426908241)
            ·
              refine ⟨10048350142697413070181181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13397800190263217426908241 10048350142697413070181181)
              ·
                refine ⟨3768131303511529901317943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10048350142697413070181181 3768131303511529901317943)
                ·
                  refine ⟨5652196955267294851976915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768131303511529901317943 5652196955267294851976915)
                  ·
                    refine ⟨8478295432900942277965373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5652196955267294851976915 8478295432900942277965373)
                    ·
                      refine ⟨3179360787337853354237015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478295432900942277965373 3179360787337853354237015)
                      ·
                        rfl

theorem cell23_6191783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6191783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191783 prefixEnd_6191783 := by exact prefixLift 6191783
  have htrace : WordTrace (prefixWord ++ tailWord_6191783) baseStart_6191783 baseEnd_6191783 := by
    simpa [prefixWord, tailWord_6191783, baseEnd_6191783] using wordTrace_append hprefix tailTrace_6191783
  have hstable : (prefixWord ++ tailWord_6191783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191783).length < 2 ^ (prefixWord ++ tailWord_6191783).sum := by decide
  have hdescent : baseEnd_6191783 < baseStart_6191783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191789 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6191789 : Nat := 118140960795 + 6191789 * 2 ^ 59
def prefixEnd_6191789 : Nat := 4983230072969 + 3 ^ 40 * 6191789 * 2
def baseEnd_6191789 : Nat := 3179363868221780330761987

theorem tailTrace_6191789 : CollatzResearch.WordTrace tailWord_6191789 prefixEnd_6191789 3179363868221780330761987 := by
  unfold tailWord_6191789
  simp only [CollatzResearch.WordTrace]
  refine ⟨225833097765213401216554421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150555398510142267477702947 225833097765213401216554421)
  ·
    refine ⟨21171852915488756364051977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225833097765213401216554421 21171852915488756364051977)
    ·
      refine ⟨15878889686616567273038983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21171852915488756364051977 15878889686616567273038983)
      ·
        refine ⟨23818334529924850909558475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878889686616567273038983 23818334529924850909558475)
        ·
          refine ⟨35727501794887276364337713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23818334529924850909558475 35727501794887276364337713)
          ·
            refine ⟨26795626346165457273253285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35727501794887276364337713 26795626346165457273253285)
            ·
              refine ⟨5024179939906023238734991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26795626346165457273253285 5024179939906023238734991)
              ·
                refine ⟨7536269909859034858102487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024179939906023238734991 7536269909859034858102487)
                ·
                  refine ⟨11304404864788552287153731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7536269909859034858102487 11304404864788552287153731)
                  ·
                    refine ⟨16956607297182828430730597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11304404864788552287153731 16956607297182828430730597)
                    ·
                      refine ⟨3179363868221780330761987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16956607297182828430730597 3179363868221780330761987)
                      ·
                        rfl

theorem cell23_6191789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6191789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191789 prefixEnd_6191789 := by exact prefixLift 6191789
  have htrace : WordTrace (prefixWord ++ tailWord_6191789) baseStart_6191789 baseEnd_6191789 := by
    simpa [prefixWord, tailWord_6191789, baseEnd_6191789] using wordTrace_append hprefix tailTrace_6191789
  have hstable : (prefixWord ++ tailWord_6191789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191789).length < 2 ^ (prefixWord ++ tailWord_6191789).sum := by decide
  have hdescent : baseEnd_6191789 < baseStart_6191789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191799 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 2, 4]
def baseStart_6191799 : Nat := 118140960795 + 6191799 * 2 ^ 59
def prefixEnd_6191799 : Nat := 4983230072969 + 3 ^ 40 * 6191799 * 2
def baseEnd_6191799 : Nat := 1059789667676108430545647

theorem tailTrace_6191799 : CollatzResearch.WordTrace tailWord_6191799 prefixEnd_6191799 1059789667676108430545647 := by
  unfold tailWord_6191799
  simp only [CollatzResearch.WordTrace]
  refine ⟨225833462495177172924418451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150555641663451448616278967 225833462495177172924418451)
  ·
    refine ⟨338750193742765759386627677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225833462495177172924418451 338750193742765759386627677)
    ·
      refine ⟨127031322653537159769985379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338750193742765759386627677 127031322653537159769985379)
      ·
        refine ⟨190546983980305739654978069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127031322653537159769985379 190546983980305739654978069)
        ·
          refine ⟨8931889874076831546327097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190546983980305739654978069 8931889874076831546327097)
          ·
            refine ⟨6698917405557623659745323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931889874076831546327097 6698917405557623659745323)
            ·
              refine ⟨10048376108336435489617985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698917405557623659745323 10048376108336435489617985)
              ·
                refine ⟨7536282081252326617213489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10048376108336435489617985 7536282081252326617213489)
                ·
                  refine ⟨5652211560939244962910117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7536282081252326617213489 5652211560939244962910117)
                  ·
                    refine ⟨1059789667676108430545647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652211560939244962910117 1059789667676108430545647)
                    ·
                      rfl

theorem cell23_6191799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_6191799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191799 prefixEnd_6191799 := by exact prefixLift 6191799
  have htrace : WordTrace (prefixWord ++ tailWord_6191799) baseStart_6191799 baseEnd_6191799 := by
    simpa [prefixWord, tailWord_6191799, baseEnd_6191799] using wordTrace_append hprefix tailTrace_6191799
  have hstable : (prefixWord ++ tailWord_6191799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191799).length < 2 ^ (prefixWord ++ tailWord_6191799).sum := by decide
  have hdescent : baseEnd_6191799 < baseStart_6191799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191806 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_6191806 : Nat := 118140960795 + 6191806 * 2 ^ 59
def prefixEnd_6191806 : Nat := 4983230072969 + 3 ^ 40 * 6191806 * 2
def baseEnd_6191806 : Nat := 3179372597392906764249409

theorem tailTrace_6191806 : CollatzResearch.WordTrace tailWord_6191806 prefixEnd_6191806 3179372597392906764249409 := by
  unfold tailWord_6191806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229214725768976639990409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150555811870767875413282181 28229214725768976639990409)
  ·
    refine ⟨21171911044326732479992807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28229214725768976639990409 21171911044326732479992807)
    ·
      refine ⟨31757866566490098719989211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21171911044326732479992807 31757866566490098719989211)
      ·
        refine ⟨47636799849735148079983817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31757866566490098719989211 47636799849735148079983817)
        ·
          refine ⟨35727599887301361059987863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47636799849735148079983817 35727599887301361059987863)
          ·
            refine ⟨53591399830952041589981795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35727599887301361059987863 53591399830952041589981795)
            ·
              refine ⟨80387099746428062384972693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53591399830952041589981795 80387099746428062384972693)
              ·
                refine ⟨3768145300613815424295595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80387099746428062384972693 3768145300613815424295595)
                ·
                  refine ⟨5652217950920723136443393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768145300613815424295595 5652217950920723136443393)
                  ·
                    refine ⟨4239163463190542352332545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652217950920723136443393 4239163463190542352332545)
                    ·
                      refine ⟨3179372597392906764249409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239163463190542352332545 3179372597392906764249409)
                      ·
                        rfl

theorem cell23_6191806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_6191806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191806 prefixEnd_6191806 := by exact prefixLift 6191806
  have htrace : WordTrace (prefixWord ++ tailWord_6191806) baseStart_6191806 baseEnd_6191806 := by
    simpa [prefixWord, tailWord_6191806, baseEnd_6191806] using wordTrace_append hprefix tailTrace_6191806
  have hstable : (prefixWord ++ tailWord_6191806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191806).length < 2 ^ (prefixWord ++ tailWord_6191806).sum := by decide
  have hdescent : baseEnd_6191806 < baseStart_6191806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191809 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6191809 : Nat := 118140960795 + 6191809 * 2 ^ 59
def prefixEnd_6191809 : Nat := 4983230072969 + 3 ^ 40 * 6191809 * 2
def baseEnd_6191809 : Nat := 3179374137834870252511895

theorem tailTrace_6191809 : CollatzResearch.WordTrace tailWord_6191809 prefixEnd_6191809 3179374137834870252511895 := by
  unfold tailWord_6191809
  simp only [CollatzResearch.WordTrace]
  refine ⟨225833827225140944632282481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150555884816760629754854987 225833827225140944632282481)
  ·
    refine ⟨169375370418855708474211861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225833827225140944632282481 169375370418855708474211861)
    ·
      refine ⟨7939470488383861334728681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169375370418855708474211861 7939470488383861334728681)
      ·
        refine ⟨5954602866287896001046511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7939470488383861334728681 5954602866287896001046511)
        ·
          refine ⟨8931904299431844001569767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954602866287896001046511 8931904299431844001569767)
          ·
            refine ⟨13397856449147766002354651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931904299431844001569767 13397856449147766002354651)
            ·
              refine ⟨20096784673721649003531977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397856449147766002354651 20096784673721649003531977)
              ·
                refine ⟨15072588505291236752648983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096784673721649003531977 15072588505291236752648983)
                ·
                  refine ⟨22608882757936855128973475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15072588505291236752648983 22608882757936855128973475)
                  ·
                    refine ⟨33913324136905282693460213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22608882757936855128973475 33913324136905282693460213)
                    ·
                      refine ⟨3179374137834870252511895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33913324136905282693460213 3179374137834870252511895)
                      ·
                        rfl

theorem cell23_6191809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6191809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191809 prefixEnd_6191809 := by exact prefixLift 6191809
  have htrace : WordTrace (prefixWord ++ tailWord_6191809) baseStart_6191809 baseEnd_6191809 := by
    simpa [prefixWord, tailWord_6191809, baseEnd_6191809] using wordTrace_append hprefix tailTrace_6191809
  have hstable : (prefixWord ++ tailWord_6191809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191809).length < 2 ^ (prefixWord ++ tailWord_6191809).sum := by decide
  have hdescent : baseEnd_6191809 < baseStart_6191809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191815 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_6191815 : Nat := 118140960795 + 6191815 * 2 ^ 59
def prefixEnd_6191815 : Nat := 4983230072969 + 3 ^ 40 * 6191815 * 2
def baseEnd_6191815 : Nat := 3179377218718797229036867

theorem tailTrace_6191815 : CollatzResearch.WordTrace tailWord_6191815 prefixEnd_6191815 3179377218718797229036867 := by
  unfold tailWord_6191815
  simp only [CollatzResearch.WordTrace]
  refine ⟨225834046063119207657000899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150556030708746138438000599 225834046063119207657000899)
  ·
    refine ⟨338751069094678811485501349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225834046063119207657000899 338751069094678811485501349)
    ·
      refine ⟨63515825455252277153531503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338751069094678811485501349 63515825455252277153531503)
      ·
        refine ⟨95273738182878415730297255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63515825455252277153531503 95273738182878415730297255)
        ·
          refine ⟨142910607274317623595445883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95273738182878415730297255 142910607274317623595445883)
          ·
            refine ⟨214365910911476435393168825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142910607274317623595445883 214365910911476435393168825)
            ·
              refine ⟨160774433183607326544876619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214365910911476435393168825 160774433183607326544876619)
              ·
                refine ⟨241161649775410989817314929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160774433183607326544876619 241161649775410989817314929)
                ·
                  refine ⟨180871237331558242362986197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241161649775410989817314929 180871237331558242362986197)
                  ·
                    refine ⟨4239169624958396305382489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180871237331558242362986197 4239169624958396305382489)
                    ·
                      refine ⟨3179377218718797229036867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239169624958396305382489 3179377218718797229036867)
                      ·
                        rfl

theorem cell23_6191815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_6191815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191815 prefixEnd_6191815 := by exact prefixLift 6191815
  have htrace : WordTrace (prefixWord ++ tailWord_6191815) baseStart_6191815 baseEnd_6191815 := by
    simpa [prefixWord, tailWord_6191815, baseEnd_6191815] using wordTrace_append hprefix tailTrace_6191815
  have hstable : (prefixWord ++ tailWord_6191815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191815).length < 2 ^ (prefixWord ++ tailWord_6191815).sum := by decide
  have hdescent : baseEnd_6191815 < baseStart_6191815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191822 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_6191822 : Nat := 118140960795 + 6191822 * 2 ^ 59
def prefixEnd_6191822 : Nat := 4983230072969 + 3 ^ 40 * 6191822 * 2
def baseEnd_6191822 : Nat := 3179380813083378701649335

theorem tailTrace_6191822 : CollatzResearch.WordTrace tailWord_6191822 prefixEnd_6191822 3179380813083378701649335 := by
  unfold tailWord_6191822
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229287671761730981563215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150556200916062565235003813 28229287671761730981563215)
  ·
    refine ⟨42343931507642596472344823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28229287671761730981563215 42343931507642596472344823)
    ·
      refine ⟨63515897261463894708517235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42343931507642596472344823 63515897261463894708517235)
      ·
        refine ⟨95273845892195842062775853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63515897261463894708517235 95273845892195842062775853)
        ·
          refine ⟨35727692209573440773540945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95273845892195842062775853 35727692209573440773540945)
          ·
            refine ⟨26795769157180080580155709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35727692209573440773540945 26795769157180080580155709)
            ·
              refine ⟨10048413433942530217558391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26795769157180080580155709 10048413433942530217558391)
              ·
                refine ⟨15072620150913795326337587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048413433942530217558391 15072620150913795326337587)
                ·
                  refine ⟨22608930226370692989506381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15072620150913795326337587 22608930226370692989506381)
                  ·
                    refine ⟨8478348834889009871064893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22608930226370692989506381 8478348834889009871064893)
                    ·
                      refine ⟨3179380813083378701649335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478348834889009871064893 3179380813083378701649335)
                      ·
                        rfl

theorem cell23_6191822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_6191822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191822 prefixEnd_6191822 := by exact prefixLift 6191822
  have htrace : WordTrace (prefixWord ++ tailWord_6191822) baseStart_6191822 baseEnd_6191822 := by
    simpa [prefixWord, tailWord_6191822, baseEnd_6191822] using wordTrace_append hprefix tailTrace_6191822
  have hstable : (prefixWord ++ tailWord_6191822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191822).length < 2 ^ (prefixWord ++ tailWord_6191822).sum := by decide
  have hdescent : baseEnd_6191822 < baseStart_6191822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191829 : List Nat := [1, 3, 2, 5, 1, 2, 2, 7]
def baseStart_6191829 : Nat := 118140960795 + 6191829 * 2 ^ 59
def prefixEnd_6191829 : Nat := 4983230072969 + 3 ^ 40 * 6191829 * 2
def baseEnd_6191829 : Nat := 117754978053628154602289

theorem tailTrace_6191829 : CollatzResearch.WordTrace tailWord_6191829 prefixEnd_6191829 117754978053628154602289 := by
  unfold tailWord_6191829
  simp only [CollatzResearch.WordTrace]
  refine ⟨225834556685068488048010541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150556371123378992032007027 225834556685068488048010541)
  ·
    refine ⟨84687958756900683018003953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225834556685068488048010541 84687958756900683018003953)
    ·
      refine ⟨63515969067675512263502965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84687958756900683018003953 63515969067675512263502965)
      ·
        refine ⟨5954622100094579274703403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63515969067675512263502965 5954622100094579274703403)
        ·
          refine ⟨8931933150141868912055105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954622100094579274703403 8931933150141868912055105)
          ·
            refine ⟨6698949862606401684041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931933150141868912055105 6698949862606401684041329)
            ·
              refine ⟨5024212396954801263030997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698949862606401684041329 5024212396954801263030997)
              ·
                refine ⟨117754978053628154602289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5024212396954801263030997 117754978053628154602289)
                ·
                  rfl

theorem cell23_6191829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 7].length) (baseStart_6191829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191829 prefixEnd_6191829 := by exact prefixLift 6191829
  have htrace : WordTrace (prefixWord ++ tailWord_6191829) baseStart_6191829 baseEnd_6191829 := by
    simpa [prefixWord, tailWord_6191829, baseEnd_6191829] using wordTrace_append hprefix tailTrace_6191829
  have hstable : (prefixWord ++ tailWord_6191829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191829).length < 2 ^ (prefixWord ++ tailWord_6191829).sum := by decide
  have hdescent : baseEnd_6191829 < baseStart_6191829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191912 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6191912 : Nat := 118140960795 + 6191912 * 2 ^ 59
def prefixEnd_6191912 : Nat := 4983230072969 + 3 ^ 40 * 6191912 * 2
def baseEnd_6191912 : Nat := 3179427026342283349523921

theorem tailTrace_6191912 : CollatzResearch.WordTrace tailWord_6191912 prefixEnd_6191912 3179427026342283349523921 := by
  unfold tailWord_6191912
  simp only [CollatzResearch.WordTrace]
  refine ⟨112918791971883896611640995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150558389295845195482187993 112918791971883896611640995)
  ·
    refine ⟨169378187957825844917461493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112918791971883896611640995 169378187957825844917461493)
    ·
      refine ⟨15879205121046172961012015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169378187957825844917461493 15879205121046172961012015)
      ·
        refine ⟨23818807681569259441518023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879205121046172961012015 23818807681569259441518023)
        ·
          refine ⟨35728211522353889162277035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23818807681569259441518023 35728211522353889162277035)
          ·
            refine ⟨53592317283530833743415553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35728211522353889162277035 53592317283530833743415553)
            ·
              refine ⟨40194237962648125307561665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53592317283530833743415553 40194237962648125307561665)
              ·
                refine ⟨30145678471986093980671249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40194237962648125307561665 30145678471986093980671249)
                ·
                  refine ⟨22609258853989570485503437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30145678471986093980671249 22609258853989570485503437)
                  ·
                    refine ⟨8478472070246088932063789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22609258853989570485503437 8478472070246088932063789)
                    ·
                      refine ⟨3179427026342283349523921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478472070246088932063789 3179427026342283349523921)
                      ·
                        rfl

theorem cell23_6191912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6191912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191912 prefixEnd_6191912 := by exact prefixLift 6191912
  have htrace : WordTrace (prefixWord ++ tailWord_6191912) baseStart_6191912 baseEnd_6191912 := by
    simpa [prefixWord, tailWord_6191912, baseEnd_6191912] using wordTrace_append hprefix tailTrace_6191912
  have hstable : (prefixWord ++ tailWord_6191912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191912).length < 2 ^ (prefixWord ++ tailWord_6191912).sum := by decide
  have hdescent : baseEnd_6191912 < baseStart_6191912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191922 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_6191922 : Nat := 118140960795 + 6191922 * 2 ^ 59
def prefixEnd_6191922 : Nat := 4983230072969 + 3 ^ 40 * 6191922 * 2
def baseEnd_6191922 : Nat := 3179432161148828310398875

theorem tailTrace_6191922 : CollatzResearch.WordTrace tailWord_6191922 prefixEnd_6191922 3179432161148828310398875 := by
  unfold tailWord_6191922
  simp only [CollatzResearch.WordTrace]
  refine ⟨56459487168432891232786505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150558632449154376620764013 56459487168432891232786505)
  ·
    refine ⟨42344615376324668424589879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56459487168432891232786505 42344615376324668424589879)
    ·
      refine ⟨63516923064487002636884819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42344615376324668424589879 63516923064487002636884819)
      ·
        refine ⟨95275384596730503955327229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63516923064487002636884819 95275384596730503955327229)
        ·
          refine ⟨35728269223773938983247711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95275384596730503955327229 35728269223773938983247711)
          ·
            refine ⟨53592403835660908474871567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35728269223773938983247711 53592403835660908474871567)
            ·
              refine ⟨80388605753491362712307351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53592403835660908474871567 80388605753491362712307351)
              ·
                refine ⟨120582908630237044068461027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80388605753491362712307351 120582908630237044068461027)
                ·
                  refine ⟨180874362945355566102691541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120582908630237044068461027 180874362945355566102691541)
                  ·
                    refine ⟨4239242881531771080531833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180874362945355566102691541 4239242881531771080531833)
                    ·
                      refine ⟨3179432161148828310398875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239242881531771080531833 3179432161148828310398875)
                      ·
                        rfl

theorem cell23_6191922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_6191922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191922 prefixEnd_6191922 := by exact prefixLift 6191922
  have htrace : WordTrace (prefixWord ++ tailWord_6191922) baseStart_6191922 baseEnd_6191922 := by
    simpa [prefixWord, tailWord_6191922, baseEnd_6191922] using wordTrace_append hprefix tailTrace_6191922
  have hstable : (prefixWord ++ tailWord_6191922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191922).length < 2 ^ (prefixWord ++ tailWord_6191922).sum := by decide
  have hdescent : baseEnd_6191922 < baseStart_6191922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191949 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6191949 : Nat := 118140960795 + 6191949 * 2 ^ 59
def prefixEnd_6191949 : Nat := 4983230072969 + 3 ^ 40 * 6191949 * 2
def baseEnd_6191949 : Nat := 1059815341708833234920417

theorem tailTrace_6191949 : CollatzResearch.WordTrace tailWord_6191949 prefixEnd_6191949 1059815341708833234920417 := by
  unfold tailWord_6191949
  simp only [CollatzResearch.WordTrace]
  refine ⟨225838933444633748542378901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150559288963089165694919267 225838933444633748542378901)
  ·
    refine ⟨10586200005217206962924011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225838933444633748542378901 10586200005217206962924011)
    ·
      refine ⟨15879300007825810444386017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586200005217206962924011 15879300007825810444386017)
      ·
        refine ⟨11909475005869357833289513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15879300007825810444386017 11909475005869357833289513)
        ·
          refine ⟨8932106254402018374967135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11909475005869357833289513 8932106254402018374967135)
          ·
            refine ⟨13398159381603027562450703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932106254402018374967135 13398159381603027562450703)
            ·
              refine ⟨20097239072404541343676055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13398159381603027562450703 20097239072404541343676055)
              ·
                refine ⟨30145858608606812015514083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20097239072404541343676055 30145858608606812015514083)
                ·
                  refine ⟨45218787912910218023271125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30145858608606812015514083 45218787912910218023271125)
                  ·
                    refine ⟨1059815341708833234920417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45218787912910218023271125 1059815341708833234920417)
                    ·
                      rfl

theorem cell23_6191949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6191949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191949 prefixEnd_6191949 := by exact prefixLift 6191949
  have htrace : WordTrace (prefixWord ++ tailWord_6191949) baseStart_6191949 baseEnd_6191949 := by
    simpa [prefixWord, tailWord_6191949, baseEnd_6191949] using wordTrace_append hprefix tailTrace_6191949
  have hstable : (prefixWord ++ tailWord_6191949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191949).length < 2 ^ (prefixWord ++ tailWord_6191949).sum := by decide
  have hdescent : baseEnd_6191949 < baseStart_6191949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191952 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_6191952 : Nat := 118140960795 + 6191952 * 2 ^ 59
def prefixEnd_6191952 : Nat := 4983230072969 + 3 ^ 40 * 6191952 * 2
def baseEnd_6191952 : Nat := 3179447565568463193023737

theorem tailTrace_6191952 : CollatzResearch.WordTrace tailWord_6191952 prefixEnd_6191952 3179447565568463193023737 := by
  unfold tailWord_6191952
  simp only [CollatzResearch.WordTrace]
  refine ⟨112919521431811440027369055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150559361909081920036492073 112919521431811440027369055)
  ·
    refine ⟨169379282147717160041053583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112919521431811440027369055 169379282147717160041053583)
    ·
      refine ⟨254068923221575740061580375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169379282147717160041053583 254068923221575740061580375)
      ·
        refine ⟨381103384832363610092370563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254068923221575740061580375 381103384832363610092370563)
        ·
          refine ⟨571655077248545415138555845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381103384832363610092370563 571655077248545415138555845)
          ·
            refine ⟨107185326984102265338479221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571655077248545415138555845 107185326984102265338479221)
            ·
              refine ⟨10048624404759587375482427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107185326984102265338479221 10048624404759587375482427)
              ·
                refine ⟨15072936607139381063223641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048624404759587375482427 15072936607139381063223641)
                ·
                  refine ⟨11304702455354535797417731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15072936607139381063223641 11304702455354535797417731)
                  ·
                    refine ⟨16957053683031803696126597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11304702455354535797417731 16957053683031803696126597)
                    ·
                      refine ⟨3179447565568463193023737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16957053683031803696126597 3179447565568463193023737)
                      ·
                        rfl

theorem cell23_6191952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_6191952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191952 prefixEnd_6191952 := by exact prefixLift 6191952
  have htrace : WordTrace (prefixWord ++ tailWord_6191952) baseStart_6191952 baseEnd_6191952 := by
    simpa [prefixWord, tailWord_6191952, baseEnd_6191952] using wordTrace_append hprefix tailTrace_6191952
  have hstable : (prefixWord ++ tailWord_6191952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191952).length < 2 ^ (prefixWord ++ tailWord_6191952).sum := by decide
  have hdescent : baseEnd_6191952 < baseStart_6191952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6191979 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 1, 4]
def baseStart_6191979 : Nat := 118140960795 + 6191979 * 2 ^ 59
def prefixEnd_6191979 : Nat := 4983230072969 + 3 ^ 40 * 6191979 * 2
def baseEnd_6191979 : Nat := 1059820476515378195795371

theorem tailTrace_6191979 : CollatzResearch.WordTrace tailWord_6191979 prefixEnd_6191979 1059820476515378195795371 := by
  unfold tailWord_6191979
  simp only [CollatzResearch.WordTrace]
  refine ⟨225840027634525063665970991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150560018423016709110647327 225840027634525063665970991)
  ·
    refine ⟨338760041451787595498956487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225840027634525063665970991 338760041451787595498956487)
    ·
      refine ⟨508140062177681393248434731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338760041451787595498956487 508140062177681393248434731)
      ·
        refine ⟨762210093266522089872652097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508140062177681393248434731 762210093266522089872652097)
        ·
          refine ⟨571657569949891567404489073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762210093266522089872652097 571657569949891567404489073)
          ·
            refine ⟨428743177462418675553366805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571657569949891567404489073 428743177462418675553366805)
            ·
              refine ⟨20097336443550875416564069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 428743177462418675553366805 20097336443550875416564069)
              ·
                refine ⟨3768250583165789140605763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20097336443550875416564069 3768250583165789140605763)
                ·
                  refine ⟨5652375874748683710908645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768250583165789140605763 5652375874748683710908645)
                  ·
                    refine ⟨1059820476515378195795371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652375874748683710908645 1059820476515378195795371)
                    ·
                      rfl

theorem cell23_6191979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 4].length) (baseStart_6191979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6191979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6191979 prefixEnd_6191979 := by exact prefixLift 6191979
  have htrace : WordTrace (prefixWord ++ tailWord_6191979) baseStart_6191979 baseEnd_6191979 := by
    simpa [prefixWord, tailWord_6191979, baseEnd_6191979] using wordTrace_append hprefix tailTrace_6191979
  have hstable : (prefixWord ++ tailWord_6191979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6191979).length < 2 ^ (prefixWord ++ tailWord_6191979).sum := by decide
  have hdescent : baseEnd_6191979 < baseStart_6191979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6191979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192076 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6192076 : Nat := 118140960795 + 6192076 * 2 ^ 59
def prefixEnd_6192076 : Nat := 4983230072969 + 3 ^ 40 * 6192076 * 2
def baseEnd_6192076 : Nat := 3179511237169620707873167

theorem tailTrace_6192076 : CollatzResearch.WordTrace tailWord_6192076 prefixEnd_6192076 3179511237169620707873167 := by
  unfold tailWord_6192076
  simp only [CollatzResearch.WordTrace]
  refine ⟨112921782757586824616126041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150562377010115766154834721 112921782757586824616126041)
  ·
    refine ⟨84691337068190118462094531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112921782757586824616126041 84691337068190118462094531)
    ·
      refine ⟨127037005602285177693141797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84691337068190118462094531 127037005602285177693141797)
      ·
        refine ⟨23819438550428470817464087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127037005602285177693141797 23819438550428470817464087)
        ·
          refine ⟨35729157825642706226196131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23819438550428470817464087 35729157825642706226196131)
          ·
            refine ⟨53593736738464059339294197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35729157825642706226196131 53593736738464059339294197)
            ·
              refine ⟨5024412819231005563058831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53593736738464059339294197 5024412819231005563058831)
              ·
                refine ⟨7536619228846508344588247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024412819231005563058831 7536619228846508344588247)
                ·
                  refine ⟨11304928843269762516882371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7536619228846508344588247 11304928843269762516882371)
                  ·
                    refine ⟨16957393264904643775323557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11304928843269762516882371 16957393264904643775323557)
                    ·
                      refine ⟨3179511237169620707873167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16957393264904643775323557 3179511237169620707873167)
                      ·
                        rfl

theorem cell23_6192076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6192076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192076 prefixEnd_6192076 := by exact prefixLift 6192076
  have htrace : WordTrace (prefixWord ++ tailWord_6192076) baseStart_6192076 baseEnd_6192076 := by
    simpa [prefixWord, tailWord_6192076, baseEnd_6192076] using wordTrace_append hprefix tailTrace_6192076
  have hstable : (prefixWord ++ tailWord_6192076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192076).length < 2 ^ (prefixWord ++ tailWord_6192076).sum := by decide
  have hdescent : baseEnd_6192076 < baseStart_6192076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192079 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_6192079 : Nat := 118140960795 + 6192079 * 2 ^ 59
def prefixEnd_6192079 : Nat := 4983230072969 + 3 ^ 40 * 6192079 * 2
def baseEnd_6192079 : Nat := 3179512777611584196135653

theorem tailTrace_6192079 : CollatzResearch.WordTrace tailWord_6192079 prefixEnd_6192079 3179512777611584196135653 := by
  unfold tailWord_6192079
  simp only [CollatzResearch.WordTrace]
  refine ⟨225843674934162780744611291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150562449956108520496407527 225843674934162780744611291)
  ·
    refine ⟨338765512401244171116916937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225843674934162780744611291 338765512401244171116916937)
    ·
      refine ⟨254074134300933128337687703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338765512401244171116916937 254074134300933128337687703)
      ·
        refine ⟨381111201451399692506531555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254074134300933128337687703 381111201451399692506531555)
        ·
          refine ⟨571666802177099538759797333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381111201451399692506531555 571666802177099538759797333)
          ·
            refine ⟨6699220338012885219841375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 571666802177099538759797333 6699220338012885219841375)
            ·
              refine ⟨10048830507019327829762063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699220338012885219841375 10048830507019327829762063)
              ·
                refine ⟨15073245760528991744643095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048830507019327829762063 15073245760528991744643095)
                ·
                  refine ⟨22609868640793487616964643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15073245760528991744643095 22609868640793487616964643)
                  ·
                    refine ⟨33914802961190231425446965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22609868640793487616964643 33914802961190231425446965)
                    ·
                      refine ⟨3179512777611584196135653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33914802961190231425446965 3179512777611584196135653)
                      ·
                        rfl

theorem cell23_6192079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_6192079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192079 prefixEnd_6192079 := by exact prefixLift 6192079
  have htrace : WordTrace (prefixWord ++ tailWord_6192079) baseStart_6192079 baseEnd_6192079 := by
    simpa [prefixWord, tailWord_6192079, baseEnd_6192079] using wordTrace_append hprefix tailTrace_6192079
  have hstable : (prefixWord ++ tailWord_6192079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192079).length < 2 ^ (prefixWord ++ tailWord_6192079).sum := by decide
  have hdescent : baseEnd_6192079 < baseStart_6192079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192082 : List Nat := [3, 2, 2, 3, 1, 12]
def baseStart_6192082 : Nat := 118140960795 + 6192082 * 2 ^ 59
def prefixEnd_6192082 : Nat := 4983230072969 + 3 ^ 40 * 6192082 * 2
def baseEnd_6192082 : Nat := 13084421061948755902873

theorem tailTrace_6192082 : CollatzResearch.WordTrace tailWord_6192082 prefixEnd_6192082 13084421061948755902873 := by
  unfold tailWord_6192082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460946088287978064242625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150562522902101274837980333 56460946088287978064242625)
  ·
    refine ⟨42345709566215983548181969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56460946088287978064242625 42345709566215983548181969)
    ·
      refine ⟨31759282174661987661136477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42345709566215983548181969 31759282174661987661136477)
      ·
        refine ⟨11909730815498245372926179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31759282174661987661136477 11909730815498245372926179)
        ·
          refine ⟨17864596223247368059389269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909730815498245372926179 17864596223247368059389269)
          ·
            refine ⟨13084421061948755902873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17864596223247368059389269 13084421061948755902873)
            ·
              rfl

theorem cell23_6192082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 12].length) (baseStart_6192082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192082 prefixEnd_6192082 := by exact prefixLift 6192082
  have htrace : WordTrace (prefixWord ++ tailWord_6192082) baseStart_6192082 baseEnd_6192082 := by
    simpa [prefixWord, tailWord_6192082, baseEnd_6192082] using wordTrace_append hprefix tailTrace_6192082
  have hstable : (prefixWord ++ tailWord_6192082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192082).length < 2 ^ (prefixWord ++ tailWord_6192082).sum := by decide
  have hdescent : baseEnd_6192082 < baseStart_6192082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192130 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6192130 : Nat := 118140960795 + 6192130 * 2 ^ 59
def prefixEnd_6192130 : Nat := 4983230072969 + 3 ^ 40 * 6192130 * 2
def baseEnd_6192130 : Nat := 3179538965124963496597919

theorem tailTrace_6192130 : CollatzResearch.WordTrace tailWord_6192130 prefixEnd_6192130 3179538965124963496597919 := by
  unfold tailWord_6192130
  simp only [CollatzResearch.WordTrace]
  refine ⟨56461383764244504113679461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150563690037985344303145229 56461383764244504113679461)
  ·
    refine ⟨10586509455795844521314899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56461383764244504113679461 10586509455795844521314899)
    ·
      refine ⟨15879764183693766781972349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586509455795844521314899 15879764183693766781972349)
      ·
        refine ⟨5954911568885162543239631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15879764183693766781972349 5954911568885162543239631)
        ·
          refine ⟨8932367353327743814859447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954911568885162543239631 8932367353327743814859447)
          ·
            refine ⟨13398551029991615722289171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932367353327743814859447 13398551029991615722289171)
            ·
              refine ⟨20097826544987423583433757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13398551029991615722289171 20097826544987423583433757)
              ·
                refine ⟨7536684954370283843787659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20097826544987423583433757 7536684954370283843787659)
                ·
                  refine ⟨11305027431555425765681489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7536684954370283843787659 11305027431555425765681489)
                  ·
                    refine ⟨8478770573666569324261117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11305027431555425765681489 8478770573666569324261117)
                    ·
                      refine ⟨3179538965124963496597919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478770573666569324261117 3179538965124963496597919)
                      ·
                        rfl

theorem cell23_6192130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6192130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192130 prefixEnd_6192130 := by exact prefixLift 6192130
  have htrace : WordTrace (prefixWord ++ tailWord_6192130) baseStart_6192130 baseEnd_6192130 := by
    simpa [prefixWord, tailWord_6192130, baseEnd_6192130] using wordTrace_append hprefix tailTrace_6192130
  have hstable : (prefixWord ++ tailWord_6192130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192130).length < 2 ^ (prefixWord ++ tailWord_6192130).sum := by decide
  have hdescent : baseEnd_6192130 < baseStart_6192130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192160 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6192160 : Nat := 118140960795 + 6192160 * 2 ^ 59
def prefixEnd_6192160 : Nat := 4983230072969 + 3 ^ 40 * 6192160 * 2
def baseEnd_6192160 : Nat := 3179554369544598379222781

theorem tailTrace_6192160 : CollatzResearch.WordTrace tailWord_6192160 prefixEnd_6192160 3179554369544598379222781 := by
  unfold tailWord_6192160
  simp only [CollatzResearch.WordTrace]
  refine ⟨112923314623434665789154967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150564419497912887718873289 112923314623434665789154967)
  ·
    refine ⟨169384971935151998683732451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112923314623434665789154967 169384971935151998683732451)
    ·
      refine ⟨254077457902727998025598677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169384971935151998683732451 254077457902727998025598677)
      ·
        refine ⟨5954940419595187453724969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254077457902727998025598677 5954940419595187453724969)
        ·
          refine ⟨4466205314696390590293727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954940419595187453724969 4466205314696390590293727)
          ·
            refine ⟨6699307972044585885440591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466205314696390590293727 6699307972044585885440591)
            ·
              refine ⟨10048961958066878828160887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699307972044585885440591 10048961958066878828160887)
              ·
                refine ⟨15073442937100318242241331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048961958066878828160887 15073442937100318242241331)
                ·
                  refine ⟨22610164405650477363361997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15073442937100318242241331 22610164405650477363361997)
                  ·
                    refine ⟨8478811652118929011260749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22610164405650477363361997 8478811652118929011260749)
                    ·
                      refine ⟨3179554369544598379222781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478811652118929011260749 3179554369544598379222781)
                      ·
                        rfl

theorem cell23_6192160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6192160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192160 prefixEnd_6192160 := by exact prefixLift 6192160
  have htrace : WordTrace (prefixWord ++ tailWord_6192160) baseStart_6192160 baseEnd_6192160 := by
    simpa [prefixWord, tailWord_6192160, baseEnd_6192160] using wordTrace_append hprefix tailTrace_6192160
  have hstable : (prefixWord ++ tailWord_6192160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192160).length < 2 ^ (prefixWord ++ tailWord_6192160).sum := by decide
  have hdescent : baseEnd_6192160 < baseStart_6192160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192170 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6192170 : Nat := 118140960795 + 6192170 * 2 ^ 59
def prefixEnd_6192170 : Nat := 4983230072969 + 3 ^ 40 * 6192170 * 2
def baseEnd_6192170 : Nat := 3179559504351143340097735

theorem tailTrace_6192170 : CollatzResearch.WordTrace tailWord_6192170 prefixEnd_6192170 3179559504351143340097735 := by
  unfold tailWord_6192170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56461748494208275821543491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150564662651222068857449309 56461748494208275821543491)
  ·
    refine ⟨84692622741312413732315237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56461748494208275821543491 84692622741312413732315237)
    ·
      refine ⟨15879866763996077574809107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84692622741312413732315237 15879866763996077574809107)
      ·
        refine ⟨23819800145994116362213661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879866763996077574809107 23819800145994116362213661)
        ·
          refine ⟨8932425054747793635830123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23819800145994116362213661 8932425054747793635830123)
          ·
            refine ⟨13398637582121690453745185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932425054747793635830123 13398637582121690453745185)
            ·
              refine ⟨10048978186591267840308889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13398637582121690453745185 10048978186591267840308889)
              ·
                refine ⟨7536733639943450880231667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10048978186591267840308889 7536733639943450880231667)
                ·
                  refine ⟨11305100459915176320347501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7536733639943450880231667 11305100459915176320347501)
                  ·
                    refine ⟨4239412672468191120130313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11305100459915176320347501 4239412672468191120130313)
                    ·
                      refine ⟨3179559504351143340097735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239412672468191120130313 3179559504351143340097735)
                      ·
                        rfl

theorem cell23_6192170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6192170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192170 prefixEnd_6192170 := by exact prefixLift 6192170
  have htrace : WordTrace (prefixWord ++ tailWord_6192170) baseStart_6192170 baseEnd_6192170 := by
    simpa [prefixWord, tailWord_6192170, baseEnd_6192170] using wordTrace_append hprefix tailTrace_6192170
  have hstable : (prefixWord ++ tailWord_6192170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192170).length < 2 ^ (prefixWord ++ tailWord_6192170).sum := by decide
  have hdescent : baseEnd_6192170 < baseStart_6192170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192172 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 7]
def baseStart_6192172 : Nat := 118140960795 + 6192172 * 2 ^ 59
def prefixEnd_6192172 : Nat := 4983230072969 + 3 ^ 40 * 6192172 * 2
def baseEnd_6192172 : Nat := 353284503479161370252525

theorem tailTrace_6192172 : CollatzResearch.WordTrace tailWord_6192172 prefixEnd_6192172 353284503479161370252525 := by
  unfold tailWord_6192172
  simp only [CollatzResearch.WordTrace]
  refine ⟨112923533461412928813873385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150564711281883905085164513 112923533461412928813873385)
  ·
    refine ⟨84692650096059696610405039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112923533461412928813873385 84692650096059696610405039)
    ·
      refine ⟨127038975144089544915607559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84692650096059696610405039 127038975144089544915607559)
      ·
        refine ⟨190558462716134317373411339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127038975144089544915607559 190558462716134317373411339)
        ·
          refine ⟨285837694074201476060117009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190558462716134317373411339 285837694074201476060117009)
          ·
            refine ⟨214378270555651107045087757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285837694074201476060117009 214378270555651107045087757)
            ·
              refine ⟨80391851458369165141907909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214378270555651107045087757 80391851458369165141907909)
              ·
                refine ⟨15073472148444218464107733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80391851458369165141907909 15073472148444218464107733)
                ·
                  refine ⟨353284503479161370252525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15073472148444218464107733 353284503479161370252525)
                  ·
                    rfl

theorem cell23_6192172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_6192172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192172 prefixEnd_6192172 := by exact prefixLift 6192172
  have htrace : WordTrace (prefixWord ++ tailWord_6192172) baseStart_6192172 baseEnd_6192172 := by
    simpa [prefixWord, tailWord_6192172, baseEnd_6192172] using wordTrace_append hprefix tailTrace_6192172
  have hstable : (prefixWord ++ tailWord_6192172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192172).length < 2 ^ (prefixWord ++ tailWord_6192172).sum := by decide
  have hdescent : baseEnd_6192172 < baseStart_6192172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192266 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_6192266 : Nat := 118140960795 + 6192266 * 2 ^ 59
def prefixEnd_6192266 : Nat := 4983230072969 + 3 ^ 40 * 6192266 * 2
def baseEnd_6192266 : Nat := 1059869599497991654832431

theorem tailTrace_6192266 : CollatzResearch.WordTrace tailWord_6192266 prefixEnd_6192266 1059869599497991654832431 := by
  unfold tailWord_6192266
  simp only [CollatzResearch.WordTrace]
  refine ⟨56462623846121327920417163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150566996922990207787779101 56462623846121327920417163)
  ·
    refine ⟨84693935769181991880625745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56462623846121327920417163 84693935769181991880625745)
    ·
      refine ⟨63520451826886493910469309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84693935769181991880625745 63520451826886493910469309)
      ·
        refine ⟨23820169435082435216425991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63520451826886493910469309 23820169435082435216425991)
        ·
          refine ⟨35730254152623652824638987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23820169435082435216425991 35730254152623652824638987)
          ·
            refine ⟨53595381228935479236958481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35730254152623652824638987 53595381228935479236958481)
            ·
              refine ⟨40196535921701609427718861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53595381228935479236958481 40196535921701609427718861)
              ·
                refine ⟨15073700970638103535394573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40196535921701609427718861 15073700970638103535394573)
                ·
                  refine ⟨5652637863989288825772965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15073700970638103535394573 5652637863989288825772965)
                  ·
                    refine ⟨1059869599497991654832431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652637863989288825772965 1059869599497991654832431)
                    ·
                      rfl

theorem cell23_6192266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_6192266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192266 prefixEnd_6192266 := by exact prefixLift 6192266
  have htrace : WordTrace (prefixWord ++ tailWord_6192266) baseStart_6192266 baseEnd_6192266 := by
    simpa [prefixWord, tailWord_6192266, baseEnd_6192266] using wordTrace_append hprefix tailTrace_6192266
  have hstable : (prefixWord ++ tailWord_6192266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192266).length < 2 ^ (prefixWord ++ tailWord_6192266).sum := by decide
  have hdescent : baseEnd_6192266 < baseStart_6192266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192290 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6192290 : Nat := 118140960795 + 6192290 * 2 ^ 59
def prefixEnd_6192290 : Nat := 4983230072969 + 3 ^ 40 * 6192290 * 2
def baseEnd_6192290 : Nat := 3179621122029682870597183

theorem tailTrace_6192290 : CollatzResearch.WordTrace tailWord_6192290 prefixEnd_6192290 3179621122029682870597183 := by
  unfold tailWord_6192290
  simp only [CollatzResearch.WordTrace]
  refine ⟨56462842684099590945135581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150567580490932242520361549 56462842684099590945135581)
  ·
    refine ⟨21173566006537346604425843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56462842684099590945135581 21173566006537346604425843)
    ·
      refine ⟨31760349009806019906638765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173566006537346604425843 31760349009806019906638765)
      ·
        refine ⟨11910130878677257464989537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31760349009806019906638765 11910130878677257464989537)
        ·
          refine ⟨8932598159007943098742153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11910130878677257464989537 8932598159007943098742153)
          ·
            refine ⟨6699448619255957324056615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8932598159007943098742153 6699448619255957324056615)
            ·
              refine ⟨10049172928883935986084923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699448619255957324056615 10049172928883935986084923)
              ·
                refine ⟨15073759393325903979127385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10049172928883935986084923 15073759393325903979127385)
                ·
                  refine ⟨11305319544994427984345539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15073759393325903979127385 11305319544994427984345539)
                  ·
                    refine ⟨16957979317491641976518309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305319544994427984345539 16957979317491641976518309)
                    ·
                      refine ⟨3179621122029682870597183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16957979317491641976518309 3179621122029682870597183)
                      ·
                        rfl

theorem cell23_6192290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6192290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192290 prefixEnd_6192290 := by exact prefixLift 6192290
  have htrace : WordTrace (prefixWord ++ tailWord_6192290) baseStart_6192290 baseEnd_6192290 := by
    simpa [prefixWord, tailWord_6192290, baseEnd_6192290] using wordTrace_append hprefix tailTrace_6192290
  have hstable : (prefixWord ++ tailWord_6192290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192290).length < 2 ^ (prefixWord ++ tailWord_6192290).sum := by decide
  have hdescent : baseEnd_6192290 < baseStart_6192290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192293 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_6192293 : Nat := 118140960795 + 6192293 * 2 ^ 59
def prefixEnd_6192293 : Nat := 4983230072969 + 3 ^ 40 * 6192293 * 2
def baseEnd_6192293 : Nat := 3179622662471646358859669

theorem tailTrace_6192293 : CollatzResearch.WordTrace tailWord_6192293 prefixEnd_6192293 3179622662471646358859669 := by
  unfold tailWord_6192293
  simp only [CollatzResearch.WordTrace]
  refine ⟨225851480155387495292901533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150567653436924996861934355 225851480155387495292901533)
  ·
    refine ⟨84694305058270310734838075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225851480155387495292901533 84694305058270310734838075)
    ·
      refine ⟨127041457587405466102257113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84694305058270310734838075 127041457587405466102257113)
      ·
        refine ⟨95281093190554099576692835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127041457587405466102257113 95281093190554099576692835)
        ·
          refine ⟨142921639785831149365039253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95281093190554099576692835 142921639785831149365039253)
          ·
            refine ⟨6699451864960835126486215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142921639785831149365039253 6699451864960835126486215)
            ·
              refine ⟨10049177797441252689729323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699451864960835126486215 10049177797441252689729323)
              ·
                refine ⟨15073766696161879034593985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10049177797441252689729323 15073766696161879034593985)
                ·
                  refine ⟨11305325022121409275945489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15073766696161879034593985 11305325022121409275945489)
                  ·
                    refine ⟨8478993766591056956959117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11305325022121409275945489 8478993766591056956959117)
                    ·
                      refine ⟨3179622662471646358859669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8478993766591056956959117 3179622662471646358859669)
                      ·
                        rfl

theorem cell23_6192293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_6192293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192293 prefixEnd_6192293 := by exact prefixLift 6192293
  have htrace : WordTrace (prefixWord ++ tailWord_6192293) baseStart_6192293 baseEnd_6192293 := by
    simpa [prefixWord, tailWord_6192293, baseEnd_6192293] using wordTrace_append hprefix tailTrace_6192293
  have hstable : (prefixWord ++ tailWord_6192293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192293).length < 2 ^ (prefixWord ++ tailWord_6192293).sum := by decide
  have hdescent : baseEnd_6192293 < baseStart_6192293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192346 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_6192346 : Nat := 118140960795 + 6192346 * 2 ^ 59
def prefixEnd_6192346 : Nat := 4983230072969 + 3 ^ 40 * 6192346 * 2
def baseEnd_6192346 : Nat := 3179649876946334651496925

theorem tailTrace_6192346 : CollatzResearch.WordTrace tailWord_6192346 prefixEnd_6192346 3179649876946334651496925 := by
  unfold tailWord_6192346
  simp only [CollatzResearch.WordTrace]
  refine ⟨56463353306048871336145223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150568942149463656896387261 56463353306048871336145223)
  ·
    refine ⟨84695029959073307004217835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56463353306048871336145223 84695029959073307004217835)
    ·
      refine ⟨127042544938609960506326753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84695029959073307004217835 127042544938609960506326753)
      ·
        refine ⟨95281908703957470379745065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127042544938609960506326753 95281908703957470379745065)
        ·
          refine ⟨71461431527968102784808799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95281908703957470379745065 71461431527968102784808799)
          ·
            refine ⟨107192147291952154177213199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71461431527968102784808799 107192147291952154177213199)
            ·
              refine ⟨160788220937928231265819799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107192147291952154177213199 160788220937928231265819799)
              ·
                refine ⟨241182331406892346898729699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160788220937928231265819799 241182331406892346898729699)
                ·
                  refine ⟨361773497110338520348094549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241182331406892346898729699 361773497110338520348094549)
                  ·
                    refine ⟨4239533169261779535329233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 361773497110338520348094549 4239533169261779535329233)
                    ·
                      refine ⟨3179649876946334651496925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239533169261779535329233 3179649876946334651496925)
                      ·
                        rfl

theorem cell23_6192346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_6192346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192346 prefixEnd_6192346 := by exact prefixLift 6192346
  have htrace : WordTrace (prefixWord ++ tailWord_6192346) baseStart_6192346 baseEnd_6192346 := by
    simpa [prefixWord, tailWord_6192346, baseEnd_6192346] using wordTrace_append hprefix tailTrace_6192346
  have hstable : (prefixWord ++ tailWord_6192346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192346).length < 2 ^ (prefixWord ++ tailWord_6192346).sum := by decide
  have hdescent : baseEnd_6192346 < baseStart_6192346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192356 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_6192356 : Nat := 118140960795 + 6192356 * 2 ^ 59
def prefixEnd_6192356 : Nat := 4983230072969 + 3 ^ 40 * 6192356 * 2
def baseEnd_6192356 : Nat := 1059885003917626537457293

theorem tailTrace_6192356 : CollatzResearch.WordTrace tailWord_6192356 prefixEnd_6192356 1059885003917626537457293 := by
  unfold tailWord_6192356
  simp only [CollatzResearch.WordTrace]
  refine ⟨112926888977079628526222461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150569185302772838034963281 112926888977079628526222461)
  ·
    refine ⟨42347583366404860697333423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112926888977079628526222461 42347583366404860697333423)
    ·
      refine ⟨63521375049607291046000135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42347583366404860697333423 63521375049607291046000135)
      ·
        refine ⟨95282062574410936569000203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63521375049607291046000135 95282062574410936569000203)
        ·
          refine ⟨142923093861616404853500305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95282062574410936569000203 142923093861616404853500305)
          ·
            refine ⟨107192320396212303640125229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142923093861616404853500305 107192320396212303640125229)
            ·
              refine ⟨40197120148579613865046961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107192320396212303640125229 40197120148579613865046961)
              ·
                refine ⟨30147840111434710398785221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40197120148579613865046961 30147840111434710398785221)
                ·
                  refine ⟨5652720020894008199772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30147840111434710398785221 5652720020894008199772229)
                  ·
                    refine ⟨1059885003917626537457293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652720020894008199772229 1059885003917626537457293)
                    ·
                      rfl

theorem cell23_6192356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_6192356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192356 prefixEnd_6192356 := by exact prefixLift 6192356
  have htrace : WordTrace (prefixWord ++ tailWord_6192356) baseStart_6192356 baseEnd_6192356 := by
    simpa [prefixWord, tailWord_6192356, baseEnd_6192356] using wordTrace_append hprefix tailTrace_6192356
  have hstable : (prefixWord ++ tailWord_6192356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192356).length < 2 ^ (prefixWord ++ tailWord_6192356).sum := by decide
  have hdescent : baseEnd_6192356 < baseStart_6192356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192366 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_6192366 : Nat := 118140960795 + 6192366 * 2 ^ 59
def prefixEnd_6192366 : Nat := 4983230072969 + 3 ^ 40 * 6192366 * 2
def baseEnd_6192366 : Nat := 3179660146559424573246833

theorem tailTrace_6192366 : CollatzResearch.WordTrace tailWord_6192366 prefixEnd_6192366 3179660146559424573246833 := by
  unfold tailWord_6192366
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231767835515378595038619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150569428456082019173539301 28231767835515378595038619)
  ·
    refine ⟨42347651753273067892557929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28231767835515378595038619 42347651753273067892557929)
    ·
      refine ⟨31760738814954800919418447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42347651753273067892557929 31760738814954800919418447)
      ·
        refine ⟨47641108222432201379127671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760738814954800919418447 47641108222432201379127671)
        ·
          refine ⟨71461662333648302068691507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47641108222432201379127671 71461662333648302068691507)
          ·
            refine ⟨107192493500472453103037261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71461662333648302068691507 107192493500472453103037261)
            ·
              refine ⟨40197185062677169913638973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107192493500472453103037261 40197185062677169913638973)
              ·
                refine ⟨15073944398503938717614615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40197185062677169913638973 15073944398503938717614615)
                ·
                  refine ⟨22610916597755908076421923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15073944398503938717614615 22610916597755908076421923)
                  ·
                    refine ⟨33916374896633862114632885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22610916597755908076421923 33916374896633862114632885)
                    ·
                      refine ⟨3179660146559424573246833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33916374896633862114632885 3179660146559424573246833)
                      ·
                        rfl

theorem cell23_6192366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_6192366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192366 prefixEnd_6192366 := by exact prefixLift 6192366
  have htrace : WordTrace (prefixWord ++ tailWord_6192366) baseStart_6192366 baseEnd_6192366 := by
    simpa [prefixWord, tailWord_6192366, baseEnd_6192366] using wordTrace_append hprefix tailTrace_6192366
  have hstable : (prefixWord ++ tailWord_6192366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192366).length < 2 ^ (prefixWord ++ tailWord_6192366).sum := by decide
  have hdescent : baseEnd_6192366 < baseStart_6192366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192389 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_6192389 : Nat := 118140960795 + 6192389 * 2 ^ 59
def prefixEnd_6192389 : Nat := 4983230072969 + 3 ^ 40 * 6192389 * 2
def baseEnd_6192389 : Nat := 3179671956614477983259227

theorem tailTrace_6192389 : CollatzResearch.WordTrace tailWord_6192389 prefixEnd_6192389 3179671956614477983259227 := by
  unfold tailWord_6192389
  simp only [CollatzResearch.WordTrace]
  refine ⟨225854981563039703688396221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150569987708693135792264147 225854981563039703688396221)
  ·
    refine ⟨84695618086139888883148583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225854981563039703688396221 84695618086139888883148583)
    ·
      refine ⟨127043427129209833324722875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84695618086139888883148583 127043427129209833324722875)
      ·
        refine ⟨190565140693814749987084313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127043427129209833324722875 190565140693814749987084313)
        ·
          refine ⟨142923855520361062490313235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190565140693814749987084313 142923855520361062490313235)
          ·
            refine ⟨214385783280541593735469853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142923855520361062490313235 214385783280541593735469853)
            ·
              refine ⟨80394668730203097650801195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214385783280541593735469853 80394668730203097650801195)
              ·
                refine ⟨120592003095304646476201793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80394668730203097650801195 120592003095304646476201793)
                ·
                  refine ⟨90444002321478484857151345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120592003095304646476201793 90444002321478484857151345)
                  ·
                    refine ⟨67833001741108863642863509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90444002321478484857151345 67833001741108863642863509)
                    ·
                      refine ⟨3179671956614477983259227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67833001741108863642863509 3179671956614477983259227)
                      ·
                        rfl

theorem cell23_6192389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_6192389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192389 prefixEnd_6192389 := by exact prefixLift 6192389
  have htrace : WordTrace (prefixWord ++ tailWord_6192389) baseStart_6192389 baseEnd_6192389 := by
    simpa [prefixWord, tailWord_6192389, baseEnd_6192389] using wordTrace_append hprefix tailTrace_6192389
  have hstable : (prefixWord ++ tailWord_6192389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192389).length < 2 ^ (prefixWord ++ tailWord_6192389).sum := by decide
  have hdescent : baseEnd_6192389 < baseStart_6192389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192413 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6192413 : Nat := 118140960795 + 6192413 * 2 ^ 59
def prefixEnd_6192413 : Nat := 4983230072969 + 3 ^ 40 * 6192413 * 2
def baseEnd_6192413 : Nat := 3179684280150185889359117

theorem tailTrace_6192413 : CollatzResearch.WordTrace tailWord_6192413 prefixEnd_6192413 3179684280150185889359117 := by
  unfold tailWord_6192413
  simp only [CollatzResearch.WordTrace]
  refine ⟨225855856914952755787269893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150570571276635170524846595 225855856914952755787269893)
  ·
    refine ⟨42347973171553641710113105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225855856914952755787269893 42347973171553641710113105)
    ·
      refine ⟨31760979878665231282584829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42347973171553641710113105 31760979878665231282584829)
      ·
        refine ⟨11910367454499461730969311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31760979878665231282584829 11910367454499461730969311)
        ·
          refine ⟨17865551181749192596453967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11910367454499461730969311 17865551181749192596453967)
          ·
            refine ⟨26798326772623788894680951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17865551181749192596453967 26798326772623788894680951)
            ·
              refine ⟨40197490158935683342021427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26798326772623788894680951 40197490158935683342021427)
              ·
                refine ⟨60296235238403525013032141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40197490158935683342021427 60296235238403525013032141)
                ·
                  refine ⟨22611088214401321879887053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60296235238403525013032141 22611088214401321879887053)
                  ·
                    refine ⟨8479158080400495704957645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22611088214401321879887053 8479158080400495704957645)
                    ·
                      refine ⟨3179684280150185889359117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8479158080400495704957645 3179684280150185889359117)
                      ·
                        rfl

theorem cell23_6192413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6192413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192413 prefixEnd_6192413 := by exact prefixLift 6192413
  have htrace : WordTrace (prefixWord ++ tailWord_6192413) baseStart_6192413 baseEnd_6192413 := by
    simpa [prefixWord, tailWord_6192413, baseEnd_6192413] using wordTrace_append hprefix tailTrace_6192413
  have hstable : (prefixWord ++ tailWord_6192413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192413).length < 2 ^ (prefixWord ++ tailWord_6192413).sum := by decide
  have hdescent : baseEnd_6192413 < baseStart_6192413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192414 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6192414 : Nat := 118140960795 + 6192414 * 2 ^ 59
def prefixEnd_6192414 : Nat := 4983230072969 + 3 ^ 40 * 6192414 * 2
def baseEnd_6192414 : Nat := 3179684793630840385446613

theorem tailTrace_6192414 : CollatzResearch.WordTrace tailWord_6192414 prefixEnd_6192414 3179684793630840385446613 := by
  unfold tailWord_6192414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231986673493641619757037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150570595591966088638704197 28231986673493641619757037)
  ·
    refine ⟨10586995002560115607408889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28231986673493641619757037 10586995002560115607408889)
    ·
      refine ⟨7940246251920086705556667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10586995002560115607408889 7940246251920086705556667)
      ·
        refine ⟨11910369377880130058335001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940246251920086705556667 11910369377880130058335001)
        ·
          refine ⟨8932777033410097543751251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11910369377880130058335001 8932777033410097543751251)
          ·
            refine ⟨13399165550115146315626877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932777033410097543751251 13399165550115146315626877)
            ·
              refine ⟨5024687081293179868360079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13399165550115146315626877 5024687081293179868360079)
              ·
                refine ⟨7537030621939769802540119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024687081293179868360079 7537030621939769802540119)
                ·
                  refine ⟨11305545932909654703810179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537030621939769802540119 11305545932909654703810179)
                  ·
                    refine ⟨16958318899364482055715269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305545932909654703810179 16958318899364482055715269)
                    ·
                      refine ⟨3179684793630840385446613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16958318899364482055715269 3179684793630840385446613)
                      ·
                        rfl

theorem cell23_6192414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6192414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192414 prefixEnd_6192414 := by exact prefixLift 6192414
  have htrace : WordTrace (prefixWord ++ tailWord_6192414) baseStart_6192414 baseEnd_6192414 := by
    simpa [prefixWord, tailWord_6192414, baseEnd_6192414] using wordTrace_append hprefix tailTrace_6192414
  have hstable : (prefixWord ++ tailWord_6192414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192414).length < 2 ^ (prefixWord ++ tailWord_6192414).sum := by decide
  have hdescent : baseEnd_6192414 < baseStart_6192414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192456 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_6192456 : Nat := 118140960795 + 6192456 * 2 ^ 59
def prefixEnd_6192456 : Nat := 4983230072969 + 3 ^ 40 * 6192456 * 2
def baseEnd_6192456 : Nat := 3179706359818329221121419

theorem tailTrace_6192456 : CollatzResearch.WordTrace tailWord_6192456 prefixEnd_6192456 3179706359818329221121419 := by
  unfold tailWord_6192456
  simp only [CollatzResearch.WordTrace]
  refine ⟨112928712626898487065542611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150571616835864649420723481 112928712626898487065542611)
  ·
    refine ⟨169393068940347730598313917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112928712626898487065542611 169393068940347730598313917)
    ·
      refine ⟨63522400852630398974367719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169393068940347730598313917 63522400852630398974367719)
      ·
        refine ⟨95283601278945598461551579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63522400852630398974367719 95283601278945598461551579)
        ·
          refine ⟨142925401918418397692327369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95283601278945598461551579 142925401918418397692327369)
          ·
            refine ⟨107194051438813798269245527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142925401918418397692327369 107194051438813798269245527)
            ·
              refine ⟨160791077158220697403868291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107194051438813798269245527 160791077158220697403868291)
              ·
                refine ⟨241186615737331046105802437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160791077158220697403868291 241186615737331046105802437)
                ·
                  refine ⟨45222490450749571144837957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241186615737331046105802437 45222490450749571144837957)
                  ·
                    refine ⟨8479216959515544589657117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45222490450749571144837957 8479216959515544589657117)
                    ·
                      refine ⟨3179706359818329221121419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8479216959515544589657117 3179706359818329221121419)
                      ·
                        rfl

theorem cell23_6192456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_6192456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192456 prefixEnd_6192456 := by exact prefixLift 6192456
  have htrace : WordTrace (prefixWord ++ tailWord_6192456) baseStart_6192456 baseEnd_6192456 := by
    simpa [prefixWord, tailWord_6192456, baseEnd_6192456] using wordTrace_append hprefix tailTrace_6192456
  have hstable : (prefixWord ++ tailWord_6192456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192456).length < 2 ^ (prefixWord ++ tailWord_6192456).sum := by decide
  have hdescent : baseEnd_6192456 < baseStart_6192456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192466 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6192466 : Nat := 118140960795 + 6192466 * 2 ^ 59
def prefixEnd_6192466 : Nat := 4983230072969 + 3 ^ 40 * 6192466 * 2
def baseEnd_6192466 : Nat := 3179711494624874181996373

theorem tailTrace_6192466 : CollatzResearch.WordTrace tailWord_6192466 prefixEnd_6192466 3179711494624874181996373 := by
  unfold tailWord_6192466
  simp only [CollatzResearch.WordTrace]
  refine ⟨56464447495940186459737313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150571859989173830559299501 56464447495940186459737313)
  ·
    refine ⟨42348335621955139844802985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56464447495940186459737313 42348335621955139844802985)
    ·
      refine ⟨31761251716466354883602239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42348335621955139844802985 31761251716466354883602239)
      ·
        refine ⟨47641877574699532325403359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761251716466354883602239 47641877574699532325403359)
        ·
          refine ⟨71462816362049298488105039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47641877574699532325403359 71462816362049298488105039)
          ·
            refine ⟨107194224543073947732157559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71462816362049298488105039 107194224543073947732157559)
            ·
              refine ⟨160791336814610921598236339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107194224543073947732157559 160791336814610921598236339)
              ·
                refine ⟨241187005221916382397354509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160791336814610921598236339 241187005221916382397354509)
                ·
                  refine ⟨90445126958218643399007941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241187005221916382397354509 90445126958218643399007941)
                  ·
                    refine ⟨16958461304665995637313989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90445126958218643399007941 16958461304665995637313989)
                    ·
                      refine ⟨3179711494624874181996373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16958461304665995637313989 3179711494624874181996373)
                      ·
                        rfl

theorem cell23_6192466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6192466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192466 prefixEnd_6192466 := by exact prefixLift 6192466
  have htrace : WordTrace (prefixWord ++ tailWord_6192466) baseStart_6192466 baseEnd_6192466 := by
    simpa [prefixWord, tailWord_6192466, baseEnd_6192466] using wordTrace_append hprefix tailTrace_6192466
  have hstable : (prefixWord ++ tailWord_6192466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192466).length < 2 ^ (prefixWord ++ tailWord_6192466).sum := by decide
  have hdescent : baseEnd_6192466 < baseStart_6192466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192487 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_6192487 : Nat := 118140960795 + 6192487 * 2 ^ 59
def prefixEnd_6192487 : Nat := 4983230072969 + 3 ^ 40 * 6192487 * 2
def baseEnd_6192487 : Nat := 3179722277718618599833777

theorem tailTrace_6192487 : CollatzResearch.WordTrace tailWord_6192487 prefixEnd_6192487 3179722277718618599833777 := by
  unfold tailWord_6192487
  simp only [CollatzResearch.WordTrace]
  refine ⟨225858555916684666425463715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150572370611123110950309143 225858555916684666425463715)
  ·
    refine ⟨338787833875026999638195573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225858555916684666425463715 338787833875026999638195573)
    ·
      refine ⟨31761359425783781216080835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338787833875026999638195573 31761359425783781216080835)
      ·
        refine ⟨47642039138675671824121253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761359425783781216080835 47642039138675671824121253)
        ·
          refine ⟨8932882338501688467022735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47642039138675671824121253 8932882338501688467022735)
          ·
            refine ⟨13399323507752532700534103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932882338501688467022735 13399323507752532700534103)
            ·
              refine ⟨20098985261628799050801155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13399323507752532700534103 20098985261628799050801155)
              ·
                refine ⟨30148477892443198576201733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20098985261628799050801155 30148477892443198576201733)
                ·
                  refine ⟨5652839604833099733037825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30148477892443198576201733 5652839604833099733037825)
                  ·
                    refine ⟨4239629703624824799778369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652839604833099733037825 4239629703624824799778369)
                    ·
                      refine ⟨3179722277718618599833777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239629703624824799778369 3179722277718618599833777)
                      ·
                        rfl

theorem cell23_6192487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_6192487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192487 prefixEnd_6192487 := by exact prefixLift 6192487
  have htrace : WordTrace (prefixWord ++ tailWord_6192487) baseStart_6192487 baseEnd_6192487 := by
    simpa [prefixWord, tailWord_6192487, baseEnd_6192487] using wordTrace_append hprefix tailTrace_6192487
  have hstable : (prefixWord ++ tailWord_6192487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192487).length < 2 ^ (prefixWord ++ tailWord_6192487).sum := by decide
  have hdescent : baseEnd_6192487 < baseStart_6192487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192493 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 7]
def baseStart_6192493 : Nat := 118140960795 + 6192493 * 2 ^ 59
def prefixEnd_6192493 : Nat := 4983230072969 + 3 ^ 40 * 6192493 * 2
def baseEnd_6192493 : Nat := 353302817622505064039861

theorem tailTrace_6192493 : CollatzResearch.WordTrace tailWord_6192493 prefixEnd_6192493 353302817622505064039861 := by
  unfold tailWord_6192493
  simp only [CollatzResearch.WordTrace]
  refine ⟨225858774754662929450182133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150572516503108619633454755 225858774754662929450182133)
  ·
    refine ⟨21174260133249649635954575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225858774754662929450182133 21174260133249649635954575)
    ·
      refine ⟨31761390199874474453931863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21174260133249649635954575 31761390199874474453931863)
      ·
        refine ⟨47642085299811711680897795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761390199874474453931863 47642085299811711680897795)
        ·
          refine ⟨71463127949717567521346693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47642085299811711680897795 71463127949717567521346693)
          ·
            refine ⟨13399336490572043910252505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71463127949717567521346693 13399336490572043910252505)
            ·
              refine ⟨10049502367929032932689379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13399336490572043910252505 10049502367929032932689379)
              ·
                refine ⟨15074253551893549399034069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10049502367929032932689379 15074253551893549399034069)
                ·
                  refine ⟨353302817622505064039861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15074253551893549399034069 353302817622505064039861)
                  ·
                    rfl

theorem cell23_6192493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_6192493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192493 prefixEnd_6192493 := by exact prefixLift 6192493
  have htrace : WordTrace (prefixWord ++ tailWord_6192493) baseStart_6192493 baseEnd_6192493 := by
    simpa [prefixWord, tailWord_6192493, baseEnd_6192493] using wordTrace_append hprefix tailTrace_6192493
  have hstable : (prefixWord ++ tailWord_6192493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192493).length < 2 ^ (prefixWord ++ tailWord_6192493).sum := by decide
  have hdescent : baseEnd_6192493 < baseStart_6192493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192506 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_6192506 : Nat := 118140960795 + 6192506 * 2 ^ 59
def prefixEnd_6192506 : Nat := 4983230072969 + 3 ^ 40 * 6192506 * 2
def baseEnd_6192506 : Nat := 1059910677950351341832063

theorem tailTrace_6192506 : CollatzResearch.WordTrace tailWord_6192506 prefixEnd_6192506 1059910677950351341832063 := by
  unfold tailWord_6192506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56464812225903958167601343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150572832602410555113603581 56464812225903958167601343)
  ·
    refine ⟨84697218338855937251402015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56464812225903958167601343 84697218338855937251402015)
    ·
      refine ⟨127045827508283905877103023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84697218338855937251402015 127045827508283905877103023)
      ·
        refine ⟨190568741262425858815654535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127045827508283905877103023 190568741262425858815654535)
        ·
          refine ⟨285853111893638788223481803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190568741262425858815654535 285853111893638788223481803)
          ·
            refine ⟨428779667840458182335222705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285853111893638788223481803 428779667840458182335222705)
            ·
              refine ⟨321584750880343636751417029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428779667840458182335222705 321584750880343636751417029)
              ·
                refine ⟨60297140790064431890890693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321584750880343636751417029 60297140790064431890890693)
                ·
                  refine ⟨11305713898137080979542005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60297140790064431890890693 11305713898137080979542005)
                  ·
                    refine ⟨1059910677950351341832063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11305713898137080979542005 1059910677950351341832063)
                    ·
                      rfl

theorem cell23_6192506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_6192506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192506 prefixEnd_6192506 := by exact prefixLift 6192506
  have htrace : WordTrace (prefixWord ++ tailWord_6192506) baseStart_6192506 baseEnd_6192506 := by
    simpa [prefixWord, tailWord_6192506, baseEnd_6192506] using wordTrace_append hprefix tailTrace_6192506
  have hstable : (prefixWord ++ tailWord_6192506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192506).length < 2 ^ (prefixWord ++ tailWord_6192506).sum := by decide
  have hdescent : baseEnd_6192506 < baseStart_6192506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
