import V185TrunkScan23Chunk1130

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6698724 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_6698724 : Nat := 118140960795 + 6698724 * 2 ^ 59
def prefixEnd_6698724 : Nat := 4983230072969 + 3 ^ 40 * 6698724 * 2
def baseEnd_6698724 : Nat := 1146555061269584815081045

theorem tailTrace_6698724 : CollatzResearch.WordTrace tailWord_6698724 prefixEnd_6698724 1146555061269584815081045 := by
  unfold tailWord_6698724
  simp only [CollatzResearch.WordTrace]
  refine ⟨122161268091837236910879613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162881690789116315881172817 122161268091837236910879613)
  ·
    refine ⟨45810475534438963841579855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122161268091837236910879613 45810475534438963841579855)
    ·
      refine ⟨68715713301658445762369783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45810475534438963841579855 68715713301658445762369783)
      ·
        refine ⟨103073569952487668643554675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68715713301658445762369783 103073569952487668643554675)
        ·
          refine ⟨154610354928731502965332013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103073569952487668643554675 154610354928731502965332013)
          ·
            refine ⟨57978883098274313611999505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154610354928731502965332013 57978883098274313611999505)
            ·
              refine ⟨43484162323705735208999629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57978883098274313611999505 43484162323705735208999629)
              ·
                refine ⟨16306560871389650703374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43484162323705735208999629 16306560871389650703374861)
                ·
                  refine ⟨6114960326771119013765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16306560871389650703374861 6114960326771119013765573)
                  ·
                    refine ⟨1146555061269584815081045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114960326771119013765573 1146555061269584815081045)
                    ·
                      rfl

theorem cell23_6698724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_6698724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698724 prefixEnd_6698724 := by exact prefixLift 6698724
  have htrace : WordTrace (prefixWord ++ tailWord_6698724) baseStart_6698724 baseEnd_6698724 := by
    simpa [prefixWord, tailWord_6698724, baseEnd_6698724] using wordTrace_append hprefix tailTrace_6698724
  have hstable : (prefixWord ++ tailWord_6698724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698724).length < 2 ^ (prefixWord ++ tailWord_6698724).sum := by decide
  have hdescent : baseEnd_6698724 < baseStart_6698724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698734 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_6698734 : Nat := 118140960795 + 6698734 * 2 ^ 59
def prefixEnd_6698734 : Nat := 4983230072969 + 3 ^ 40 * 6698734 * 2
def baseEnd_6698734 : Nat := 3439670318615299406118089

theorem tailTrace_6698734 : CollatzResearch.WordTrace tailWord_6698734 prefixEnd_6698734 3439670318615299406118089 := by
  unfold tailWord_6698734
  simp only [CollatzResearch.WordTrace]
  refine ⟨30540362614204780691202907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162881933942425497019748837 30540362614204780691202907)
  ·
    refine ⟨45810543921307171036804361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30540362614204780691202907 45810543921307171036804361)
    ·
      refine ⟨34357907940980378277603271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45810543921307171036804361 34357907940980378277603271)
      ·
        refine ⟨51536861911470567416404907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34357907940980378277603271 51536861911470567416404907)
        ·
          refine ⟨77305292867205851124607361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51536861911470567416404907 77305292867205851124607361)
          ·
            refine ⟨57978969650404388343455521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77305292867205851124607361 57978969650404388343455521)
            ·
              refine ⟨43484227237803291257591641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57978969650404388343455521 43484227237803291257591641)
              ·
                refine ⟨32613170428352468443193731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43484227237803291257591641 32613170428352468443193731)
                ·
                  refine ⟨48919755642528702664790597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32613170428352468443193731 48919755642528702664790597)
                  ·
                    refine ⟨9172454182974131749648237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48919755642528702664790597 9172454182974131749648237)
                    ·
                      refine ⟨3439670318615299406118089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9172454182974131749648237 3439670318615299406118089)
                      ·
                        rfl

theorem cell23_6698734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_6698734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698734 prefixEnd_6698734 := by exact prefixLift 6698734
  have htrace : WordTrace (prefixWord ++ tailWord_6698734) baseStart_6698734 baseEnd_6698734 := by
    simpa [prefixWord, tailWord_6698734, baseEnd_6698734] using wordTrace_append hprefix tailTrace_6698734
  have hstable : (prefixWord ++ tailWord_6698734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698734).length < 2 ^ (prefixWord ++ tailWord_6698734).sum := by decide
  have hdescent : baseEnd_6698734 < baseStart_6698734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698747 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3]
def baseStart_6698747 : Nat := 118140960795 + 6698747 * 2 ^ 59
def prefixEnd_6698747 : Nat := 4983230072969 + 3 ^ 40 * 6698747 * 2
def baseEnd_6698747 : Nat := 3439676993863807855255529

theorem tailTrace_6698747 : CollatzResearch.WordTrace tailWord_6698747 prefixEnd_6698747 3439676993863807855255529 := by
  unfold tailWord_6698747
  simp only [CollatzResearch.WordTrace]
  refine ⟨244323375062591148749846495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162882250041727432499897663 244323375062591148749846495)
  ·
    refine ⟨366485062593886723124769743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244323375062591148749846495 366485062593886723124769743)
    ·
      refine ⟨549727593890830084687154615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366485062593886723124769743 549727593890830084687154615)
      ·
        refine ⟨824591390836245127030731923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549727593890830084687154615 824591390836245127030731923)
        ·
          refine ⟨1236887086254367690546097885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824591390836245127030731923 1236887086254367690546097885)
          ·
            refine ⟨463832657345387883954786707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236887086254367690546097885 463832657345387883954786707)
            ·
              refine ⟨695748986018081825932180061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463832657345387883954786707 695748986018081825932180061)
              ·
                refine ⟨260905869756780684724567523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695748986018081825932180061 260905869756780684724567523)
                ·
                  refine ⟨391358804635171027086851285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260905869756780684724567523 391358804635171027086851285)
                  ·
                    refine ⟨9172471983636820947348077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 391358804635171027086851285 9172471983636820947348077)
                    ·
                      refine ⟨3439676993863807855255529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9172471983636820947348077 3439676993863807855255529)
                      ·
                        rfl

theorem cell23_6698747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].length) (baseStart_6698747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698747 prefixEnd_6698747 := by exact prefixLift 6698747
  have htrace : WordTrace (prefixWord ++ tailWord_6698747) baseStart_6698747 baseEnd_6698747 := by
    simpa [prefixWord, tailWord_6698747, baseEnd_6698747] using wordTrace_append hprefix tailTrace_6698747
  have hstable : (prefixWord ++ tailWord_6698747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698747).length < 2 ^ (prefixWord ++ tailWord_6698747).sum := by decide
  have hdescent : baseEnd_6698747 < baseStart_6698747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698754 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_6698754 : Nat := 118140960795 + 6698754 * 2 ^ 59
def prefixEnd_6698754 : Nat := 4983230072969 + 3 ^ 40 * 6698754 * 2
def baseEnd_6698754 : Nat := 382186732025376591985333

theorem tailTrace_6698754 : CollatzResearch.WordTrace tailWord_6698754 prefixEnd_6698754 382186732025376591985333 := by
  unfold tailWord_6698754
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080907593391447236337829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162882420249043859296900877 61080907593391447236337829)
  ·
    refine ⟨11452670173760896356813343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61080907593391447236337829 11452670173760896356813343)
    ·
      refine ⟨17179005260641344535220015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452670173760896356813343 17179005260641344535220015)
      ·
        refine ⟨25768507890962016802830023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179005260641344535220015 25768507890962016802830023)
        ·
          refine ⟨38652761836443025204245035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25768507890962016802830023 38652761836443025204245035)
          ·
            refine ⟨57979142754664537806367553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38652761836443025204245035 57979142754664537806367553)
            ·
              refine ⟨43484357065998403354775665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57979142754664537806367553 43484357065998403354775665)
              ·
                refine ⟨32613267799498802516081749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43484357065998403354775665 32613267799498802516081749)
                ·
                  refine ⟨382186732025376591985333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32613267799498802516081749 382186732025376591985333)
                  ·
                    rfl

theorem cell23_6698754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_6698754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698754 prefixEnd_6698754 := by exact prefixLift 6698754
  have htrace : WordTrace (prefixWord ++ tailWord_6698754) baseStart_6698754 baseEnd_6698754 := by
    simpa [prefixWord, tailWord_6698754, baseEnd_6698754] using wordTrace_append hprefix tailTrace_6698754
  have hstable : (prefixWord ++ tailWord_6698754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698754).length < 2 ^ (prefixWord ++ tailWord_6698754).sum := by decide
  have hdescent : baseEnd_6698754 < baseStart_6698754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698767 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 5, 5]
def baseStart_6698767 : Nat := 118140960795 + 6698767 * 2 ^ 59
def prefixEnd_6698767 : Nat := 4983230072969 + 3 ^ 40 * 6698767 * 2
def baseEnd_6698767 : Nat := 1146562421158965925668479

theorem tailTrace_6698767 : CollatzResearch.WordTrace tailWord_6698767 prefixEnd_6698767 1146562421158965925668479 := by
  unfold tailWord_6698767
  simp only [CollatzResearch.WordTrace]
  refine ⟨244324104522518692165574555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162882736348345794777049703 244324104522518692165574555)
  ·
    refine ⟨366486156783778038248361833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244324104522518692165574555 366486156783778038248361833)
    ·
      refine ⟨274864617587833528686271375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366486156783778038248361833 274864617587833528686271375)
      ·
        refine ⟨412296926381750293029407063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274864617587833528686271375 412296926381750293029407063)
        ·
          refine ⟨618445389572625439544110595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412296926381750293029407063 618445389572625439544110595)
          ·
            refine ⟨927668084358938159316165893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618445389572625439544110595 927668084358938159316165893)
            ·
              refine ⟨173937765817300904871781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 927668084358938159316165893 173937765817300904871781105)
              ·
                refine ⟨130453324362975678653835829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173937765817300904871781105 130453324362975678653835829)
                ·
                  refine ⟨12229999159028969873797109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130453324362975678653835829 12229999159028969873797109)
                  ·
                    refine ⟨1146562421158965925668479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12229999159028969873797109 1146562421158965925668479)
                    ·
                      rfl

theorem cell23_6698767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_6698767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698767 prefixEnd_6698767 := by exact prefixLift 6698767
  have htrace : WordTrace (prefixWord ++ tailWord_6698767) baseStart_6698767 baseEnd_6698767 := by
    simpa [prefixWord, tailWord_6698767, baseEnd_6698767] using wordTrace_append hprefix tailTrace_6698767
  have hstable : (prefixWord ++ tailWord_6698767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698767).length < 2 ^ (prefixWord ++ tailWord_6698767).sum := by decide
  have hdescent : baseEnd_6698767 < baseStart_6698767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698801 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_6698801 : Nat := 118140960795 + 6698801 * 2 ^ 59
def prefixEnd_6698801 : Nat := 4983230072969 + 3 ^ 40 * 6698801 * 2
def baseEnd_6698801 : Nat := 1146568240606383547993427

theorem tailTrace_6698801 : CollatzResearch.WordTrace tailWord_6698801 prefixEnd_6698801 1146568240606383547993427 := by
  unfold tailWord_6698801
  simp only [CollatzResearch.WordTrace]
  refine ⟨244325344604395515972312257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162883563069597010648208171 244325344604395515972312257)
  ·
    refine ⟨183244008453296636979234193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244325344604395515972312257 183244008453296636979234193)
    ·
      refine ⟨137433006339972477734425645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183244008453296636979234193 137433006339972477734425645)
      ·
        refine ⟨51537377377489679150409617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137433006339972477734425645 51537377377489679150409617)
        ·
          refine ⟨38653033033117259362807213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51537377377489679150409617 38653033033117259362807213)
          ·
            refine ⟨14494887387418972261052705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38653033033117259362807213 14494887387418972261052705)
            ·
              refine ⟨10871165540564229195789529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494887387418972261052705 10871165540564229195789529)
              ·
                refine ⟨8153374155423171896842147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871165540564229195789529 8153374155423171896842147)
                ·
                  refine ⟨12230061233134757845263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153374155423171896842147 12230061233134757845263221)
                  ·
                    refine ⟨1146568240606383547993427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12230061233134757845263221 1146568240606383547993427)
                    ·
                      rfl

theorem cell23_6698801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_6698801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698801 prefixEnd_6698801 := by exact prefixLift 6698801
  have htrace : WordTrace (prefixWord ++ tailWord_6698801) baseStart_6698801 baseEnd_6698801 := by
    simpa [prefixWord, tailWord_6698801, baseEnd_6698801] using wordTrace_append hprefix tailTrace_6698801
  have hstable : (prefixWord ++ tailWord_6698801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698801).length < 2 ^ (prefixWord ++ tailWord_6698801).sum := by decide
  have hdescent : baseEnd_6698801 < baseStart_6698801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698824 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6698824 : Nat := 118140960795 + 6698824 * 2 ^ 59
def prefixEnd_6698824 : Nat := 4983230072969 + 3 ^ 40 * 6698824 * 2
def baseEnd_6698824 : Nat := 3439716531874204053992675

theorem tailTrace_6698824 : CollatzResearch.WordTrace tailWord_6698824 prefixEnd_6698824 3439716531874204053992675 := by
  unfold tailWord_6698824
  simp only [CollatzResearch.WordTrace]
  refine ⟨122163091741656095450199763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162884122322208127266933017 122163091741656095450199763)
  ·
    refine ⟨183244637612484143175299645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122163091741656095450199763 183244637612484143175299645)
    ·
      refine ⟨68716739104681553690737367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183244637612484143175299645 68716739104681553690737367)
      ·
        refine ⟨103075108657022330536106051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68716739104681553690737367 103075108657022330536106051)
        ·
          refine ⟨154612662985533495804159077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103075108657022330536106051 154612662985533495804159077)
          ·
            refine ⟨28989874309787530463279827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154612662985533495804159077 28989874309787530463279827)
            ·
              refine ⟨43484811464681295694919741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28989874309787530463279827 43484811464681295694919741)
              ·
                refine ⟨16306804299255485885594903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43484811464681295694919741 16306804299255485885594903)
                ·
                  refine ⟨24460206448883228828392355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16306804299255485885594903 24460206448883228828392355)
                  ·
                    refine ⟨36690309673324843242588533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24460206448883228828392355 36690309673324843242588533)
                    ·
                      refine ⟨3439716531874204053992675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36690309673324843242588533 3439716531874204053992675)
                      ·
                        rfl

theorem cell23_6698824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6698824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698824 prefixEnd_6698824 := by exact prefixLift 6698824
  have htrace : WordTrace (prefixWord ++ tailWord_6698824) baseStart_6698824 baseEnd_6698824 := by
    simpa [prefixWord, tailWord_6698824, baseEnd_6698824] using wordTrace_append hprefix tailTrace_6698824
  have hstable : (prefixWord ++ tailWord_6698824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698824).length < 2 ^ (prefixWord ++ tailWord_6698824).sum := by decide
  have hdescent : baseEnd_6698824 < baseStart_6698824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698834 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_6698834 : Nat := 118140960795 + 6698834 * 2 ^ 59
def prefixEnd_6698834 : Nat := 4983230072969 + 3 ^ 40 * 6698834 * 2
def baseEnd_6698834 : Nat := 3439721666680749014867629

theorem tailTrace_6698834 : CollatzResearch.WordTrace tailWord_6698834 prefixEnd_6698834 3439721666680749014867629 := by
  unfold tailWord_6698834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61081637053318990652065889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162884365475517308405509037 61081637053318990652065889)
  ·
    refine ⟨45811227789989242989049417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61081637053318990652065889 45811227789989242989049417)
    ·
      refine ⟨34358420842491932241787063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45811227789989242989049417 34358420842491932241787063)
      ·
        refine ⟨51537631263737898362680595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34358420842491932241787063 51537631263737898362680595)
        ·
          refine ⟨77306446895606847544020893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51537631263737898362680595 77306446895606847544020893)
          ·
            refine ⟨28989917585852567829007835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77306446895606847544020893 28989917585852567829007835)
            ·
              refine ⟨43484876378778851743511753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28989917585852567829007835 43484876378778851743511753)
              ·
                refine ⟨32613657284084138807633815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43484876378778851743511753 32613657284084138807633815)
                ·
                  refine ⟨48920485926126208211450723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32613657284084138807633815 48920485926126208211450723)
                  ·
                    refine ⟨73380728889189312317176085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48920485926126208211450723 73380728889189312317176085)
                    ·
                      refine ⟨3439721666680749014867629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73380728889189312317176085 3439721666680749014867629)
                      ·
                        rfl

theorem cell23_6698834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_6698834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698834 prefixEnd_6698834 := by exact prefixLift 6698834
  have htrace : WordTrace (prefixWord ++ tailWord_6698834) baseStart_6698834 baseEnd_6698834 := by
    simpa [prefixWord, tailWord_6698834, baseEnd_6698834] using wordTrace_append hprefix tailTrace_6698834
  have hstable : (prefixWord ++ tailWord_6698834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698834).length < 2 ^ (prefixWord ++ tailWord_6698834).sum := by decide
  have hdescent : baseEnd_6698834 < baseStart_6698834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698848 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_6698848 : Nat := 118140960795 + 6698848 * 2 ^ 59
def prefixEnd_6698848 : Nat := 4983230072969 + 3 ^ 40 * 6698848 * 2
def baseEnd_6698848 : Nat := 1146576285136637320030855

theorem tailTrace_6698848 : CollatzResearch.WordTrace tailWord_6698848 prefixEnd_6698848 1146576285136637320030855 := by
  unfold tailWord_6698848
  simp only [CollatzResearch.WordTrace]
  refine ⟨122163529417612621499636599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162884705890150161999515465 122163529417612621499636599)
  ·
    refine ⟨183245294126418932249454899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122163529417612621499636599 183245294126418932249454899)
    ·
      refine ⟨274867941189628398374182349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183245294126418932249454899 274867941189628398374182349)
      ·
        refine ⟨103075477946110649390318381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274867941189628398374182349 103075477946110649390318381)
        ·
          refine ⟨38653304229791493521369393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103075477946110649390318381 38653304229791493521369393)
          ·
            refine ⟨28989978172343620141027045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38653304229791493521369393 28989978172343620141027045)
            ·
              refine ⟨5435620907314428776442571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28989978172343620141027045 5435620907314428776442571)
              ·
                refine ⟨8153431360971643164663857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435620907314428776442571 8153431360971643164663857)
                ·
                  refine ⟨6115073520728732373497893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8153431360971643164663857 6115073520728732373497893)
                  ·
                    refine ⟨1146576285136637320030855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115073520728732373497893 1146576285136637320030855)
                    ·
                      rfl

theorem cell23_6698848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_6698848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698848 prefixEnd_6698848 := by exact prefixLift 6698848
  have htrace : WordTrace (prefixWord ++ tailWord_6698848) baseStart_6698848 baseEnd_6698848 := by
    simpa [prefixWord, tailWord_6698848, baseEnd_6698848] using wordTrace_append hprefix tailTrace_6698848
  have hstable : (prefixWord ++ tailWord_6698848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698848).length < 2 ^ (prefixWord ++ tailWord_6698848).sum := by decide
  have hdescent : baseEnd_6698848 < baseStart_6698848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698884 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6698884 : Nat := 118140960795 + 6698884 * 2 ^ 59
def prefixEnd_6698884 : Nat := 4983230072969 + 3 ^ 40 * 6698884 * 2
def baseEnd_6698884 : Nat := 3439747340713473819242399

theorem tailTrace_6698884 : CollatzResearch.WordTrace tailWord_6698884 prefixEnd_6698884 3439747340713473819242399 := by
  unfold tailWord_6698884
  simp only [CollatzResearch.WordTrace]
  refine ⟨122164185931547410573791853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162885581242063214098389137 122164185931547410573791853)
  ·
    refine ⟨45811569724330278965171945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122164185931547410573791853 45811569724330278965171945)
    ·
      refine ⟨34358677293247709223878959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45811569724330278965171945 34358677293247709223878959)
      ·
        refine ⟨51538015939871563835818439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34358677293247709223878959 51538015939871563835818439)
        ·
          refine ⟨77307023909807345753727659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51538015939871563835818439 77307023909807345753727659)
          ·
            refine ⟨115960535864711018630591489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77307023909807345753727659 115960535864711018630591489)
            ·
              refine ⟨86970401898533263972943617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115960535864711018630591489 86970401898533263972943617)
              ·
                refine ⟨65227801423899947979707713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86970401898533263972943617 65227801423899947979707713)
                ·
                  refine ⟨48920851067924960984780785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65227801423899947979707713 48920851067924960984780785)
                  ·
                    refine ⟨36690638300943720738585589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48920851067924960984780785 36690638300943720738585589)
                    ·
                      refine ⟨3439747340713473819242399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36690638300943720738585589 3439747340713473819242399)
                      ·
                        rfl

theorem cell23_6698884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6698884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698884 prefixEnd_6698884 := by exact prefixLift 6698884
  have htrace : WordTrace (prefixWord ++ tailWord_6698884) baseStart_6698884 baseEnd_6698884 := by
    simpa [prefixWord, tailWord_6698884, baseEnd_6698884] using wordTrace_append hprefix tailTrace_6698884
  have hstable : (prefixWord ++ tailWord_6698884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698884).length < 2 ^ (prefixWord ++ tailWord_6698884).sum := by decide
  have hdescent : baseEnd_6698884 < baseStart_6698884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698902 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6698902 : Nat := 118140960795 + 6698902 * 2 ^ 59
def prefixEnd_6698902 : Nat := 4983230072969 + 3 ^ 40 * 6698902 * 2
def baseEnd_6698902 : Nat := 3439756583365254748817317

theorem tailTrace_6698902 : CollatzResearch.WordTrace tailWord_6698902 prefixEnd_6698902 3439756583365254748817317 := by
  unfold tailWord_6698902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270564273564350638858685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162886018918019740147825973 15270564273564350638858685)
  ·
    refine ⟨5726461602586631489572007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15270564273564350638858685 5726461602586631489572007)
    ·
      refine ⟨8589692403879947234358011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726461602586631489572007 8589692403879947234358011)
      ·
        refine ⟨12884538605819920851537017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8589692403879947234358011 12884538605819920851537017)
        ·
          refine ⟨9663403954364940638652763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12884538605819920851537017 9663403954364940638652763)
          ·
            refine ⟨14495105931547410957979145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663403954364940638652763 14495105931547410957979145)
            ·
              refine ⟨10871329448660558218484359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495105931547410957979145 10871329448660558218484359)
              ·
                refine ⟨16306994172990837327726539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871329448660558218484359 16306994172990837327726539)
                ·
                  refine ⟨24460491259486255991589809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16306994172990837327726539 24460491259486255991589809)
                  ·
                    refine ⟨18345368444614691993692357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24460491259486255991589809 18345368444614691993692357)
                    ·
                      refine ⟨3439756583365254748817317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18345368444614691993692357 3439756583365254748817317)
                      ·
                        rfl

theorem cell23_6698902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6698902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698902 prefixEnd_6698902 := by exact prefixLift 6698902
  have htrace : WordTrace (prefixWord ++ tailWord_6698902) baseStart_6698902 baseEnd_6698902 := by
    simpa [prefixWord, tailWord_6698902, baseEnd_6698902] using wordTrace_append hprefix tailTrace_6698902
  have hstable : (prefixWord ++ tailWord_6698902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698902).length < 2 ^ (prefixWord ++ tailWord_6698902).sum := by decide
  have hdescent : baseEnd_6698902 < baseStart_6698902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698924 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6698924 : Nat := 118140960795 + 6698924 * 2 ^ 59
def prefixEnd_6698924 : Nat := 4983230072969 + 3 ^ 40 * 6698924 * 2
def baseEnd_6698924 : Nat := 3439767879939653662742215

theorem tailTrace_6698924 : CollatzResearch.WordTrace tailWord_6698924 prefixEnd_6698924 3439767879939653662742215 := by
  unfold tailWord_6698924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122164915391474953989519913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162886553855299938652693217 122164915391474953989519913)
  ·
    refine ⟨91623686543606215492139935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122164915391474953989519913 91623686543606215492139935)
    ·
      refine ⟨137435529815409323238209903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91623686543606215492139935 137435529815409323238209903)
      ·
        refine ⟨206153294723113984857314855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137435529815409323238209903 206153294723113984857314855)
        ·
          refine ⟨309229942084670977285972283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206153294723113984857314855 309229942084670977285972283)
          ·
            refine ⟨463844913127006465928958425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309229942084670977285972283 463844913127006465928958425)
            ·
              refine ⟨347883684845254849446718819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463844913127006465928958425 347883684845254849446718819)
              ·
                refine ⟨521825527267882274170078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347883684845254849446718819 521825527267882274170078229)
                ·
                  refine ⟨24460571590681981601722417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 521825527267882274170078229 24460571590681981601722417)
                  ·
                    refine ⟨18345428693011486201291813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24460571590681981601722417 18345428693011486201291813)
                    ·
                      refine ⟨3439767879939653662742215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18345428693011486201291813 3439767879939653662742215)
                      ·
                        rfl

theorem cell23_6698924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6698924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698924 prefixEnd_6698924 := by exact prefixLift 6698924
  have htrace : WordTrace (prefixWord ++ tailWord_6698924) baseStart_6698924 baseEnd_6698924 := by
    simpa [prefixWord, tailWord_6698924, baseEnd_6698924] using wordTrace_append hprefix tailTrace_6698924
  have hstable : (prefixWord ++ tailWord_6698924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698924).length < 2 ^ (prefixWord ++ tailWord_6698924).sum := by decide
  have hdescent : baseEnd_6698924 < baseStart_6698924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698926 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6698926 : Nat := 118140960795 + 6698926 * 2 ^ 59
def prefixEnd_6698926 : Nat := 4983230072969 + 3 ^ 40 * 6698926 * 2
def baseEnd_6698926 : Nat := 3439768906900962654917207

theorem tailTrace_6698926 : CollatzResearch.WordTrace tailWord_6698926 prefixEnd_6698926 3439768906900962654917207 := by
  unfold tailWord_6698926
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541237966117832790076579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162886602485961774880408421 30541237966117832790076579)
  ·
    refine ⟨45811856949176749185114869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541237966117832790076579 45811856949176749185114869)
    ·
      refine ⟨4294861588985320236104519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45811856949176749185114869 4294861588985320236104519)
      ·
        refine ⟨6442292383477980354156779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294861588985320236104519 6442292383477980354156779)
        ·
          refine ⟨9663438575216970531235169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442292383477980354156779 9663438575216970531235169)
          ·
            refine ⟨7247578931412727898426377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9663438575216970531235169 7247578931412727898426377)
            ·
              refine ⟨5435684198559545923819783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7247578931412727898426377 5435684198559545923819783)
              ·
                refine ⟨8153526297839318885729675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435684198559545923819783 8153526297839318885729675)
                ·
                  refine ⟨12230289446758978328594513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153526297839318885729675 12230289446758978328594513)
                  ·
                    refine ⟨9172717085069233746445885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12230289446758978328594513 9172717085069233746445885)
                    ·
                      refine ⟨3439768906900962654917207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9172717085069233746445885 3439768906900962654917207)
                      ·
                        rfl

theorem cell23_6698926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6698926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698926 prefixEnd_6698926 := by exact prefixLift 6698926
  have htrace : WordTrace (prefixWord ++ tailWord_6698926) baseStart_6698926 baseEnd_6698926 := by
    simpa [prefixWord, tailWord_6698926, baseEnd_6698926] using wordTrace_append hprefix tailTrace_6698926
  have hstable : (prefixWord ++ tailWord_6698926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698926).length < 2 ^ (prefixWord ++ tailWord_6698926).sum := by decide
  have hdescent : baseEnd_6698926 < baseStart_6698926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698941 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6698941 : Nat := 118140960795 + 6698941 * 2 ^ 59
def prefixEnd_6698941 : Nat := 4983230072969 + 3 ^ 40 * 6698941 * 2
def baseEnd_6698941 : Nat := 3439776609110780096229637

theorem tailTrace_6698941 : CollatzResearch.WordTrace tailWord_6698941 prefixEnd_6698941 3439776609110780096229637 := by
  unfold tailWord_6698941
  simp only [CollatzResearch.WordTrace]
  refine ⟨244330450823888319882408677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162886967215925546588272451 244330450823888319882408677)
  ·
    refine ⟨45811959529479059977951627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244330450823888319882408677 45811959529479059977951627)
    ·
      refine ⟨68717939294218589966927441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45811959529479059977951627 68717939294218589966927441)
      ·
        refine ⟨51538454470663942475195581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68717939294218589966927441 51538454470663942475195581)
        ·
          refine ⟨19326920426498978428198343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51538454470663942475195581 19326920426498978428198343)
          ·
            refine ⟨28990380639748467642297515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326920426498978428198343 28990380639748467642297515)
            ·
              refine ⟨43485570959622701463446273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28990380639748467642297515 43485570959622701463446273)
              ·
                refine ⟨32614178219717026097584705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43485570959622701463446273 32614178219717026097584705)
                ·
                  refine ⟨24460633664787769573188529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32614178219717026097584705 24460633664787769573188529)
                  ·
                    refine ⟨18345475248590827179891397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24460633664787769573188529 18345475248590827179891397)
                    ·
                      refine ⟨3439776609110780096229637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18345475248590827179891397 3439776609110780096229637)
                      ·
                        rfl

theorem cell23_6698941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6698941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698941 prefixEnd_6698941 := by exact prefixLift 6698941
  have htrace : WordTrace (prefixWord ++ tailWord_6698941) baseStart_6698941 baseEnd_6698941 := by
    simpa [prefixWord, tailWord_6698941, baseEnd_6698941] using wordTrace_append hprefix tailTrace_6698941
  have hstable : (prefixWord ++ tailWord_6698941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698941).length < 2 ^ (prefixWord ++ tailWord_6698941).sum := by decide
  have hdescent : baseEnd_6698941 < baseStart_6698941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698962 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6698962 : Nat := 118140960795 + 6698962 * 2 ^ 59
def prefixEnd_6698962 : Nat := 4983230072969 + 3 ^ 40 * 6698962 * 2
def baseEnd_6698962 : Nat := 3439787392204524514067041

theorem tailTrace_6698962 : CollatzResearch.WordTrace tailWord_6698962 prefixEnd_6698962 3439787392204524514067041 := by
  unfold tailWord_6698962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61082804189203060117230785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162887477837874826979282093 61082804189203060117230785)
  ·
    refine ⟨45812103141902295087923089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61082804189203060117230785 45812103141902295087923089)
    ·
      refine ⟨34359077356426721315942317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45812103141902295087923089 34359077356426721315942317)
      ·
        refine ⟨12884654008660020493478369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34359077356426721315942317 12884654008660020493478369)
        ·
          refine ⟨9663490506495015370108777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12884654008660020493478369 9663490506495015370108777)
          ·
            refine ⟨7247617879871261527581583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9663490506495015370108777 7247617879871261527581583)
            ·
              refine ⟨10871426819806892291372375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247617879871261527581583 10871426819806892291372375)
              ·
                refine ⟨16307140229710338437058563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871426819806892291372375 16307140229710338437058563)
                ·
                  refine ⟨24460710344565507655587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16307140229710338437058563 24460710344565507655587845)
                  ·
                    refine ⟨4586383189606032685422721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24460710344565507655587845 4586383189606032685422721)
                    ·
                      refine ⟨3439787392204524514067041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586383189606032685422721 3439787392204524514067041)
                      ·
                        rfl

theorem cell23_6698962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6698962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698962 prefixEnd_6698962 := by exact prefixLift 6698962
  have htrace : WordTrace (prefixWord ++ tailWord_6698962) baseStart_6698962 baseEnd_6698962 := by
    simpa [prefixWord, tailWord_6698962, baseEnd_6698962] using wordTrace_append hprefix tailTrace_6698962
  have hstable : (prefixWord ++ tailWord_6698962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698962).length < 2 ^ (prefixWord ++ tailWord_6698962).sum := by decide
  have hdescent : baseEnd_6698962 < baseStart_6698962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699001 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6699001 : Nat := 118140960795 + 6699001 * 2 ^ 59
def prefixEnd_6699001 : Nat := 4983230072969 + 3 ^ 40 * 6699001 * 2
def baseEnd_6699001 : Nat := 3439807417950049861479361

theorem tailTrace_6699001 : CollatzResearch.WordTrace tailWord_6699001 prefixEnd_6699001 3439807417950049861479361 := by
  unfold tailWord_6699001
  simp only [CollatzResearch.WordTrace]
  refine ⟨244332639203670950129592857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162888426135780633419728571 244332639203670950129592857)
  ·
    refine ⟨183249479402753212597194643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244332639203670950129592857 183249479402753212597194643)
    ·
      refine ⟨274874219104129818895791965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183249479402753212597194643 274874219104129818895791965)
      ·
        refine ⟨103077832164048682085921987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274874219104129818895791965 103077832164048682085921987)
        ·
          refine ⟨154616748246073023128882981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103077832164048682085921987 154616748246073023128882981)
          ·
            refine ⟨28990640296138691836665559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154616748246073023128882981 28990640296138691836665559)
            ·
              refine ⟨43485960444208037754998339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28990640296138691836665559 43485960444208037754998339)
              ·
                refine ⟨65228940666312056632497509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43485960444208037754998339 65228940666312056632497509)
                ·
                  refine ⟨12230426374933510618593283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65228940666312056632497509 12230426374933510618593283)
                  ·
                    refine ⟨18345639562400265927889925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12230426374933510618593283 18345639562400265927889925)
                    ·
                      refine ⟨3439807417950049861479361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18345639562400265927889925 3439807417950049861479361)
                      ·
                        rfl

theorem cell23_6699001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6699001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699001 prefixEnd_6699001 := by exact prefixLift 6699001
  have htrace : WordTrace (prefixWord ++ tailWord_6699001) baseStart_6699001 baseEnd_6699001 := by
    simpa [prefixWord, tailWord_6699001, baseEnd_6699001] using wordTrace_append hprefix tailTrace_6699001
  have hstable : (prefixWord ++ tailWord_6699001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699001).length < 2 ^ (prefixWord ++ tailWord_6699001).sum := by decide
  have hdescent : baseEnd_6699001 < baseStart_6699001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699058 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_6699058 : Nat := 118140960795 + 6699058 * 2 ^ 59
def prefixEnd_6699058 : Nat := 4983230072969 + 3 ^ 40 * 6699058 * 2
def baseEnd_6699058 : Nat := 382204076260817348718511

theorem tailTrace_6699058 : CollatzResearch.WordTrace tailWord_6699058 prefixEnd_6699058 382204076260817348718511 := by
  unfold tailWord_6699058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61083679541116112216104457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162889812109642965909611885 61083679541116112216104457)
  ·
    refine ⟨45812759655837084162078343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61083679541116112216104457 45812759655837084162078343)
    ·
      refine ⟨68719139483755626243117515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45812759655837084162078343 68719139483755626243117515)
      ·
        refine ⟨103078709225633439364676273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68719139483755626243117515 103078709225633439364676273)
        ·
          refine ⟨77309031919225079523507205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103078709225633439364676273 77309031919225079523507205)
          ·
            refine ⟨14495443484854702410657601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77309031919225079523507205 14495443484854702410657601)
            ·
              refine ⟨10871582613641026807993201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495443484854702410657601 10871582613641026807993201)
              ·
                refine ⟨8153686960230770105994901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871582613641026807993201 8153686960230770105994901)
                ·
                  refine ⟨382204076260817348718511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8153686960230770105994901 382204076260817348718511)
                  ·
                    rfl

theorem cell23_6699058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_6699058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699058 prefixEnd_6699058 := by exact prefixLift 6699058
  have htrace : WordTrace (prefixWord ++ tailWord_6699058) baseStart_6699058 baseEnd_6699058 := by
    simpa [prefixWord, tailWord_6699058, baseEnd_6699058] using wordTrace_append hprefix tailTrace_6699058
  have hstable : (prefixWord ++ tailWord_6699058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699058).length < 2 ^ (prefixWord ++ tailWord_6699058).sum := by decide
  have hdescent : baseEnd_6699058 < baseStart_6699058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699062 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6699062 : Nat := 118140960795 + 6699062 * 2 ^ 59
def prefixEnd_6699062 : Nat := 4983230072969 + 3 ^ 40 * 6699062 * 2
def baseEnd_6699062 : Nat := 1146612913423324707605527

theorem tailTrace_6699062 : CollatzResearch.WordTrace tailWord_6699062 prefixEnd_6699062 1146612913423324707605527 := by
  unfold tailWord_6699062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270929003528122346722715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162889909370966638365042293 15270929003528122346722715)
  ·
    refine ⟨22906393505292183520084073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15270929003528122346722715 22906393505292183520084073)
    ·
      refine ⟨17179795128969137640063055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22906393505292183520084073 17179795128969137640063055)
      ·
        refine ⟨25769692693453706460094583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179795128969137640063055 25769692693453706460094583)
        ·
          refine ⟨38654539040180559690141875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25769692693453706460094583 38654539040180559690141875)
          ·
            refine ⟨57981808560270839535212813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38654539040180559690141875 57981808560270839535212813)
            ·
              refine ⟨21743178210101564825704805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57981808560270839535212813 21743178210101564825704805)
              ·
                refine ⟨4076845914394043404819651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21743178210101564825704805 4076845914394043404819651)
                ·
                  refine ⟨6115268871591065107229477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076845914394043404819651 6115268871591065107229477)
                  ·
                    refine ⟨1146612913423324707605527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115268871591065107229477 1146612913423324707605527)
                    ·
                      rfl

theorem cell23_6699062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6699062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699062 prefixEnd_6699062 := by exact prefixLift 6699062
  have htrace : WordTrace (prefixWord ++ tailWord_6699062) baseStart_6699062 baseEnd_6699062 := by
    simpa [prefixWord, tailWord_6699062, baseEnd_6699062] using wordTrace_append hprefix tailTrace_6699062
  have hstable : (prefixWord ++ tailWord_6699062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699062).length < 2 ^ (prefixWord ++ tailWord_6699062).sum := by decide
  have hdescent : baseEnd_6699062 < baseStart_6699062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699071 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 3, 5]
def baseStart_6699071 : Nat := 118140960795 + 6699071 * 2 ^ 59
def prefixEnd_6699071 : Nat := 4983230072969 + 3 ^ 40 * 6699071 * 2
def baseEnd_6699071 : Nat := 1146614453865288195868013

theorem tailTrace_6699071 : CollatzResearch.WordTrace tailWord_6699071 prefixEnd_6699071 1146614453865288195868013 := by
  unfold tailWord_6699071
  simp only [CollatzResearch.WordTrace]
  refine ⟨244335192313417352084641067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162890128208944901389760711 244335192313417352084641067)
  ·
    refine ⟨366502788470126028126961601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244335192313417352084641067 366502788470126028126961601)
    ·
      refine ⟨274877091352594521095221201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366502788470126028126961601 274877091352594521095221201)
      ·
        refine ⟨206157818514445890821415901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274877091352594521095221201 206157818514445890821415901)
        ·
          refine ⟨77309181942917209058030963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206157818514445890821415901 77309181942917209058030963)
          ·
            refine ⟨115963772914375813587046445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77309181942917209058030963 115963772914375813587046445)
            ·
              refine ⟨43486414842890930095142417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115963772914375813587046445 43486414842890930095142417)
              ·
                refine ⟨32614811132168197571356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43486414842890930095142417 32614811132168197571356813)
                ·
                  refine ⟨12230554174563074089258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32614811132168197571356813 12230554174563074089258805)
                  ·
                    refine ⟨1146614453865288195868013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12230554174563074089258805 1146614453865288195868013)
                    ·
                      rfl

theorem cell23_6699071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_6699071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699071 prefixEnd_6699071 := by exact prefixLift 6699071
  have htrace : WordTrace (prefixWord ++ tailWord_6699071) baseStart_6699071 baseEnd_6699071 := by
    simpa [prefixWord, tailWord_6699071, baseEnd_6699071] using wordTrace_append hprefix tailTrace_6699071
  have hstable : (prefixWord ++ tailWord_6699071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699071).length < 2 ^ (prefixWord ++ tailWord_6699071).sum := by decide
  have hdescent : baseEnd_6699071 < baseStart_6699071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699091 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4]
def baseStart_6699091 : Nat := 118140960795 + 6699091 * 2 ^ 59
def prefixEnd_6699091 : Nat := 4983230072969 + 3 ^ 40 * 6699091 * 2
def baseEnd_6699091 : Nat := 3439853631208954509353947

theorem tailTrace_6699091 : CollatzResearch.WordTrace tailWord_6699091 prefixEnd_6699091 3439853631208954509353947 := by
  unfold tailWord_6699091
  simp only [CollatzResearch.WordTrace]
  refine ⟨244335921773344895500369127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162890614515563263666912751 244335921773344895500369127)
  ·
    refine ⟨366503882660017343250553691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244335921773344895500369127 366503882660017343250553691)
    ·
      refine ⟨549755823990026014875830537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366503882660017343250553691 549755823990026014875830537)
      ·
        refine ⟨412316867992519511156872903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549755823990026014875830537 412316867992519511156872903)
        ·
          refine ⟨618475301988779266735309355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412316867992519511156872903 618475301988779266735309355)
          ·
            refine ⟨927712952983168900102964033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618475301988779266735309355 927712952983168900102964033)
            ·
              refine ⟨695784714737376675077223025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927712952983168900102964033 695784714737376675077223025)
              ·
                refine ⟨521838536053032506307917269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695784714737376675077223025 521838536053032506307917269)
                ·
                  refine ⟨12230590688742949366591811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 521838536053032506307917269 12230590688742949366591811)
                  ·
                    refine ⟨18345886033114424049887717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12230590688742949366591811 18345886033114424049887717)
                    ·
                      refine ⟨3439853631208954509353947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18345886033114424049887717 3439853631208954509353947)
                      ·
                        rfl

theorem cell23_6699091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_6699091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699091 prefixEnd_6699091 := by exact prefixLift 6699091
  have htrace : WordTrace (prefixWord ++ tailWord_6699091) baseStart_6699091 baseEnd_6699091 := by
    simpa [prefixWord, tailWord_6699091, baseEnd_6699091] using wordTrace_append hprefix tailTrace_6699091
  have hstable : (prefixWord ++ tailWord_6699091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699091).length < 2 ^ (prefixWord ++ tailWord_6699091).sum := by decide
  have hdescent : baseEnd_6699091 < baseStart_6699091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699095 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_6699095 : Nat := 118140960795 + 6699095 * 2 ^ 59
def prefixEnd_6699095 : Nat := 4983230072969 + 3 ^ 40 * 6699095 * 2
def baseEnd_6699095 : Nat := 3439855685131572493703929

theorem tailTrace_6699095 : CollatzResearch.WordTrace tailWord_6699095 prefixEnd_6699095 3439855685131572493703929 := by
  unfold tailWord_6699095
  simp only [CollatzResearch.WordTrace]
  refine ⟨244336067665330404183514739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162890711776886936122343159 244336067665330404183514739)
  ·
    refine ⟨366504101497995606275272109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244336067665330404183514739 366504101497995606275272109)
    ·
      refine ⟨137439038061748352353227041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366504101497995606275272109 137439038061748352353227041)
      ·
        refine ⟨103079278546311264264920281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137439038061748352353227041 103079278546311264264920281)
        ·
          refine ⟨77309458909733448198690211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103079278546311264264920281 77309458909733448198690211)
          ·
            refine ⟨115964188364600172298035317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77309458909733448198690211 115964188364600172298035317)
            ·
              refine ⟨10871642659181266152940811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115964188364600172298035317 10871642659181266152940811)
              ·
                refine ⟨16307463988771899229411217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871642659181266152940811 16307463988771899229411217)
                ·
                  refine ⟨12230597991578924422058413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16307463988771899229411217 12230597991578924422058413)
                  ·
                    refine ⟨4586474246842096658271905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12230597991578924422058413 4586474246842096658271905)
                    ·
                      refine ⟨3439855685131572493703929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586474246842096658271905 3439855685131572493703929)
                      ·
                        rfl

theorem cell23_6699095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_6699095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699095 prefixEnd_6699095 := by exact prefixLift 6699095
  have htrace : WordTrace (prefixWord ++ tailWord_6699095) baseStart_6699095 baseEnd_6699095 := by
    simpa [prefixWord, tailWord_6699095, baseEnd_6699095] using wordTrace_append hprefix tailTrace_6699095
  have hstable : (prefixWord ++ tailWord_6699095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699095).length < 2 ^ (prefixWord ++ tailWord_6699095).sum := by decide
  have hdescent : baseEnd_6699095 < baseStart_6699095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699121 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_6699121 : Nat := 118140960795 + 6699121 * 2 ^ 59
def prefixEnd_6699121 : Nat := 4983230072969 + 3 ^ 40 * 6699121 * 2
def baseEnd_6699121 : Nat := 3439869035628589391978809

theorem tailTrace_6699121 : CollatzResearch.WordTrace tailWord_6699121 prefixEnd_6699121 3439869035628589391978809 := by
  unfold tailWord_6699121
  simp only [CollatzResearch.WordTrace]
  refine ⟨244337015963236210623961217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162891343975490807082640811 244337015963236210623961217)
  ·
    refine ⟨183252761972427157967970913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244337015963236210623961217 183252761972427157967970913)
    ·
      refine ⟨137439571479320368475978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183252761972427157967970913 137439571479320368475978185)
      ·
        refine ⟨103079678609490276356983639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137439571479320368475978185 103079678609490276356983639)
        ·
          refine ⟨154619517914235414535475459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103079678609490276356983639 154619517914235414535475459)
          ·
            refine ⟨231929276871353121803213189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154619517914235414535475459 231929276871353121803213189)
            ·
              refine ⟨43486739413378710338102473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231929276871353121803213189 43486739413378710338102473)
              ·
                refine ⟨32615054560034032753576855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43486739413378710338102473 32615054560034032753576855)
                ·
                  refine ⟨48922581840051049130365283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32615054560034032753576855 48922581840051049130365283)
                  ·
                    refine ⟨73383872760076573695547925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48922581840051049130365283 73383872760076573695547925)
                    ·
                      refine ⟨3439869035628589391978809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73383872760076573695547925 3439869035628589391978809)
                      ·
                        rfl

theorem cell23_6699121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_6699121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699121 prefixEnd_6699121 := by exact prefixLift 6699121
  have htrace : WordTrace (prefixWord ++ tailWord_6699121) baseStart_6699121 baseEnd_6699121 := by
    simpa [prefixWord, tailWord_6699121, baseEnd_6699121] using wordTrace_append hprefix tailTrace_6699121
  have hstable : (prefixWord ++ tailWord_6699121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699121).length < 2 ^ (prefixWord ++ tailWord_6699121).sum := by decide
  have hdescent : baseEnd_6699121 < baseStart_6699121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699145 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_6699145 : Nat := 118140960795 + 6699145 * 2 ^ 59
def prefixEnd_6699145 : Nat := 4983230072969 + 3 ^ 40 * 6699145 * 2
def baseEnd_6699145 : Nat := 3439881359164297298078699

theorem tailTrace_6699145 : CollatzResearch.WordTrace tailWord_6699145 prefixEnd_6699145 3439881359164297298078699 := by
  unfold tailWord_6699145
  simp only [CollatzResearch.WordTrace]
  refine ⟨244337891315149262722834889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162891927543432841815223259 244337891315149262722834889)
  ·
    refine ⟨183253418486361947042126167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244337891315149262722834889 183253418486361947042126167)
    ·
      refine ⟨274880127729542920563189251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183253418486361947042126167 274880127729542920563189251)
      ·
        refine ⟨412320191594314380844783877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274880127729542920563189251 412320191594314380844783877)
        ·
          refine ⟨77310035923933946408396977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412320191594314380844783877 77310035923933946408396977)
          ·
            refine ⟨57982526942950459806297733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77310035923933946408396977 57982526942950459806297733)
            ·
              refine ⟨10871723801803211213680825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57982526942950459806297733 10871723801803211213680825)
              ·
                refine ⟨8153792851352408410260619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871723801803211213680825 8153792851352408410260619)
                ·
                  refine ⟨12230689277028612615390929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153792851352408410260619 12230689277028612615390929)
                  ·
                    refine ⟨9173016957771459461543197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12230689277028612615390929 9173016957771459461543197)
                    ·
                      refine ⟨3439881359164297298078699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9173016957771459461543197 3439881359164297298078699)
                      ·
                        rfl

theorem cell23_6699145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_6699145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699145 prefixEnd_6699145 := by exact prefixLift 6699145
  have htrace : WordTrace (prefixWord ++ tailWord_6699145) baseStart_6699145 baseEnd_6699145 := by
    simpa [prefixWord, tailWord_6699145, baseEnd_6699145] using wordTrace_append hprefix tailTrace_6699145
  have hstable : (prefixWord ++ tailWord_6699145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699145).length < 2 ^ (prefixWord ++ tailWord_6699145).sum := by decide
  have hdescent : baseEnd_6699145 < baseStart_6699145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699182 : List Nat := [4, 1, 4, 2, 1, 1, 2, 8]
def baseStart_6699182 : Nat := 118140960795 + 6699182 * 2 ^ 59
def prefixEnd_6699182 : Nat := 4983230072969 + 3 ^ 40 * 6699182 * 2
def baseEnd_6699182 : Nat := 127403716961056061233927

theorem tailTrace_6699182 : CollatzResearch.WordTrace tailWord_6699182 prefixEnd_6699182 127403716961056061233927 := by
  unfold tailWord_6699182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30542405102001902255241475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162892827210676812027954533 30542405102001902255241475)
  ·
    refine ⟨45813607653002853382862213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30542405102001902255241475 45813607653002853382862213)
    ·
      refine ⟨8590051434938035009286665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45813607653002853382862213 8590051434938035009286665)
      ·
        refine ⟨6442538576203526256964999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8590051434938035009286665 6442538576203526256964999)
        ·
          refine ⟨9663807864305289385447499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442538576203526256964999 9663807864305289385447499)
          ·
            refine ⟨14495711796457934078171249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663807864305289385447499 14495711796457934078171249)
            ·
              refine ⟨10871783847343450558628437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495711796457934078171249 10871783847343450558628437)
              ·
                refine ⟨127403716961056061233927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10871783847343450558628437 127403716961056061233927)
                ·
                  rfl

theorem cell23_6699182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_6699182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699182 prefixEnd_6699182 := by exact prefixLift 6699182
  have htrace : WordTrace (prefixWord ++ tailWord_6699182) baseStart_6699182 baseEnd_6699182 := by
    simpa [prefixWord, tailWord_6699182, baseEnd_6699182] using wordTrace_append hprefix tailTrace_6699182
  have hstable : (prefixWord ++ tailWord_6699182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699182).length < 2 ^ (prefixWord ++ tailWord_6699182).sum := by decide
  have hdescent : baseEnd_6699182 < baseStart_6699182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699215 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 4, 2]
def baseStart_6699215 : Nat := 118140960795 + 6699215 * 2 ^ 59
def prefixEnd_6699215 : Nat := 4983230072969 + 3 ^ 40 * 6699215 * 2
def baseEnd_6699215 : Nat := 3439917302810112024203377

theorem tailTrace_6699215 : CollatzResearch.WordTrace tailWord_6699215 prefixEnd_6699215 3439917302810112024203377 := by
  unfold tailWord_6699215
  simp only [CollatzResearch.WordTrace]
  refine ⟨244340444424895664677883099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162893629616597109785255399 244340444424895664677883099)
  ·
    refine ⟨366510666637343497016824649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244340444424895664677883099 366510666637343497016824649)
    ·
      refine ⟨274882999978007622762618487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366510666637343497016824649 274882999978007622762618487)
      ·
        refine ⟨412324499967011434143927731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274882999978007622762618487 412324499967011434143927731)
        ·
          refine ⟨618486749950517151215891597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412324499967011434143927731 618486749950517151215891597)
          ·
            refine ⟨231932531231443931705959349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618486749950517151215891597 231932531231443931705959349)
            ·
              refine ⟨21743674802947868597433689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231932531231443931705959349 21743674802947868597433689)
              ·
                refine ⟨16307756102210901448075267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21743674802947868597433689 16307756102210901448075267)
                ·
                  refine ⟨24461634153316352172112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16307756102210901448075267 24461634153316352172112901)
                  ·
                    refine ⟨4586556403746816032271169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24461634153316352172112901 4586556403746816032271169)
                    ·
                      refine ⟨3439917302810112024203377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586556403746816032271169 3439917302810112024203377)
                      ·
                        rfl

theorem cell23_6699215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4, 2].length) (baseStart_6699215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699215 prefixEnd_6699215 := by exact prefixLift 6699215
  have htrace : WordTrace (prefixWord ++ tailWord_6699215) baseStart_6699215 baseEnd_6699215 := by
    simpa [prefixWord, tailWord_6699215, baseEnd_6699215] using wordTrace_append hprefix tailTrace_6699215
  have hstable : (prefixWord ++ tailWord_6699215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699215).length < 2 ^ (prefixWord ++ tailWord_6699215).sum := by decide
  have hdescent : baseEnd_6699215 < baseStart_6699215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699272 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 5]
def baseStart_6699272 : Nat := 118140960795 + 6699272 * 2 ^ 59
def prefixEnd_6699272 : Nat := 4983230072969 + 3 ^ 40 * 6699272 * 2
def baseEnd_6699272 : Nat := 382216285689713144576735

theorem tailTrace_6699272 : CollatzResearch.WordTrace tailWord_6699272 prefixEnd_6699272 382216285689713144576735 := by
  unfold tailWord_6699272
  simp only [CollatzResearch.WordTrace]
  refine ⟨122171261692844581706354035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162895015590459442275138713 122171261692844581706354035)
  ·
    refine ⟨183256892539266872559531053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122171261692844581706354035 183256892539266872559531053)
    ·
      refine ⟨68721334702225077209824145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183256892539266872559531053 68721334702225077209824145)
      ·
        refine ⟨51541001026668807907368109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68721334702225077209824145 51541001026668807907368109)
        ·
          refine ⟨19327875385000802965263041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51541001026668807907368109 19327875385000802965263041)
          ·
            refine ⟨14495906538750602223947281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19327875385000802965263041 14495906538750602223947281)
            ·
              refine ⟨10871929904062951667960461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495906538750602223947281 10871929904062951667960461)
              ·
                refine ⟨4076973714023606875485173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10871929904062951667960461 4076973714023606875485173)
                ·
                  refine ⟨382216285689713144576735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4076973714023606875485173 382216285689713144576735)
                  ·
                    rfl

theorem cell23_6699272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 5].length) (baseStart_6699272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699272 prefixEnd_6699272 := by exact prefixLift 6699272
  have htrace : WordTrace (prefixWord ++ tailWord_6699272) baseStart_6699272 baseEnd_6699272 := by
    simpa [prefixWord, tailWord_6699272, baseEnd_6699272] using wordTrace_append hprefix tailTrace_6699272
  have hstable : (prefixWord ++ tailWord_6699272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699272).length < 2 ^ (prefixWord ++ tailWord_6699272).sum := by decide
  have hdescent : baseEnd_6699272 < baseStart_6699272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699315 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 3, 4]
def baseStart_6699315 : Nat := 118140960795 + 6699315 * 2 ^ 59
def prefixEnd_6699315 : Nat := 4983230072969 + 3 ^ 40 * 6699315 * 2
def baseEnd_6699315 : Nat := 1146656216958520544317639

theorem tailTrace_6699315 : CollatzResearch.WordTrace tailWord_6699315 prefixEnd_6699315 1146656216958520544317639 := by
  unfold tailWord_6699315
  simp only [CollatzResearch.WordTrace]
  refine ⟨244344091724533381756523399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162896061149688921171015599 244344091724533381756523399)
  ·
    refine ⟨366516137586800072634785099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244344091724533381756523399 366516137586800072634785099)
    ·
      refine ⟨549774206380200108952177649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366516137586800072634785099 549774206380200108952177649)
      ·
        refine ⟨412330654785150081714133237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549774206380200108952177649 412330654785150081714133237)
        ·
          refine ⟨38655998886107820160699991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412330654785150081714133237 38655998886107820160699991)
          ·
            refine ⟨57983998329161730241049987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38655998886107820160699991 57983998329161730241049987)
            ·
              refine ⟨86975997493742595361574981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57983998329161730241049987 86975997493742595361574981)
              ·
                refine ⟨16307999530076736630295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86975997493742595361574981 16307999530076736630295309)
                ·
                  refine ⟨6115499823778776236360741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16307999530076736630295309 6115499823778776236360741)
                  ·
                    refine ⟨1146656216958520544317639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115499823778776236360741 1146656216958520544317639)
                    ·
                      rfl

theorem cell23_6699315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 4].length) (baseStart_6699315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699315 prefixEnd_6699315 := by exact prefixLift 6699315
  have htrace : WordTrace (prefixWord ++ tailWord_6699315) baseStart_6699315 baseEnd_6699315 := by
    simpa [prefixWord, tailWord_6699315, baseEnd_6699315] using wordTrace_append hprefix tailTrace_6699315
  have hstable : (prefixWord ++ tailWord_6699315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699315).length < 2 ^ (prefixWord ++ tailWord_6699315).sum := by decide
  have hdescent : baseEnd_6699315 < baseStart_6699315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699349 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_6699349 : Nat := 118140960795 + 6699349 * 2 ^ 59
def prefixEnd_6699349 : Nat := 4983230072969 + 3 ^ 40 * 6699349 * 2
def baseEnd_6699349 : Nat := 1146662036405938166642587

theorem tailTrace_6699349 : CollatzResearch.WordTrace tailWord_6699349 prefixEnd_6699349 1146662036405938166642587 := by
  unfold tailWord_6699349
  simp only [CollatzResearch.WordTrace]
  refine ⟨244345331806410205563261101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162896887870940137042174067 244345331806410205563261101)
  ·
    refine ⟨91629499427403827086222913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244345331806410205563261101 91629499427403827086222913)
    ·
      refine ⟨68722124570552870314667185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91629499427403827086222913 68722124570552870314667185)
      ·
        refine ⟨51541593427914652736000389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68722124570552870314667185 51541593427914652736000389)
        ·
          refine ⟨9664048767733997388000073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51541593427914652736000389 9664048767733997388000073)
          ·
            refine ⟨7248036575800498041000055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9664048767733997388000073 7248036575800498041000055)
            ·
              refine ⟨10872054863700747061500083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248036575800498041000055 10872054863700747061500083)
              ·
                refine ⟨16308082295551120592250125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872054863700747061500083 16308082295551120592250125)
                ·
                  refine ⟨6115530860831670222093797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16308082295551120592250125 6115530860831670222093797)
                  ·
                    refine ⟨1146662036405938166642587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115530860831670222093797 1146662036405938166642587)
                    ·
                      rfl

theorem cell23_6699349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_6699349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699349 prefixEnd_6699349 := by exact prefixLift 6699349
  have htrace : WordTrace (prefixWord ++ tailWord_6699349) baseStart_6699349 baseEnd_6699349 := by
    simpa [prefixWord, tailWord_6699349, baseEnd_6699349] using wordTrace_append hprefix tailTrace_6699349
  have hstable : (prefixWord ++ tailWord_6699349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699349).length < 2 ^ (prefixWord ++ tailWord_6699349).sum := by decide
  have hdescent : baseEnd_6699349 < baseStart_6699349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699362 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_6699362 : Nat := 118140960795 + 6699362 * 2 ^ 59
def prefixEnd_6699362 : Nat := 4983230072969 + 3 ^ 40 * 6699362 * 2
def baseEnd_6699362 : Nat := 382221420496258105451689

theorem tailTrace_6699362 : CollatzResearch.WordTrace tailWord_6699362 prefixEnd_6699362 382221420496258105451689 := by
  unfold tailWord_6699362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61086451488840777195871085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162897203970242072522322893 61086451488840777195871085)
  ·
    refine ⟨22907419308315291448451657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61086451488840777195871085 22907419308315291448451657)
    ·
      refine ⟨17180564481236468586338743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22907419308315291448451657 17180564481236468586338743)
      ·
        refine ⟨25770846721854702879508115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17180564481236468586338743 25770846721854702879508115)
        ·
          refine ⟨38656270082782054319262173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25770846721854702879508115 38656270082782054319262173)
          ·
            refine ⟨14496101281043270369723315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38656270082782054319262173 14496101281043270369723315)
            ·
              refine ⟨21744151921564905554584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14496101281043270369723315 21744151921564905554584973)
              ·
                refine ⟨8154056970586839582969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21744151921564905554584973 8154056970586839582969365)
                ·
                  refine ⟨382221420496258105451689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8154056970586839582969365 382221420496258105451689)
                  ·
                    rfl

theorem cell23_6699362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_6699362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699362 prefixEnd_6699362 := by exact prefixLift 6699362
  have htrace : WordTrace (prefixWord ++ tailWord_6699362) baseStart_6699362 baseEnd_6699362 := by
    simpa [prefixWord, tailWord_6699362, baseEnd_6699362] using wordTrace_append hprefix tailTrace_6699362
  have hstable : (prefixWord ++ tailWord_6699362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699362).length < 2 ^ (prefixWord ++ tailWord_6699362).sum := by decide
  have hdescent : baseEnd_6699362 < baseStart_6699362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699375 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 1, 5]
def baseStart_6699375 : Nat := 118140960795 + 6699375 * 2 ^ 59
def prefixEnd_6699375 : Nat := 4983230072969 + 3 ^ 40 * 6699375 * 2
def baseEnd_6699375 : Nat := 1146666486571610466067547

theorem tailTrace_6699375 : CollatzResearch.WordTrace tailWord_6699375 prefixEnd_6699375 1146666486571610466067547 := by
  unfold tailWord_6699375
  simp only [CollatzResearch.WordTrace]
  refine ⟨244346280104316012003707579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162897520069544008002471719 244346280104316012003707579)
  ·
    refine ⟨366519420156474018005561369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244346280104316012003707579 366519420156474018005561369)
    ·
      refine ⟨274889565117355513504171027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366519420156474018005561369 274889565117355513504171027)
      ·
        refine ⟨412334347676033270256256541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274889565117355513504171027 412334347676033270256256541)
        ·
          refine ⟨154625380378512476346096203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412334347676033270256256541 154625380378512476346096203)
          ·
            refine ⟨231938070567768714519144305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154625380378512476346096203 231938070567768714519144305)
            ·
              refine ⟨173953552925826535889358229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231938070567768714519144305 173953552925826535889358229)
              ·
                refine ⟨8154072793398118869813667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173953552925826535889358229 8154072793398118869813667)
                ·
                  refine ⟨12231109190097178304720501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154072793398118869813667 12231109190097178304720501)
                  ·
                    refine ⟨1146666486571610466067547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12231109190097178304720501 1146666486571610466067547)
                    ·
                      rfl

theorem cell23_6699375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_6699375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699375 prefixEnd_6699375 := by exact prefixLift 6699375
  have htrace : WordTrace (prefixWord ++ tailWord_6699375) baseStart_6699375 baseEnd_6699375 := by
    simpa [prefixWord, tailWord_6699375, baseEnd_6699375] using wordTrace_append hprefix tailTrace_6699375
  have hstable : (prefixWord ++ tailWord_6699375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699375).length < 2 ^ (prefixWord ++ tailWord_6699375).sum := by decide
  have hdescent : baseEnd_6699375 < baseStart_6699375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699415 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_6699415 : Nat := 118140960795 + 6699415 * 2 ^ 59
def prefixEnd_6699415 : Nat := 4983230072969 + 3 ^ 40 * 6699415 * 2
def baseEnd_6699415 : Nat := 3440019998941011241702457

theorem tailTrace_6699415 : CollatzResearch.WordTrace tailWord_6699415 prefixEnd_6699415 3440019998941011241702457 := by
  unfold tailWord_6699415
  simp only [CollatzResearch.WordTrace]
  refine ⟨244347739024171098835163699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162898492682780732556775799 244347739024171098835163699)
  ·
    refine ⟨366521608536256648252745549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244347739024171098835163699 366521608536256648252745549)
    ·
      refine ⟨137445603201096243094779581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366521608536256648252745549 137445603201096243094779581)
      ·
        refine ⟨51542101200411091160542343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137445603201096243094779581 51542101200411091160542343)
        ·
          refine ⟨77313151800616636740813515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51542101200411091160542343 77313151800616636740813515)
          ·
            refine ⟨115969727700924955111220273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77313151800616636740813515 115969727700924955111220273)
            ·
              refine ⟨86977295775693716333415205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115969727700924955111220273 86977295775693716333415205)
              ·
                refine ⟨16308242957942571812515351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86977295775693716333415205 16308242957942571812515351)
                ·
                  refine ⟨24462364436913857718773027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16308242957942571812515351 24462364436913857718773027)
                  ·
                    refine ⟨36693546655370786578159541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24462364436913857718773027 36693546655370786578159541)
                    ·
                      refine ⟨3440019998941011241702457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36693546655370786578159541 3440019998941011241702457)
                      ·
                        rfl

theorem cell23_6699415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_6699415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699415 prefixEnd_6699415 := by exact prefixLift 6699415
  have htrace : WordTrace (prefixWord ++ tailWord_6699415) baseStart_6699415 baseEnd_6699415 := by
    simpa [prefixWord, tailWord_6699415, baseEnd_6699415] using wordTrace_append hprefix tailTrace_6699415
  have hstable : (prefixWord ++ tailWord_6699415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699415).length < 2 ^ (prefixWord ++ tailWord_6699415).sum := by decide
  have hdescent : baseEnd_6699415 < baseStart_6699415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699429 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_6699429 : Nat := 118140960795 + 6699429 * 2 ^ 59
def prefixEnd_6699429 : Nat := 4983230072969 + 3 ^ 40 * 6699429 * 2
def baseEnd_6699429 : Nat := 3440027187670174186927393

theorem tailTrace_6699429 : CollatzResearch.WordTrace tailWord_6699429 prefixEnd_6699429 3440027187670174186927393 := by
  unfold tailWord_6699429
  simp only [CollatzResearch.WordTrace]
  refine ⟨244348249646120379226173341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162898833097413586150782227 244348249646120379226173341)
  ·
    refine ⟨91630593617295142209815003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244348249646120379226173341 91630593617295142209815003)
    ·
      refine ⟨137445890425942713314722505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91630593617295142209815003 137445890425942713314722505)
      ·
        refine ⟨103084417819457034986041879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137445890425942713314722505 103084417819457034986041879)
        ·
          refine ⟨154626626729185552479062819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103084417819457034986041879 154626626729185552479062819)
          ·
            refine ⟨231939940093778328718594229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154626626729185552479062819 231939940093778328718594229)
            ·
              refine ⟨21744369383791718317368209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231939940093778328718594229 21744369383791718317368209)
              ·
                refine ⟨16308277037843788738026157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21744369383791718317368209 16308277037843788738026157)
                ·
                  refine ⟨6115603889191420776759809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16308277037843788738026157 6115603889191420776759809)
                  ·
                    refine ⟨4586702916893565582569857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6115603889191420776759809 4586702916893565582569857)
                    ·
                      refine ⟨3440027187670174186927393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586702916893565582569857 3440027187670174186927393)
                      ·
                        rfl

theorem cell23_6699429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_6699429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699429 prefixEnd_6699429 := by exact prefixLift 6699429
  have htrace : WordTrace (prefixWord ++ tailWord_6699429) baseStart_6699429 baseEnd_6699429 := by
    simpa [prefixWord, tailWord_6699429, baseEnd_6699429] using wordTrace_append hprefix tailTrace_6699429
  have hstable : (prefixWord ++ tailWord_6699429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699429).length < 2 ^ (prefixWord ++ tailWord_6699429).sum := by decide
  have hdescent : baseEnd_6699429 < baseStart_6699429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699449 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6699449 : Nat := 118140960795 + 6699449 * 2 ^ 59
def prefixEnd_6699449 : Nat := 4983230072969 + 3 ^ 40 * 6699449 * 2
def baseEnd_6699449 : Nat := 3440037457283264108677301

theorem tailTrace_6699449 : CollatzResearch.WordTrace tailWord_6699449 prefixEnd_6699449 3440037457283264108677301 := by
  unfold tailWord_6699449
  simp only [CollatzResearch.WordTrace]
  refine ⟨244348979106047922641901401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162899319404031948427934267 244348979106047922641901401)
  ·
    refine ⟨183261734329535941981426051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244348979106047922641901401 183261734329535941981426051)
    ·
      refine ⟨274892601494303912972139077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183261734329535941981426051 274892601494303912972139077)
      ·
        refine ⟨51542362780181983682276077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274892601494303912972139077 51542362780181983682276077)
        ·
          refine ⟨19328386042568243880853529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51542362780181983682276077 19328386042568243880853529)
          ·
            refine ⟨14496289531926182910640147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19328386042568243880853529 14496289531926182910640147)
            ·
              refine ⟨21744434297889274365960221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14496289531926182910640147 21744434297889274365960221)
              ·
                refine ⟨8154162861708477887235083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21744434297889274365960221 8154162861708477887235083)
                ·
                  refine ⟨12231244292562716830852625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154162861708477887235083 12231244292562716830852625)
                  ·
                    refine ⟨9173433219422037623139469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12231244292562716830852625 9173433219422037623139469)
                    ·
                      refine ⟨3440037457283264108677301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9173433219422037623139469 3440037457283264108677301)
                      ·
                        rfl

theorem cell23_6699449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6699449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699449 prefixEnd_6699449 := by exact prefixLift 6699449
  have htrace : WordTrace (prefixWord ++ tailWord_6699449) baseStart_6699449 baseEnd_6699449 := by
    simpa [prefixWord, tailWord_6699449, baseEnd_6699449] using wordTrace_append hprefix tailTrace_6699449
  have hstable : (prefixWord ++ tailWord_6699449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699449).length < 2 ^ (prefixWord ++ tailWord_6699449).sum := by decide
  have hdescent : baseEnd_6699449 < baseStart_6699449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699519 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 4, 2, 2]
def baseStart_6699519 : Nat := 118140960795 + 6699519 * 2 ^ 59
def prefixEnd_6699519 : Nat := 4983230072969 + 3 ^ 40 * 6699519 * 2
def baseEnd_6699519 : Nat := 3440073400929078834801979

theorem tailTrace_6699519 : CollatzResearch.WordTrace tailWord_6699519 prefixEnd_6699519 3440073400929078834801979 := by
  unfold tailWord_6699519
  simp only [CollatzResearch.WordTrace]
  refine ⟨244351532215794324596949611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162901021477196216397966407 244351532215794324596949611)
  ·
    refine ⟨366527298323691486895424417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244351532215794324596949611 366527298323691486895424417)
    ·
      refine ⟨274895473742768615171568313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366527298323691486895424417 274895473742768615171568313)
      ·
        refine ⟨206171605307076461378676235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274895473742768615171568313 206171605307076461378676235)
        ·
          refine ⟨309257407960614692068014353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206171605307076461378676235 309257407960614692068014353)
          ·
            refine ⟨231943055970461019051010765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309257407960614692068014353 231943055970461019051010765)
            ·
              refine ⟨86978645988922882144129037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231943055970461019051010765 86978645988922882144129037)
              ·
                refine ⟨32616992245846080804048389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86978645988922882144129037 32616992245846080804048389)
                ·
                  refine ⟨6115686046096140150759073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32616992245846080804048389 6115686046096140150759073)
                  ·
                    refine ⟨4586764534572105113069305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6115686046096140150759073 4586764534572105113069305)
                    ·
                      refine ⟨3440073400929078834801979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586764534572105113069305 3440073400929078834801979)
                      ·
                        rfl

theorem cell23_6699519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_6699519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699519 prefixEnd_6699519 := by exact prefixLift 6699519
  have htrace : WordTrace (prefixWord ++ tailWord_6699519) baseStart_6699519 baseEnd_6699519 := by
    simpa [prefixWord, tailWord_6699519, baseEnd_6699519] using wordTrace_append hprefix tailTrace_6699519
  have hstable : (prefixWord ++ tailWord_6699519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699519).length < 2 ^ (prefixWord ++ tailWord_6699519).sum := by decide
  have hdescent : baseEnd_6699519 < baseStart_6699519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699540 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6699540 : Nat := 118140960795 + 6699540 * 2 ^ 59
def prefixEnd_6699540 : Nat := 4983230072969 + 3 ^ 40 * 6699540 * 2
def baseEnd_6699540 : Nat := 3440084184022823252639383

theorem tailTrace_6699540 : CollatzResearch.WordTrace tailWord_6699540 prefixEnd_6699540 3440084184022823252639383 := by
  unfold tailWord_6699540
  simp only [CollatzResearch.WordTrace]
  refine ⟨122176149074359122591732037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162901532099145496788976049 122176149074359122591732037)
  ·
    refine ⟨22908027951442335485949757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122176149074359122591732037 22908027951442335485949757)
    ·
      refine ⟨8590510481790875807231159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22908027951442335485949757 8590510481790875807231159)
      ·
        refine ⟨12885765722686313710846739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8590510481790875807231159 12885765722686313710846739)
        ·
          refine ⟨19328648584029470566270109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12885765722686313710846739 19328648584029470566270109)
          ·
            refine ⟨7248243219011051462351291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19328648584029470566270109 7248243219011051462351291)
            ·
              refine ⟨10872364828516577193526937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248243219011051462351291 10872364828516577193526937)
              ·
                refine ⟨8154273621387432895145203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10872364828516577193526937 8154273621387432895145203)
                ·
                  refine ⟨12231410432081149342717805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154273621387432895145203 12231410432081149342717805)
                  ·
                    refine ⟨4586778912030431003519177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12231410432081149342717805 4586778912030431003519177)
                    ·
                      refine ⟨3440084184022823252639383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586778912030431003519177 3440084184022823252639383)
                      ·
                        rfl

theorem cell23_6699540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6699540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699540 prefixEnd_6699540 := by exact prefixLift 6699540
  have htrace : WordTrace (prefixWord ++ tailWord_6699540) baseStart_6699540 baseEnd_6699540 := by
    simpa [prefixWord, tailWord_6699540, baseEnd_6699540] using wordTrace_append hprefix tailTrace_6699540
  have hstable : (prefixWord ++ tailWord_6699540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699540).length < 2 ^ (prefixWord ++ tailWord_6699540).sum := by decide
  have hdescent : baseEnd_6699540 < baseStart_6699540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699592 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6699592 : Nat := 118140960795 + 6699592 * 2 ^ 59
def prefixEnd_6699592 : Nat := 4983230072969 + 3 ^ 40 * 6699592 * 2
def baseEnd_6699592 : Nat := 3440110885016857049189143

theorem tailTrace_6699592 : CollatzResearch.WordTrace tailWord_6699592 prefixEnd_6699592 3440110885016857049189143 := by
  unfold tailWord_6699592
  simp only [CollatzResearch.WordTrace]
  refine ⟨122177097372264929032178515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162902796496353238709571353 122177097372264929032178515)
  ·
    refine ⟨183265646058397393548267773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122177097372264929032178515 183265646058397393548267773)
    ·
      refine ⟨68724617271899022580600415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183265646058397393548267773 68724617271899022580600415)
      ·
        refine ⟨103086925907848533870900623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68724617271899022580600415 103086925907848533870900623)
        ·
          refine ⟨154630388861772800806350935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103086925907848533870900623 154630388861772800806350935)
          ·
            refine ⟨231945583292659201209526403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154630388861772800806350935 231945583292659201209526403)
            ·
              refine ⟨347918374938988801814289605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231945583292659201209526403 347918374938988801814289605)
              ·
                refine ⟨65234695301060400340179301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347918374938988801814289605 65234695301060400340179301)
                ·
                  refine ⟨12231505368948825063783619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65234695301060400340179301 12231505368948825063783619)
                  ·
                    refine ⟨18347258053423237595675429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12231505368948825063783619 18347258053423237595675429)
                    ·
                      refine ⟨3440110885016857049189143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18347258053423237595675429 3440110885016857049189143)
                      ·
                        rfl

theorem cell23_6699592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6699592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699592 prefixEnd_6699592 := by exact prefixLift 6699592
  have htrace : WordTrace (prefixWord ++ tailWord_6699592) baseStart_6699592 baseEnd_6699592 := by
    simpa [prefixWord, tailWord_6699592, baseEnd_6699592] using wordTrace_append hprefix tailTrace_6699592
  have hstable : (prefixWord ++ tailWord_6699592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699592).length < 2 ^ (prefixWord ++ tailWord_6699592).sum := by decide
  have hdescent : baseEnd_6699592 < baseStart_6699592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699659 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 3]
def baseStart_6699659 : Nat := 118140960795 + 6699659 * 2 ^ 59
def prefixEnd_6699659 : Nat := 4983230072969 + 3 ^ 40 * 6699659 * 2
def baseEnd_6699659 : Nat := 3440145288220708287051335

theorem tailTrace_6699659 : CollatzResearch.WordTrace tailWord_6699659 prefixEnd_6699659 3440145288220708287051335 := by
  unfold tailWord_6699659
  simp only [CollatzResearch.WordTrace]
  refine ⟨244356638435287128507046031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162904425623524752338030687 244356638435287128507046031)
  ·
    refine ⟨366534957652930692760569047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244356638435287128507046031 366534957652930692760569047)
    ·
      refine ⟨549802436479396039140853571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366534957652930692760569047 549802436479396039140853571)
      ·
        refine ⟨824703654719094058711280357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549802436479396039140853571 824703654719094058711280357)
        ·
          refine ⟨154631935259830136008365067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 824703654719094058711280357 154631935259830136008365067)
          ·
            refine ⟨231947902889745204012547601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154631935259830136008365067 231947902889745204012547601)
            ·
              refine ⟨173960927167308903009410701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231947902889745204012547601 173960927167308903009410701)
              ·
                refine ⟨65235347687740838628529013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173960927167308903009410701 65235347687740838628529013)
                ·
                  refine ⟨6115813845725703621424595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65235347687740838628529013 6115813845725703621424595)
                  ·
                    refine ⟨9173720768588555432136893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115813845725703621424595 9173720768588555432136893)
                    ·
                      refine ⟨3440145288220708287051335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9173720768588555432136893 3440145288220708287051335)
                      ·
                        rfl

theorem cell23_6699659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 3].length) (baseStart_6699659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699659 prefixEnd_6699659 := by exact prefixLift 6699659
  have htrace : WordTrace (prefixWord ++ tailWord_6699659) baseStart_6699659 baseEnd_6699659 := by
    simpa [prefixWord, tailWord_6699659, baseEnd_6699659] using wordTrace_append hprefix tailTrace_6699659
  have hstable : (prefixWord ++ tailWord_6699659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699659).length < 2 ^ (prefixWord ++ tailWord_6699659).sum := by decide
  have hdescent : baseEnd_6699659 < baseStart_6699659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699687 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6699687 : Nat := 118140960795 + 6699687 * 2 ^ 59
def prefixEnd_6699687 : Nat := 4983230072969 + 3 ^ 40 * 6699687 * 2
def baseEnd_6699687 : Nat := 1146719888559678059167069

theorem tailTrace_6699687 : CollatzResearch.WordTrace tailWord_6699687 prefixEnd_6699687 1146719888559678059167069 := by
  unfold tailWord_6699687
  simp only [CollatzResearch.WordTrace]
  refine ⟨244357659679185689289065315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162905106452790459526043543 244357659679185689289065315)
  ·
    refine ⟨366536489518778533933597973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244357659679185689289065315 366536489518778533933597973)
    ·
      refine ⟨17181397946192743778137405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366536489518778533933597973 17181397946192743778137405)
      ·
        refine ⟨6443024229822278916801527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17181397946192743778137405 6443024229822278916801527)
        ·
          refine ⟨9664536344733418375202291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443024229822278916801527 9664536344733418375202291)
          ·
            refine ⟨14496804517100127562803437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9664536344733418375202291 14496804517100127562803437)
            ·
              refine ⟨5436301693912547836051289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14496804517100127562803437 5436301693912547836051289)
              ·
                refine ⟨4077226270434410877038467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436301693912547836051289 4077226270434410877038467)
                ·
                  refine ⟨6115839405651616315557701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077226270434410877038467 6115839405651616315557701)
                  ·
                    refine ⟨1146719888559678059167069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115839405651616315557701 1146719888559678059167069)
                    ·
                      rfl

theorem cell23_6699687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6699687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699687 prefixEnd_6699687 := by exact prefixLift 6699687
  have htrace : WordTrace (prefixWord ++ tailWord_6699687) baseStart_6699687 baseEnd_6699687 := by
    simpa [prefixWord, tailWord_6699687, baseEnd_6699687] using wordTrace_append hprefix tailTrace_6699687
  have hstable : (prefixWord ++ tailWord_6699687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699687).length < 2 ^ (prefixWord ++ tailWord_6699687).sum := by decide
  have hdescent : baseEnd_6699687 < baseStart_6699687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699693 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_6699693 : Nat := 118140960795 + 6699693 * 2 ^ 59
def prefixEnd_6699693 : Nat := 4983230072969 + 3 ^ 40 * 6699693 * 2
def baseEnd_6699693 : Nat := 3440162746562961154026179

theorem tailTrace_6699693 : CollatzResearch.WordTrace tailWord_6699693 prefixEnd_6699693 3440162746562961154026179 := by
  unfold tailWord_6699693
  simp only [CollatzResearch.WordTrace]
  refine ⟨244357878517163952313783733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162905252344775968209189155 244357878517163952313783733)
  ·
    refine ⟨22908551110984120529417225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244357878517163952313783733 22908551110984120529417225)
    ·
      refine ⟨17181413333238090397062919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22908551110984120529417225 17181413333238090397062919)
      ·
        refine ⟨25772119999857135595594379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181413333238090397062919 25772119999857135595594379)
        ·
          refine ⟨38658179999785703393391569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772119999857135595594379 38658179999785703393391569)
          ·
            refine ⟨28993634999839277545043677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38658179999785703393391569 28993634999839277545043677)
            ·
              refine ⟨10872613124939729079391379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28993634999839277545043677 10872613124939729079391379)
              ·
                refine ⟨16308919687409593619087069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872613124939729079391379 16308919687409593619087069)
                ·
                  refine ⟨6115844882778597607157651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16308919687409593619087069 6115844882778597607157651)
                  ·
                    refine ⟨9173767324167896410736477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115844882778597607157651 9173767324167896410736477)
                    ·
                      refine ⟨3440162746562961154026179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9173767324167896410736477 3440162746562961154026179)
                      ·
                        rfl

theorem cell23_6699693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_6699693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699693 prefixEnd_6699693 := by exact prefixLift 6699693
  have htrace : WordTrace (prefixWord ++ tailWord_6699693) baseStart_6699693 baseEnd_6699693 := by
    simpa [prefixWord, tailWord_6699693, baseEnd_6699693] using wordTrace_append hprefix tailTrace_6699693
  have hstable : (prefixWord ++ tailWord_6699693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699693).length < 2 ^ (prefixWord ++ tailWord_6699693).sum := by decide
  have hdescent : baseEnd_6699693 < baseStart_6699693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699713 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6699713 : Nat := 118140960795 + 6699713 * 2 ^ 59
def prefixEnd_6699713 : Nat := 4983230072969 + 3 ^ 40 * 6699713 * 2
def baseEnd_6699713 : Nat := 1146724338725350358592029

theorem tailTrace_6699713 : CollatzResearch.WordTrace tailWord_6699713 prefixEnd_6699713 1146724338725350358592029 := by
  unfold tailWord_6699713
  simp only [CollatzResearch.WordTrace]
  refine ⟨244358607977091495729511793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162905738651394330486341195 244358607977091495729511793)
  ·
    refine ⟨183268955982818621797133845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244358607977091495729511793 183268955982818621797133845)
    ·
      refine ⟨8590732311694622896740649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183268955982818621797133845 8590732311694622896740649)
      ·
        refine ⟨6443049233770967172555487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8590732311694622896740649 6443049233770967172555487)
        ·
          refine ⟨9664573850656450758833231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443049233770967172555487 9664573850656450758833231)
          ·
            refine ⟨14496860775984676138249847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9664573850656450758833231 14496860775984676138249847)
            ·
              refine ⟨21745291163977014207374771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14496860775984676138249847 21745291163977014207374771)
              ·
                refine ⟨32617936745965521311062157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21745291163977014207374771 32617936745965521311062157)
                ·
                  refine ⟨12231726279737070491648309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32617936745965521311062157 12231726279737070491648309)
                  ·
                    refine ⟨1146724338725350358592029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12231726279737070491648309 1146724338725350358592029)
                    ·
                      rfl

theorem cell23_6699713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6699713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699713 prefixEnd_6699713 := by exact prefixLift 6699713
  have htrace : WordTrace (prefixWord ++ tailWord_6699713) baseStart_6699713 baseEnd_6699713 := by
    simpa [prefixWord, tailWord_6699713, baseEnd_6699713] using wordTrace_append hprefix tailTrace_6699713
  have hstable : (prefixWord ++ tailWord_6699713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699713).length < 2 ^ (prefixWord ++ tailWord_6699713).sum := by decide
  have hdescent : baseEnd_6699713 < baseStart_6699713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699716 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6699716 : Nat := 118140960795 + 6699716 * 2 ^ 59
def prefixEnd_6699716 : Nat := 4983230072969 + 3 ^ 40 * 6699716 * 2
def baseEnd_6699716 : Nat := 3440174556618014564038573

theorem tailTrace_6699716 : CollatzResearch.WordTrace tailWord_6699716 prefixEnd_6699716 3440174556618014564038573 := by
  unfold tailWord_6699716
  simp only [CollatzResearch.WordTrace]
  refine ⟨122179358698040313620935501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162905811597387084827914001 122179358698040313620935501)
  ·
    refine ⟨45817259511765117607850813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122179358698040313620935501 45817259511765117607850813)
    ·
      refine ⟨17181472316911919102944055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45817259511765117607850813 17181472316911919102944055)
      ·
        refine ⟨25772208475367878654416083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181472316911919102944055 25772208475367878654416083)
        ·
          refine ⟨38658312713051817981624125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772208475367878654416083 38658312713051817981624125)
          ·
            refine ⟨14496867267394431743109047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38658312713051817981624125 14496867267394431743109047)
            ·
              refine ⟨21745300901091647614663571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14496867267394431743109047 21745300901091647614663571)
              ·
                refine ⟨32617951351637471421995357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21745300901091647614663571 32617951351637471421995357)
                ·
                  refine ⟨12231731756864051783248259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32617951351637471421995357 12231731756864051783248259)
                  ·
                    refine ⟨18347597635296077674872389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12231731756864051783248259 18347597635296077674872389)
                    ·
                      refine ⟨3440174556618014564038573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18347597635296077674872389 3440174556618014564038573)
                      ·
                        rfl

theorem cell23_6699716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6699716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699716 prefixEnd_6699716 := by exact prefixLift 6699716
  have htrace : WordTrace (prefixWord ++ tailWord_6699716) baseStart_6699716 baseEnd_6699716 := by
    simpa [prefixWord, tailWord_6699716, baseEnd_6699716] using wordTrace_append hprefix tailTrace_6699716
  have hstable : (prefixWord ++ tailWord_6699716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699716).length < 2 ^ (prefixWord ++ tailWord_6699716).sum := by decide
  have hdescent : baseEnd_6699716 < baseStart_6699716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699729 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_6699729 : Nat := 118140960795 + 6699729 * 2 ^ 59
def prefixEnd_6699729 : Nat := 4983230072969 + 3 ^ 40 * 6699729 * 2
def baseEnd_6699729 : Nat := 3440181231866523013176013

theorem tailTrace_6699729 : CollatzResearch.WordTrace tailWord_6699729 prefixEnd_6699729 3440181231866523013176013 := by
  unfold tailWord_6699729
  simp only [CollatzResearch.WordTrace]
  refine ⟨244359191545033530462094241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162906127696689020308062827 244359191545033530462094241)
  ·
    refine ⟨183269393658775147846570681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244359191545033530462094241 183269393658775147846570681)
    ·
      refine ⟨137452045244081360884928011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183269393658775147846570681 137452045244081360884928011)
      ·
        refine ⟨206178067866122041327392017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137452045244081360884928011 206178067866122041327392017)
        ·
          refine ⟨154633550899591530995544013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206178067866122041327392017 154633550899591530995544013)
          ·
            refine ⟨57987581587346824123329005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154633550899591530995544013 57987581587346824123329005)
            ·
              refine ⟨21745343095255059046248377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57987581587346824123329005 21745343095255059046248377)
              ·
                refine ⟨16309007321441294284686283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21745343095255059046248377 16309007321441294284686283)
                ·
                  refine ⟨24463510982161941427029425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16309007321441294284686283 24463510982161941427029425)
                  ·
                    refine ⟨18347633236621456070272069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24463510982161941427029425 18347633236621456070272069)
                    ·
                      refine ⟨3440181231866523013176013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18347633236621456070272069 3440181231866523013176013)
                      ·
                        rfl

theorem cell23_6699729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_6699729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699729 prefixEnd_6699729 := by exact prefixLift 6699729
  have htrace : WordTrace (prefixWord ++ tailWord_6699729) baseStart_6699729 baseEnd_6699729 := by
    simpa [prefixWord, tailWord_6699729, baseEnd_6699729] using wordTrace_append hprefix tailTrace_6699729
  have hstable : (prefixWord ++ tailWord_6699729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699729).length < 2 ^ (prefixWord ++ tailWord_6699729).sum := by decide
  have hdescent : baseEnd_6699729 < baseStart_6699729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699736 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_6699736 : Nat := 118140960795 + 6699736 * 2 ^ 59
def prefixEnd_6699736 : Nat := 4983230072969 + 3 ^ 40 * 6699736 * 2
def baseEnd_6699736 : Nat := 3440184826231104485788481

theorem tailTrace_6699736 : CollatzResearch.WordTrace tailWord_6699736 prefixEnd_6699736 3440184826231104485788481 := by
  unfold tailWord_6699736
  simp only [CollatzResearch.WordTrace]
  refine ⟨122179723428004085328799531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162906297904005447105066041 122179723428004085328799531)
  ·
    refine ⟨183269585142006127993199297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122179723428004085328799531 183269585142006127993199297)
    ·
      refine ⟨137452188856504595994899473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183269585142006127993199297 137452188856504595994899473)
      ·
        refine ⟨103089141642378446996174605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137452188856504595994899473 103089141642378446996174605)
        ·
          refine ⟨38658428115891917623565477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103089141642378446996174605 38658428115891917623565477)
          ·
            refine ⟨7248455271729734554418527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38658428115891917623565477 7248455271729734554418527)
            ·
              refine ⟨10872682907594601831627791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248455271729734554418527 10872682907594601831627791)
              ·
                refine ⟨16309024361391902747441687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872682907594601831627791 16309024361391902747441687)
                ·
                  refine ⟨24463536542087854121162531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16309024361391902747441687 24463536542087854121162531)
                  ·
                    refine ⟨36695304813131781181743797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24463536542087854121162531 36695304813131781181743797)
                    ·
                      refine ⟨3440184826231104485788481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36695304813131781181743797 3440184826231104485788481)
                      ·
                        rfl

theorem cell23_6699736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_6699736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699736 prefixEnd_6699736 := by exact prefixLift 6699736
  have htrace : WordTrace (prefixWord ++ tailWord_6699736) baseStart_6699736 baseEnd_6699736 := by
    simpa [prefixWord, tailWord_6699736, baseEnd_6699736] using wordTrace_append hprefix tailTrace_6699736
  have hstable : (prefixWord ++ tailWord_6699736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699736).length < 2 ^ (prefixWord ++ tailWord_6699736).sum := by decide
  have hdescent : baseEnd_6699736 < baseStart_6699736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699893 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_6699893 : Nat := 118140960795 + 6699893 * 2 ^ 59
def prefixEnd_6699893 : Nat := 4983230072969 + 3 ^ 40 * 6699893 * 2
def baseEnd_6699893 : Nat := 1146755147564620123841753

theorem tailTrace_6699893 : CollatzResearch.WordTrace tailWord_6699893 prefixEnd_6699893 1146755147564620123841753 := by
  unfold tailWord_6699893
  simp only [CollatzResearch.WordTrace]
  refine ⟨244365173116439386471064333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162910115410959590980709555 244365173116439386471064333)
  ·
    refine ⟨91636939918664769926649125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244365173116439386471064333 91636939918664769926649125)
    ·
      refine ⟨17181926234749644361246711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91636939918664769926649125 17181926234749644361246711)
      ·
        refine ⟨25772889352124466541870067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181926234749644361246711 25772889352124466541870067)
        ·
          refine ⟨38659334028186699812805101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772889352124466541870067 38659334028186699812805101)
          ·
            refine ⟨14497250260570012429801913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38659334028186699812805101 14497250260570012429801913)
            ·
              refine ⟨10872937695427509322351435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14497250260570012429801913 10872937695427509322351435)
              ·
                refine ⟨16309406543141263983527153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872937695427509322351435 16309406543141263983527153)
                ·
                  refine ⟨12232054907355947987645365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16309406543141263983527153 12232054907355947987645365)
                  ·
                    refine ⟨1146755147564620123841753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12232054907355947987645365 1146755147564620123841753)
                    ·
                      rfl

theorem cell23_6699893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_6699893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699893 prefixEnd_6699893 := by exact prefixLift 6699893
  have htrace : WordTrace (prefixWord ++ tailWord_6699893) baseStart_6699893 baseEnd_6699893 := by
    simpa [prefixWord, tailWord_6699893, baseEnd_6699893] using wordTrace_append hprefix tailTrace_6699893
  have hstable : (prefixWord ++ tailWord_6699893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699893).length < 2 ^ (prefixWord ++ tailWord_6699893).sum := by decide
  have hdescent : baseEnd_6699893 < baseStart_6699893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699896 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_6699896 : Nat := 118140960795 + 6699896 * 2 ^ 59
def prefixEnd_6699896 : Nat := 4983230072969 + 3 ^ 40 * 6699896 * 2
def baseEnd_6699896 : Nat := 3440266983135823859787745

theorem tailTrace_6699896 : CollatzResearch.WordTrace tailWord_6699896 prefixEnd_6699896 3440266983135823859787745 := by
  unfold tailWord_6699896
  simp only [CollatzResearch.WordTrace]
  refine ⟨122182641267714258991711771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162910188356952345322282361 122182641267714258991711771)
  ·
    refine ⟨183273961901571388487567657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122182641267714258991711771 183273961901571388487567657)
    ·
      refine ⟨137455471426178541365675743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183273961901571388487567657 137455471426178541365675743)
      ·
        refine ⟨206183207139267812048513615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137455471426178541365675743 206183207139267812048513615)
        ·
          refine ⟨309274810708901718072770423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206183207139267812048513615 309274810708901718072770423)
          ·
            refine ⟨463912216063352577109155635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309274810708901718072770423 463912216063352577109155635)
            ·
              refine ⟨695868324095028865663733453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463912216063352577109155635 695868324095028865663733453)
              ·
                refine ⟨260950621535635824623900045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695868324095028865663733453 260950621535635824623900045)
                ·
                  refine ⟨97856483075863434233962517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260950621535635824623900045 97856483075863434233962517)
                  ·
                    refine ⟨4587022644181098479716993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97856483075863434233962517 4587022644181098479716993)
                    ·
                      refine ⟨3440266983135823859787745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587022644181098479716993 3440266983135823859787745)
                      ·
                        rfl

theorem cell23_6699896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_6699896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699896 prefixEnd_6699896 := by exact prefixLift 6699896
  have htrace : WordTrace (prefixWord ++ tailWord_6699896) baseStart_6699896 baseEnd_6699896 := by
    simpa [prefixWord, tailWord_6699896, baseEnd_6699896] using wordTrace_append hprefix tailTrace_6699896
  have hstable : (prefixWord ++ tailWord_6699896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699896).length < 2 ^ (prefixWord ++ tailWord_6699896).sum := by decide
  have hdescent : baseEnd_6699896 < baseStart_6699896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699930 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6699930 : Nat := 118140960795 + 6699930 * 2 ^ 59
def prefixEnd_6699930 : Nat := 4983230072969 + 3 ^ 40 * 6699930 * 2
def baseEnd_6699930 : Nat := 3440284441478076726762589

theorem tailTrace_6699930 : CollatzResearch.WordTrace tailWord_6699930 prefixEnd_6699930 3440284441478076726762589 := by
  unfold tailWord_6699930
  simp only [CollatzResearch.WordTrace]
  refine ⟨61091630654326335447540311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162911015078203561193440829 61091630654326335447540311)
  ·
    refine ⟨91637445981489503171310467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61091630654326335447540311 91637445981489503171310467)
    ·
      refine ⟨137456168972234254756965701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91637445981489503171310467 137456168972234254756965701)
      ·
        refine ⟨25773031682293922766931069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137456168972234254756965701 25773031682293922766931069)
        ·
          refine ⟨9664886880860221037599151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25773031682293922766931069 9664886880860221037599151)
          ·
            refine ⟨14497330321290331556398727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9664886880860221037599151 14497330321290331556398727)
            ·
              refine ⟨21745995481935497334598091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497330321290331556398727 21745995481935497334598091)
              ·
                refine ⟨32618993222903246001897137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21745995481935497334598091 32618993222903246001897137)
                ·
                  refine ⟨24464244917177434501422853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32618993222903246001897137 24464244917177434501422853)
                  ·
                    refine ⟨4587045921970768969016785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24464244917177434501422853 4587045921970768969016785)
                    ·
                      refine ⟨3440284441478076726762589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587045921970768969016785 3440284441478076726762589)
                      ·
                        rfl

theorem cell23_6699930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6699930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699930 prefixEnd_6699930 := by exact prefixLift 6699930
  have htrace : WordTrace (prefixWord ++ tailWord_6699930) baseStart_6699930 baseEnd_6699930 := by
    simpa [prefixWord, tailWord_6699930, baseEnd_6699930] using wordTrace_append hprefix tailTrace_6699930
  have hstable : (prefixWord ++ tailWord_6699930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699930).length < 2 ^ (prefixWord ++ tailWord_6699930).sum := by decide
  have hdescent : baseEnd_6699930 < baseStart_6699930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699936 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 6]
def baseStart_6699936 : Nat := 118140960795 + 6699936 * 2 ^ 59
def prefixEnd_6699936 : Nat := 4983230072969 + 3 ^ 40 * 6699936 * 2
def baseEnd_6699936 : Nat := 382254169151333744809729

theorem tailTrace_6699936 : CollatzResearch.WordTrace tailWord_6699936 prefixEnd_6699936 382254169151333744809729 := by
  unfold tailWord_6699936
  simp only [CollatzResearch.WordTrace]
  refine ⟨122183370727641802407439831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162911160970189069876586441 122183370727641802407439831)
  ·
    refine ⟨183275056091462703611159747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122183370727641802407439831 183275056091462703611159747)
    ·
      refine ⟨274912584137194055416739621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183275056091462703611159747 274912584137194055416739621)
      ·
        refine ⟨51546109525723885390638679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274912584137194055416739621 51546109525723885390638679)
        ·
          refine ⟨77319164288585828085958019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51546109525723885390638679 77319164288585828085958019)
          ·
            refine ⟨115978746432878742128937029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77319164288585828085958019 115978746432878742128937029)
            ·
              refine ⟨21746014956164764149175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115978746432878742128937029 21746014956164764149175693)
              ·
                refine ⟨8154755608561786555940885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21746014956164764149175693 8154755608561786555940885)
                ·
                  refine ⟨382254169151333744809729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8154755608561786555940885 382254169151333744809729)
                  ·
                    rfl

theorem cell23_6699936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_6699936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699936 prefixEnd_6699936 := by exact prefixLift 6699936
  have htrace : WordTrace (prefixWord ++ tailWord_6699936) baseStart_6699936 baseEnd_6699936 := by
    simpa [prefixWord, tailWord_6699936, baseEnd_6699936] using wordTrace_append hprefix tailTrace_6699936
  have hstable : (prefixWord ++ tailWord_6699936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699936).length < 2 ^ (prefixWord ++ tailWord_6699936).sum := by decide
  have hdescent : baseEnd_6699936 < baseStart_6699936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6699980 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6699980 : Nat := 118140960795 + 6699980 * 2 ^ 59
def prefixEnd_6699980 : Nat := 4983230072969 + 3 ^ 40 * 6699980 * 2
def baseEnd_6699980 : Nat := 3440310115510801531137359

theorem tailTrace_6699980 : CollatzResearch.WordTrace tailWord_6699980 prefixEnd_6699980 3440310115510801531137359 := by
  unfold tailWord_6699980
  simp only [CollatzResearch.WordTrace]
  refine ⟨122184173133562100164740697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162912230844749466886320929 122184173133562100164740697)
  ·
    refine ⟨91638129850171575123555523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122184173133562100164740697 91638129850171575123555523)
    ·
      refine ⟨137457194775257362685333285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91638129850171575123555523 137457194775257362685333285)
      ·
        refine ⟨25773224020360755503499991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137457194775257362685333285 25773224020360755503499991)
        ·
          refine ⟨38659836030541133255249987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773224020360755503499991 38659836030541133255249987)
          ·
            refine ⟨57989754045811699882874981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38659836030541133255249987 57989754045811699882874981)
            ·
              refine ⟨10873078883589693728039059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57989754045811699882874981 10873078883589693728039059)
              ·
                refine ⟨16309618325384540592058589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873078883589693728039059 16309618325384540592058589)
                ·
                  refine ⟨6116106872019202722021971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16309618325384540592058589 6116106872019202722021971)
                  ·
                    refine ⟨9174160308028804083032957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116106872019202722021971 9174160308028804083032957)
                    ·
                      refine ⟨3440310115510801531137359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174160308028804083032957 3440310115510801531137359)
                      ·
                        rfl

theorem cell23_6699980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6699980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6699980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6699980 prefixEnd_6699980 := by exact prefixLift 6699980
  have htrace : WordTrace (prefixWord ++ tailWord_6699980) baseStart_6699980 baseEnd_6699980 := by
    simpa [prefixWord, tailWord_6699980, baseEnd_6699980] using wordTrace_append hprefix tailTrace_6699980
  have hstable : (prefixWord ++ tailWord_6699980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6699980).length < 2 ^ (prefixWord ++ tailWord_6699980).sum := by decide
  have hdescent : baseEnd_6699980 < baseStart_6699980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6699980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700003 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6700003 : Nat := 118140960795 + 6700003 * 2 ^ 59
def prefixEnd_6700003 : Nat := 4983230072969 + 3 ^ 40 * 6700003 * 2
def baseEnd_6700003 : Nat := 3440321925565854941149753

theorem tailTrace_6700003 : CollatzResearch.WordTrace tailWord_6700003 prefixEnd_6700003 3440321925565854941149753 := by
  unfold tailWord_6700003
  simp only [CollatzResearch.WordTrace]
  refine ⟨244369185146040875257568663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162912790097360583505045775 244369185146040875257568663)
  ·
    refine ⟨366553777719061312886352995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244369185146040875257568663 366553777719061312886352995)
    ·
      refine ⟨549830666578591969329529493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366553777719061312886352995 549830666578591969329529493)
      ·
        refine ⟨25773312495871498562321695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 549830666578591969329529493 25773312495871498562321695)
        ·
          refine ⟨38659968743807247843482543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773312495871498562321695 38659968743807247843482543)
          ·
            refine ⟨57989953115710871765223815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38659968743807247843482543 57989953115710871765223815)
            ·
              refine ⟨86984929673566307647835723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57989953115710871765223815 86984929673566307647835723)
              ·
                refine ⟨130477394510349461471753585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86984929673566307647835723 130477394510349461471753585)
                ·
                  refine ⟨97858045882762096103815189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130477394510349461471753585 97858045882762096103815189)
                  ·
                    refine ⟨4587095900754473254866337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97858045882762096103815189 4587095900754473254866337)
                    ·
                      refine ⟨3440321925565854941149753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587095900754473254866337 3440321925565854941149753)
                      ·
                        rfl

theorem cell23_6700003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6700003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700003 prefixEnd_6700003 := by exact prefixLift 6700003
  have htrace : WordTrace (prefixWord ++ tailWord_6700003) baseStart_6700003 baseEnd_6700003 := by
    simpa [prefixWord, tailWord_6700003, baseEnd_6700003] using wordTrace_append hprefix tailTrace_6700003
  have hstable : (prefixWord ++ tailWord_6700003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700003).length < 2 ^ (prefixWord ++ tailWord_6700003).sum := by decide
  have hdescent : baseEnd_6700003 < baseStart_6700003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700016 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_6700016 : Nat := 118140960795 + 6700016 * 2 ^ 59
def prefixEnd_6700016 : Nat := 4983230072969 + 3 ^ 40 * 6700016 * 2
def baseEnd_6700016 : Nat := 3440328600814363390287193

theorem tailTrace_6700016 : CollatzResearch.WordTrace tailWord_6700016 prefixEnd_6700016 3440328600814363390287193 := by
  unfold tailWord_6700016
  simp only [CollatzResearch.WordTrace]
  refine ⟨122184829647496889238895951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162913106196662518985194601 122184829647496889238895951)
  ·
    refine ⟨183277244471245333858343927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122184829647496889238895951 183277244471245333858343927)
    ·
      refine ⟨274915866706868000787515891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183277244471245333858343927 274915866706868000787515891)
      ·
        refine ⟨412373800060302001181273837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274915866706868000787515891 412373800060302001181273837)
        ·
          refine ⟨154640175022613250442977689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412373800060302001181273837 154640175022613250442977689)
          ·
            refine ⟨115980131266959937832233267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154640175022613250442977689 115980131266959937832233267)
            ·
              refine ⟨173970196900439906748349901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115980131266959937832233267 173970196900439906748349901)
              ·
                refine ⟨65238823837664965030631213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173970196900439906748349901 65238823837664965030631213)
                ·
                  refine ⟨24464558939124361886486705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65238823837664965030631213 24464558939124361886486705)
                  ·
                    refine ⟨18348419204343271414865029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24464558939124361886486705 18348419204343271414865029)
                    ·
                      refine ⟨3440328600814363390287193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18348419204343271414865029 3440328600814363390287193)
                      ·
                        rfl

theorem cell23_6700016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_6700016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700016 prefixEnd_6700016 := by exact prefixLift 6700016
  have htrace : WordTrace (prefixWord ++ tailWord_6700016) baseStart_6700016 baseEnd_6700016 := by
    simpa [prefixWord, tailWord_6700016, baseEnd_6700016] using wordTrace_append hprefix tailTrace_6700016
  have hstable : (prefixWord ++ tailWord_6700016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700016).length < 2 ^ (prefixWord ++ tailWord_6700016).sum := by decide
  have hdescent : baseEnd_6700016 < baseStart_6700016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700074 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6700074 : Nat := 118140960795 + 6700074 * 2 ^ 59
def prefixEnd_6700074 : Nat := 4983230072969 + 3 ^ 40 * 6700074 * 2
def baseEnd_6700074 : Nat := 3440358382692324163361927

theorem tailTrace_6700074 : CollatzResearch.WordTrace tailWord_6700074 prefixEnd_6700074 3440358382692324163361927 := by
  unfold tailWord_6700074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61092943682195913595850819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162914516485855769588935517 61092943682195913595850819)
  ·
    refine ⟨91639415523293870393776229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61092943682195913595850819 91639415523293870393776229)
    ·
      refine ⟨17182390410617600698833043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91639415523293870393776229 17182390410617600698833043)
      ·
        refine ⟨25773585615926401048249565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17182390410617600698833043 25773585615926401048249565)
        ·
          refine ⟨9665094605972400393093587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25773585615926401048249565 9665094605972400393093587)
          ·
            refine ⟨14497641908958600589640381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665094605972400393093587 14497641908958600589640381)
            ·
              refine ⟨5436615715859475221115143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14497641908958600589640381 5436615715859475221115143)
              ·
                refine ⟨8154923573789212831672715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436615715859475221115143 8154923573789212831672715)
                ·
                  refine ⟨12232385360683819247509073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154923573789212831672715 12232385360683819247509073)
                  ·
                    refine ⟨9174289020512864435631805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12232385360683819247509073 9174289020512864435631805)
                    ·
                      refine ⟨3440358382692324163361927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174289020512864435631805 3440358382692324163361927)
                      ·
                        rfl

theorem cell23_6700074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6700074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700074 prefixEnd_6700074 := by exact prefixLift 6700074
  have htrace : WordTrace (prefixWord ++ tailWord_6700074) baseStart_6700074 baseEnd_6700074 := by
    simpa [prefixWord, tailWord_6700074, baseEnd_6700074] using wordTrace_append hprefix tailTrace_6700074
  have hstable : (prefixWord ++ tailWord_6700074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700074).length < 2 ^ (prefixWord ++ tailWord_6700074).sum := by decide
  have hdescent : baseEnd_6700074 < baseStart_6700074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700093 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6700093 : Nat := 118140960795 + 6700093 * 2 ^ 59
def prefixEnd_6700093 : Nat := 4983230072969 + 3 ^ 40 * 6700093 * 2
def baseEnd_6700093 : Nat := 3440368138824759589024339

theorem tailTrace_6700093 : CollatzResearch.WordTrace tailWord_6700093 prefixEnd_6700093 3440368138824759589024339 := by
  unfold tailWord_6700093
  simp only [CollatzResearch.WordTrace]
  refine ⟨244372467715714820628344933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162914978477143213752229955 244372467715714820628344933)
  ·
    refine ⟨45819837696696528867814675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244372467715714820628344933 45819837696696528867814675)
    ·
      refine ⟨68729756545044793301722013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45819837696696528867814675 68729756545044793301722013)
      ·
        refine ⟨25773658704391797488145755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68729756545044793301722013 25773658704391797488145755)
        ·
          refine ⟨38660488056587696232218633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773658704391797488145755 38660488056587696232218633)
          ·
            refine ⟨28995366042440772174163975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38660488056587696232218633 28995366042440772174163975)
            ·
              refine ⟨43493049063661158261245963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28995366042440772174163975 43493049063661158261245963)
              ·
                refine ⟨65239573595491737391868945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43493049063661158261245963 65239573595491737391868945)
                ·
                  refine ⟨48929680196618803043901709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65239573595491737391868945 48929680196618803043901709)
                  ·
                    refine ⟨18348630073732051141463141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48929680196618803043901709 18348630073732051141463141)
                    ·
                      refine ⟨3440368138824759589024339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18348630073732051141463141 3440368138824759589024339)
                      ·
                        rfl

theorem cell23_6700093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6700093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700093 prefixEnd_6700093 := by exact prefixLift 6700093
  have htrace : WordTrace (prefixWord ++ tailWord_6700093) baseStart_6700093 baseEnd_6700093 := by
    simpa [prefixWord, tailWord_6700093, baseEnd_6700093] using wordTrace_append hprefix tailTrace_6700093
  have hstable : (prefixWord ++ tailWord_6700093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700093).length < 2 ^ (prefixWord ++ tailWord_6700093).sum := by decide
  have hdescent : baseEnd_6700093 < baseStart_6700093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700103 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 6]
def baseStart_6700103 : Nat := 118140960795 + 6700103 * 2 ^ 59
def prefixEnd_6700103 : Nat := 4983230072969 + 3 ^ 40 * 6700103 * 2
def baseEnd_6700103 : Nat := 1146791091210434849966431

theorem tailTrace_6700103 : CollatzResearch.WordTrace tailWord_6700103 prefixEnd_6700103 1146791091210434849966431 := by
  unfold tailWord_6700103
  simp only [CollatzResearch.WordTrace]
  refine ⟨244372832445678592336208963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162915221630452394890805975 244372832445678592336208963)
  ·
    refine ⟨366559248668517888504313445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244372832445678592336208963 366559248668517888504313445)
    ·
      refine ⟨68729859125347104094558771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366559248668517888504313445 68729859125347104094558771)
      ·
        refine ⟨103094788688020656141838157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68729859125347104094558771 103094788688020656141838157)
        ·
          refine ⟨38660545758007746053189309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103094788688020656141838157 38660545758007746053189309)
          ·
            refine ⟨14497704659252904769945991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38660545758007746053189309 14497704659252904769945991)
            ·
              refine ⟨21746556988879357154918987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497704659252904769945991 21746556988879357154918987)
              ·
                refine ⟨32619835483319035732378481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21746556988879357154918987 32619835483319035732378481)
                ·
                  refine ⟨24464876612489276799283861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32619835483319035732378481 24464876612489276799283861)
                  ·
                    refine ⟨1146791091210434849966431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24464876612489276799283861 1146791091210434849966431)
                    ·
                      rfl

theorem cell23_6700103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_6700103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700103 prefixEnd_6700103 := by exact prefixLift 6700103
  have htrace : WordTrace (prefixWord ++ tailWord_6700103) baseStart_6700103 baseEnd_6700103 := by
    simpa [prefixWord, tailWord_6700103, baseEnd_6700103] using wordTrace_append hprefix tailTrace_6700103
  have hstable : (prefixWord ++ tailWord_6700103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700103).length < 2 ^ (prefixWord ++ tailWord_6700103).sum := by decide
  have hdescent : baseEnd_6700103 < baseStart_6700103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700143 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_6700143 : Nat := 118140960795 + 6700143 * 2 ^ 59
def prefixEnd_6700143 : Nat := 4983230072969 + 3 ^ 40 * 6700143 * 2
def baseEnd_6700143 : Nat := 3440393812857484393399109

theorem tailTrace_6700143 : CollatzResearch.WordTrace tailWord_6700143 prefixEnd_6700143 3440393812857484393399109 := by
  unfold tailWord_6700143
  simp only [CollatzResearch.WordTrace]
  refine ⟨244374291365533679167665083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162916194243689119445110055 244374291365533679167665083)
  ·
    refine ⟨366561437048300518751497625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244374291365533679167665083 366561437048300518751497625)
    ·
      refine ⟨274921077786225389063623219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366561437048300518751497625 274921077786225389063623219)
      ·
        refine ⟨412381616679338083595434829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274921077786225389063623219 412381616679338083595434829)
        ·
          refine ⟨154643106254751781348288061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412381616679338083595434829 154643106254751781348288061)
          ·
            refine ⟨57991164845531918005608023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154643106254751781348288061 57991164845531918005608023)
            ·
              refine ⟨86986747268297877008412035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57991164845531918005608023 86986747268297877008412035)
              ·
                refine ⟨130480120902446815512618053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86986747268297877008412035 130480120902446815512618053)
                ·
                  refine ⟨24465022669208777908615885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130480120902446815512618053 24465022669208777908615885)
                  ·
                    refine ⟨9174383500953291715730957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24465022669208777908615885 9174383500953291715730957)
                    ·
                      refine ⟨3440393812857484393399109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174383500953291715730957 3440393812857484393399109)
                      ·
                        rfl

theorem cell23_6700143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_6700143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700143 prefixEnd_6700143 := by exact prefixLift 6700143
  have htrace : WordTrace (prefixWord ++ tailWord_6700143) baseStart_6700143 baseEnd_6700143 := by
    simpa [prefixWord, tailWord_6700143, baseEnd_6700143] using wordTrace_append hprefix tailTrace_6700143
  have hstable : (prefixWord ++ tailWord_6700143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700143).length < 2 ^ (prefixWord ++ tailWord_6700143).sum := by decide
  have hdescent : baseEnd_6700143 < baseStart_6700143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700150 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6700150 : Nat := 118140960795 + 6700150 * 2 ^ 59
def prefixEnd_6700150 : Nat := 4983230072969 + 3 ^ 40 * 6700150 * 2
def baseEnd_6700150 : Nat := 382266378580229540667953

theorem tailTrace_6700150 : CollatzResearch.WordTrace tailWord_6700150 prefixEnd_6700150 382266378580229540667953 := by
  unfold tailWord_6700150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15273409167281769960198119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162916364451005546242113269 15273409167281769960198119)
  ·
    refine ⟨22910113750922654940297179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15273409167281769960198119 22910113750922654940297179)
    ·
      refine ⟨34365170626383982410445769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22910113750922654940297179 34365170626383982410445769)
      ·
        refine ⟨25773877969787986807834327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34365170626383982410445769 25773877969787986807834327)
        ·
          refine ⟨38660816954681980211751491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773877969787986807834327 38660816954681980211751491)
          ·
            refine ⟨57991225432022970317627237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38660816954681980211751491 57991225432022970317627237)
            ·
              refine ⟨10873354768504306934555107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57991225432022970317627237 10873354768504306934555107)
              ·
                refine ⟨16310032152756460401832661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873354768504306934555107 16310032152756460401832661)
                ·
                  refine ⟨382266378580229540667953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16310032152756460401832661 382266378580229540667953)
                  ·
                    rfl

theorem cell23_6700150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6700150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700150 prefixEnd_6700150 := by exact prefixLift 6700150
  have htrace : WordTrace (prefixWord ++ tailWord_6700150) baseStart_6700150 baseEnd_6700150 := by
    simpa [prefixWord, tailWord_6700150, baseEnd_6700150] using wordTrace_append hprefix tailTrace_6700150
  have hstable : (prefixWord ++ tailWord_6700150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700150).length < 2 ^ (prefixWord ++ tailWord_6700150).sum := by decide
  have hdescent : baseEnd_6700150 < baseStart_6700150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700161 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6700161 : Nat := 118140960795 + 6700161 * 2 ^ 59
def prefixEnd_6700161 : Nat := 4983230072969 + 3 ^ 40 * 6700161 * 2
def baseEnd_6700161 : Nat := 3440403055509265322974027

theorem tailTrace_6700161 : CollatzResearch.WordTrace tailWord_6700161 prefixEnd_6700161 3440403055509265322974027 := by
  unfold tailWord_6700161
  simp only [CollatzResearch.WordTrace]
  refine ⟨244374947879468468241820337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162916631919645645494546891 244374947879468468241820337)
  ·
    refine ⟨183281210909601351181365253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244374947879468468241820337 183281210909601351181365253)
    ·
      refine ⟨34365227045550253346505985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183281210909601351181365253 34365227045550253346505985)
      ·
        refine ⟨25773920284162690009879489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34365227045550253346505985 25773920284162690009879489)
        ·
          refine ⟨19330440213122017507409617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25773920284162690009879489 19330440213122017507409617)
          ·
            refine ⟨14497830159841513130557213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19330440213122017507409617 14497830159841513130557213)
            ·
              refine ⟨5436686309940567423958955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14497830159841513130557213 5436686309940567423958955)
              ·
                refine ⟨8155029464910851135938433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436686309940567423958955 8155029464910851135938433)
                ·
                  refine ⟨6116272098683138351953825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8155029464910851135938433 6116272098683138351953825)
                  ·
                    refine ⟨4587204074012353763965369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116272098683138351953825 4587204074012353763965369)
                    ·
                      refine ⟨3440403055509265322974027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587204074012353763965369 3440403055509265322974027)
                      ·
                        rfl

theorem cell23_6700161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6700161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700161 prefixEnd_6700161 := by exact prefixLift 6700161
  have htrace : WordTrace (prefixWord ++ tailWord_6700161) baseStart_6700161 baseEnd_6700161 := by
    simpa [prefixWord, tailWord_6700161, baseEnd_6700161] using wordTrace_append hprefix tailTrace_6700161
  have hstable : (prefixWord ++ tailWord_6700161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700161).length < 2 ^ (prefixWord ++ tailWord_6700161).sum := by decide
  have hdescent : baseEnd_6700161 < baseStart_6700161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700270 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6700270 : Nat := 118140960795 + 6700270 * 2 ^ 59
def prefixEnd_6700270 : Nat := 4983230072969 + 3 ^ 40 * 6700270 * 2
def baseEnd_6700270 : Nat := 1146819674966868465503675

theorem tailTrace_6700270 : CollatzResearch.WordTrace tailWord_6700270 prefixEnd_6700270 1146819674966868465503675 := by
  unfold tailWord_6700270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30547365429509197482192283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162919282290715719905025509 30547365429509197482192283)
  ·
    refine ⟨45821048144263796223288425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30547365429509197482192283 45821048144263796223288425)
    ·
      refine ⟨34365786108197847167466319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45821048144263796223288425 34365786108197847167466319)
      ·
        refine ⟨51548679162296770751199479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34365786108197847167466319 51548679162296770751199479)
        ·
          refine ⟨77323018743445156126799219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51548679162296770751199479 77323018743445156126799219)
          ·
            refine ⟨115984528115167734190198829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77323018743445156126799219 115984528115167734190198829)
            ·
              refine ⟨43494198043187900321324561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115984528115167734190198829 43494198043187900321324561)
              ·
                refine ⟨32620648532390925240993421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43494198043187900321324561 32620648532390925240993421)
                ·
                  refine ⟨12232743199646596965372533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32620648532390925240993421 12232743199646596965372533)
                  ·
                    refine ⟨1146819674966868465503675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12232743199646596965372533 1146819674966868465503675)
                    ·
                      rfl

theorem cell23_6700270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6700270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700270 prefixEnd_6700270 := by exact prefixLift 6700270
  have htrace : WordTrace (prefixWord ++ tailWord_6700270) baseStart_6700270 baseEnd_6700270 := by
    simpa [prefixWord, tailWord_6700270, baseEnd_6700270] using wordTrace_append hprefix tailTrace_6700270
  have hstable : (prefixWord ++ tailWord_6700270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700270).length < 2 ^ (prefixWord ++ tailWord_6700270).sum := by decide
  have hdescent : baseEnd_6700270 < baseStart_6700270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700284 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_6700284 : Nat := 118140960795 + 6700284 * 2 ^ 59
def prefixEnd_6700284 : Nat := 4983230072969 + 3 ^ 40 * 6700284 * 2
def baseEnd_6700284 : Nat := 3440466213629768341735961

theorem tailTrace_6700284 : CollatzResearch.WordTrace tailWord_6700284 prefixEnd_6700284 3440466213629768341735961 := by
  unfold tailWord_6700284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122189717029011430124273953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162919622705348573499031937 122189717029011430124273953)
  ·
    refine ⟨91642287771758572593205465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122189717029011430124273953 91642287771758572593205465)
    ·
      refine ⟨68731715828818929444904099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91642287771758572593205465 68731715828818929444904099)
      ·
        refine ⟨103097573743228394167356149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68731715828818929444904099 103097573743228394167356149)
        ·
          refine ⟨9665397538427661953189639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103097573743228394167356149 9665397538427661953189639)
          ·
            refine ⟨14498096307641492929784459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665397538427661953189639 14498096307641492929784459)
            ·
              refine ⟨21747144461462239394676689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498096307641492929784459 21747144461462239394676689)
              ·
                refine ⟨16310358346096679546007517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21747144461462239394676689 16310358346096679546007517)
                ·
                  refine ⟨6116384379786254829752819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16310358346096679546007517 6116384379786254829752819)
                  ·
                    refine ⟨9174576569679382244629229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116384379786254829752819 9174576569679382244629229)
                    ·
                      refine ⟨3440466213629768341735961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174576569679382244629229 3440466213629768341735961)
                      ·
                        rfl

theorem cell23_6700284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_6700284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700284 prefixEnd_6700284 := by exact prefixLift 6700284
  have htrace : WordTrace (prefixWord ++ tailWord_6700284) baseStart_6700284 baseEnd_6700284 := by
    simpa [prefixWord, tailWord_6700284, baseEnd_6700284] using wordTrace_append hprefix tailTrace_6700284
  have hstable : (prefixWord ++ tailWord_6700284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700284).length < 2 ^ (prefixWord ++ tailWord_6700284).sum := by decide
  have hdescent : baseEnd_6700284 < baseStart_6700284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700300 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_6700300 : Nat := 118140960795 + 6700300 * 2 ^ 59
def prefixEnd_6700300 : Nat := 4983230072969 + 3 ^ 40 * 6700300 * 2
def baseEnd_6700300 : Nat := 1146824809773413426378629

theorem tailTrace_6700300 : CollatzResearch.WordTrace tailWord_6700300 prefixEnd_6700300 1146824809773413426378629 := by
  unfold tailWord_6700300
  simp only [CollatzResearch.WordTrace]
  refine ⟨122190008812982447490565177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162920011750643263320753569 122190008812982447490565177)
  ·
    refine ⟨91642506609736835617923883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122190008812982447490565177 91642506609736835617923883)
    ·
      refine ⟨137463759914605253426885825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91642506609736835617923883 137463759914605253426885825)
      ·
        refine ⟨103097819935953940070164369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137463759914605253426885825 103097819935953940070164369)
        ·
          refine ⟨77323364951965455052623277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103097819935953940070164369 77323364951965455052623277)
          ·
            refine ⟨28996261856987045644733729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77323364951965455052623277 28996261856987045644733729)
            ·
              refine ⟨21747196392740284233550297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28996261856987045644733729 21747196392740284233550297)
              ·
                refine ⟨16310397294555213175162723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21747196392740284233550297 16310397294555213175162723)
                ·
                  refine ⟨24465595941832819762744085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16310397294555213175162723 24465595941832819762744085)
                  ·
                    refine ⟨1146824809773413426378629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24465595941832819762744085 1146824809773413426378629)
                    ·
                      rfl

theorem cell23_6700300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_6700300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700300 prefixEnd_6700300 := by exact prefixLift 6700300
  have htrace : WordTrace (prefixWord ++ tailWord_6700300) baseStart_6700300 baseEnd_6700300 := by
    simpa [prefixWord, tailWord_6700300, baseEnd_6700300] using wordTrace_append hprefix tailTrace_6700300
  have hstable : (prefixWord ++ tailWord_6700300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700300).length < 2 ^ (prefixWord ++ tailWord_6700300).sum := by decide
  have hdescent : baseEnd_6700300 < baseStart_6700300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700303 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_6700303 : Nat := 118140960795 + 6700303 * 2 ^ 59
def prefixEnd_6700303 : Nat := 4983230072969 + 3 ^ 40 * 6700303 * 2
def baseEnd_6700303 : Nat := 3440475969762203767398373

theorem tailTrace_6700303 : CollatzResearch.WordTrace tailWord_6700303 prefixEnd_6700303 3440475969762203767398373 := by
  unfold tailWord_6700303
  simp only [CollatzResearch.WordTrace]
  refine ⟨244380127044954026493489563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162920084696636017662326375 244380127044954026493489563)
  ·
    refine ⟨366570190567431039740234345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244380127044954026493489563 366570190567431039740234345)
    ·
      refine ⟨274927642925573279805175759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366570190567431039740234345 274927642925573279805175759)
      ·
        refine ⟨412391464388359919707763639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274927642925573279805175759 412391464388359919707763639)
        ·
          refine ⟨618587196582539879561645459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412391464388359919707763639 618587196582539879561645459)
          ·
            refine ⟨927880794873809819342468189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618587196582539879561645459 927880794873809819342468189)
            ·
              refine ⟨347955298077678682253425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927880794873809819342468189 347955298077678682253425571)
              ·
                refine ⟨521932947116518023380138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347955298077678682253425571 521932947116518023380138357)
                ·
                  refine ⟨48931213792173564691887971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521932947116518023380138357 48931213792173564691887971)
                  ·
                    refine ⟨73396820688260347037831957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48931213792173564691887971 73396820688260347037831957)
                    ·
                      refine ⟨3440475969762203767398373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73396820688260347037831957 3440475969762203767398373)
                      ·
                        rfl

theorem cell23_6700303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_6700303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700303 prefixEnd_6700303 := by exact prefixLift 6700303
  have htrace : WordTrace (prefixWord ++ tailWord_6700303) baseStart_6700303 baseEnd_6700303 := by
    simpa [prefixWord, tailWord_6700303, baseEnd_6700303] using wordTrace_append hprefix tailTrace_6700303
  have hstable : (prefixWord ++ tailWord_6700303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700303).length < 2 ^ (prefixWord ++ tailWord_6700303).sum := by decide
  have hdescent : baseEnd_6700303 < baseStart_6700303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700318 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6700318 : Nat := 118140960795 + 6700318 * 2 ^ 59
def prefixEnd_6700318 : Nat := 4983230072969 + 3 ^ 40 * 6700318 * 2
def baseEnd_6700318 : Nat := 3440483671972021208710805

theorem tailTrace_6700318 : CollatzResearch.WordTrace tailWord_6700318 prefixEnd_6700318 3440483671972021208710805 := by
  unfold tailWord_6700318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30547584267487460506910701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162920449426599789370190405 30547584267487460506910701)
  ·
    refine ⟨11455344100307797690091513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30547584267487460506910701 11455344100307797690091513)
    ·
      refine ⟨8591508075230848267568635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11455344100307797690091513 8591508075230848267568635)
      ·
        refine ⟨12887262112846272401352953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8591508075230848267568635 12887262112846272401352953)
        ·
          refine ⟨9665446584634704301014715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12887262112846272401352953 9665446584634704301014715)
          ·
            refine ⟨14498169876952056451522073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665446584634704301014715 14498169876952056451522073)
            ·
              refine ⟨10873627407714042338641555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14498169876952056451522073 10873627407714042338641555)
              ·
                refine ⟨16310441111571063507962333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873627407714042338641555 16310441111571063507962333)
                ·
                  refine ⟨6116415416839148815485875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16310441111571063507962333 6116415416839148815485875)
                  ·
                    refine ⟨9174623125258723223228813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116415416839148815485875 9174623125258723223228813)
                    ·
                      refine ⟨3440483671972021208710805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174623125258723223228813 3440483671972021208710805)
                      ·
                        rfl

theorem cell23_6700318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6700318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700318 prefixEnd_6700318 := by exact prefixLift 6700318
  have htrace : WordTrace (prefixWord ++ tailWord_6700318) baseStart_6700318 baseEnd_6700318 := by
    simpa [prefixWord, tailWord_6700318, baseEnd_6700318] using wordTrace_append hprefix tailTrace_6700318
  have hstable : (prefixWord ++ tailWord_6700318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700318).length < 2 ^ (prefixWord ++ tailWord_6700318).sum := by decide
  have hdescent : baseEnd_6700318 < baseStart_6700318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700337 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_6700337 : Nat := 118140960795 + 6700337 * 2 ^ 59
def prefixEnd_6700337 : Nat := 4983230072969 + 3 ^ 40 * 6700337 * 2
def baseEnd_6700337 : Nat := 3440493428104456634373217

theorem tailTrace_6700337 : CollatzResearch.WordTrace tailWord_6700337 prefixEnd_6700337 3440493428104456634373217 := by
  unfold tailWord_6700337
  simp only [CollatzResearch.WordTrace]
  refine ⟨244381367126830850300227265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162920911417887233533484843 244381367126830850300227265)
  ·
    refine ⟨183286025345123137725170449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244381367126830850300227265 183286025345123137725170449)
    ·
      refine ⟨137464519008842353293877837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183286025345123137725170449 137464519008842353293877837)
      ·
        refine ⟨51549194628315882485204189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137464519008842353293877837 51549194628315882485204189)
        ·
          refine ⟨19330947985618455931951571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51549194628315882485204189 19330947985618455931951571)
          ·
            refine ⟨28996421978427683897927357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19330947985618455931951571 28996421978427683897927357)
            ·
              refine ⟨10873658241910381461722759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28996421978427683897927357 10873658241910381461722759)
              ·
                refine ⟨16310487362865572192584139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873658241910381461722759 16310487362865572192584139)
                ·
                  refine ⟨24465731044298358288876209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16310487362865572192584139 24465731044298358288876209)
                  ·
                    refine ⟨18349298283223768716657157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24465731044298358288876209 18349298283223768716657157)
                    ·
                      refine ⟨3440493428104456634373217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18349298283223768716657157 3440493428104456634373217)
                      ·
                        rfl

theorem cell23_6700337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_6700337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700337 prefixEnd_6700337 := by exact prefixLift 6700337
  have htrace : WordTrace (prefixWord ++ tailWord_6700337) baseStart_6700337 baseEnd_6700337 := by
    simpa [prefixWord, tailWord_6700337, baseEnd_6700337] using wordTrace_append hprefix tailTrace_6700337
  have hstable : (prefixWord ++ tailWord_6700337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700337).length < 2 ^ (prefixWord ++ tailWord_6700337).sum := by decide
  have hdescent : baseEnd_6700337 < baseStart_6700337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700370 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_6700370 : Nat := 118140960795 + 6700370 * 2 ^ 59
def prefixEnd_6700370 : Nat := 4983230072969 + 3 ^ 40 * 6700370 * 2
def baseEnd_6700370 : Nat := 3440510372966055005260565

theorem tailTrace_6700370 : CollatzResearch.WordTrace tailWord_6700370 prefixEnd_6700370 3440510372966055005260565 := by
  unfold tailWord_6700370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61095642683927824234044641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162921713823807531290785709 61095642683927824234044641)
  ·
    refine ⟨45821732012945868175533481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61095642683927824234044641 45821732012945868175533481)
    ·
      refine ⟨34366299009709401131650111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45821732012945868175533481 34366299009709401131650111)
      ·
        refine ⟨51549448514564101697475167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34366299009709401131650111 51549448514564101697475167)
        ·
          refine ⟨77324172771846152546212751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51549448514564101697475167 77324172771846152546212751)
          ·
            refine ⟨115986259157769228819319127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77324172771846152546212751 115986259157769228819319127)
            ·
              refine ⟨173979388736653843228978691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115986259157769228819319127 173979388736653843228978691)
              ·
                refine ⟨260969083104980764843468037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173979388736653843228978691 260969083104980764843468037)
                ·
                  refine ⟨48931703082183893408150257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260969083104980764843468037 48931703082183893408150257)
                  ·
                    refine ⟨36698777311637920056112693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48931703082183893408150257 36698777311637920056112693)
                    ·
                      refine ⟨3440510372966055005260565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36698777311637920056112693 3440510372966055005260565)
                      ·
                        rfl

theorem cell23_6700370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_6700370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700370 prefixEnd_6700370 := by exact prefixLift 6700370
  have htrace : WordTrace (prefixWord ++ tailWord_6700370) baseStart_6700370 baseEnd_6700370 := by
    simpa [prefixWord, tailWord_6700370, baseEnd_6700370] using wordTrace_append hprefix tailTrace_6700370
  have hstable : (prefixWord ++ tailWord_6700370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700370).length < 2 ^ (prefixWord ++ tailWord_6700370).sum := by decide
  have hdescent : baseEnd_6700370 < baseStart_6700370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700381 : List Nat := [1, 4, 5, 1, 1, 1, 2, 8]
def baseStart_6700381 : Nat := 118140960795 + 6700381 * 2 ^ 59
def prefixEnd_6700381 : Nat := 4983230072969 + 3 ^ 40 * 6700381 * 2
def baseEnd_6700381 : Nat := 127426519305676091193445

theorem tailTrace_6700381 : CollatzResearch.WordTrace tailWord_6700381 prefixEnd_6700381 127426519305676091193445 := by
  unfold tailWord_6700381
  simp only [CollatzResearch.WordTrace]
  refine ⟨244382971938671445814828997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162921981292447630543219331 244382971938671445814828997)
  ·
    refine ⟨45821807238500896090280437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244382971938671445814828997 45821807238500896090280437)
    ·
      refine ⟨4295794428609459008463791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45821807238500896090280437 4295794428609459008463791)
      ·
        refine ⟨6443691642914188512695687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295794428609459008463791 6443691642914188512695687)
        ·
          refine ⟨9665537464371282769043531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443691642914188512695687 9665537464371282769043531)
          ·
            refine ⟨14498306196556924153565297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665537464371282769043531 14498306196556924153565297)
            ·
              refine ⟨10873729647417693115173973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14498306196556924153565297 10873729647417693115173973)
              ·
                refine ⟨127426519305676091193445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10873729647417693115173973 127426519305676091193445)
                ·
                  rfl

theorem cell23_6700381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 8].length) (baseStart_6700381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700381 prefixEnd_6700381 := by exact prefixLift 6700381
  have htrace : WordTrace (prefixWord ++ tailWord_6700381) baseStart_6700381 baseEnd_6700381 := by
    simpa [prefixWord, tailWord_6700381, baseEnd_6700381] using wordTrace_append hprefix tailTrace_6700381
  have hstable : (prefixWord ++ tailWord_6700381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700381).length < 2 ^ (prefixWord ++ tailWord_6700381).sum := by decide
  have hdescent : baseEnd_6700381 < baseStart_6700381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700391 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_6700391 : Nat := 118140960795 + 6700391 * 2 ^ 59
def prefixEnd_6700391 : Nat := 4983230072969 + 3 ^ 40 * 6700391 * 2
def baseEnd_6700391 : Nat := 3440521156059799423097969

theorem tailTrace_6700391 : CollatzResearch.WordTrace tailWord_6700391 prefixEnd_6700391 3440521156059799423097969 := by
  unfold tailWord_6700391
  simp only [CollatzResearch.WordTrace]
  refine ⟨244383336668635217522693027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162922224445756811681795351 244383336668635217522693027)
  ·
    refine ⟨366575005002952826284039541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244383336668635217522693027 366575005002952826284039541)
    ·
      refine ⟨34366406719026827464128707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366575005002952826284039541 34366406719026827464128707)
      ·
        refine ⟨51549610078540241196193061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34366406719026827464128707 51549610078540241196193061)
        ·
          refine ⟨9665551889726295224286199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51549610078540241196193061 9665551889726295224286199)
          ·
            refine ⟨14498327834589442836429299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665551889726295224286199 14498327834589442836429299)
            ·
              refine ⟨21747491751884164254643949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498327834589442836429299 21747491751884164254643949)
              ·
                refine ⟨8155309406956561595491481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21747491751884164254643949 8155309406956561595491481)
                ·
                  refine ⟨6116482055217421196618611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8155309406956561595491481 6116482055217421196618611)
                  ·
                    refine ⟨9174723082826131794927917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116482055217421196618611 9174723082826131794927917)
                    ·
                      refine ⟨3440521156059799423097969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174723082826131794927917 3440521156059799423097969)
                      ·
                        rfl

theorem cell23_6700391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_6700391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700391 prefixEnd_6700391 := by exact prefixLift 6700391
  have htrace : WordTrace (prefixWord ++ tailWord_6700391) baseStart_6700391 baseEnd_6700391 := by
    simpa [prefixWord, tailWord_6700391, baseEnd_6700391] using wordTrace_append hprefix tailTrace_6700391
  have hstable : (prefixWord ++ tailWord_6700391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700391).length < 2 ^ (prefixWord ++ tailWord_6700391).sum := by decide
  have hdescent : baseEnd_6700391 < baseStart_6700391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700400 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_6700400 : Nat := 118140960795 + 6700400 * 2 ^ 59
def prefixEnd_6700400 : Nat := 4983230072969 + 3 ^ 40 * 6700400 * 2
def baseEnd_6700400 : Nat := 3440525777385689887885427

theorem tailTrace_6700400 : CollatzResearch.WordTrace tailWord_6700400 prefixEnd_6700400 3440525777385689887885427 := by
  unfold tailWord_6700400
  simp only [CollatzResearch.WordTrace]
  refine ⟨122191832462801306029885327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162922443283735074706513769 122191832462801306029885327)
  ·
    refine ⟨183287748694201959044827991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122191832462801306029885327 183287748694201959044827991)
    ·
      refine ⟨274931623041302938567241987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183287748694201959044827991 274931623041302938567241987)
      ·
        refine ⟨412397434561954407850862981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274931623041302938567241987 412397434561954407850862981)
        ·
          refine ⟨77324518980366451472036809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412397434561954407850862981 77324518980366451472036809)
          ·
            refine ⟨57993389235274838604027607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77324518980366451472036809 57993389235274838604027607)
            ·
              refine ⟨86990083852912257906041411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57993389235274838604027607 86990083852912257906041411)
              ·
                refine ⟨130485125779368386859062117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86990083852912257906041411 130485125779368386859062117)
                ·
                  refine ⟨24465961083631572536074147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130485125779368386859062117 24465961083631572536074147)
                  ·
                    refine ⟨36698941625447358804111221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24465961083631572536074147 36698941625447358804111221)
                    ·
                      refine ⟨3440525777385689887885427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36698941625447358804111221 3440525777385689887885427)
                      ·
                        rfl

theorem cell23_6700400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_6700400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700400 prefixEnd_6700400 := by exact prefixLift 6700400
  have htrace : WordTrace (prefixWord ++ tailWord_6700400) baseStart_6700400 baseEnd_6700400 := by
    simpa [prefixWord, tailWord_6700400, baseEnd_6700400] using wordTrace_append hprefix tailTrace_6700400
  have hstable : (prefixWord ++ tailWord_6700400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700400).length < 2 ^ (prefixWord ++ tailWord_6700400).sum := by decide
  have hdescent : baseEnd_6700400 < baseStart_6700400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700410 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_6700410 : Nat := 118140960795 + 6700410 * 2 ^ 59
def prefixEnd_6700410 : Nat := 4983230072969 + 3 ^ 40 * 6700410 * 2
def baseEnd_6700410 : Nat := 3440530912192234848760381

theorem tailTrace_6700410 : CollatzResearch.WordTrace tailWord_6700410 prefixEnd_6700410 3440530912192234848760381 := by
  unfold tailWord_6700410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61096007413891595941908671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162922686437044255845089789 61096007413891595941908671)
  ·
    refine ⟨91644011120837393912863007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61096007413891595941908671 91644011120837393912863007)
    ·
      refine ⟨137466016681256090869294511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91644011120837393912863007 137466016681256090869294511)
      ·
        refine ⟨206199025021884136303941767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137466016681256090869294511 206199025021884136303941767)
        ·
          refine ⟨309298537532826204455912651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206199025021884136303941767 309298537532826204455912651)
          ·
            refine ⟨463947806299239306683868977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309298537532826204455912651 463947806299239306683868977)
            ·
              refine ⟨347960854724429480012901733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463947806299239306683868977 347960854724429480012901733)
              ·
                refine ⟨65242660260830527502419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347960854724429480012901733 65242660260830527502419075)
                ·
                  refine ⟨97863990391245791253628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65242660260830527502419075 97863990391245791253628613)
                  ·
                    refine ⟨18349498198358585860055365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97863990391245791253628613 18349498198358585860055365)
                    ·
                      refine ⟨3440530912192234848760381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18349498198358585860055365 3440530912192234848760381)
                      ·
                        rfl

theorem cell23_6700410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_6700410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700410 prefixEnd_6700410 := by exact prefixLift 6700410
  have htrace : WordTrace (prefixWord ++ tailWord_6700410) baseStart_6700410 baseEnd_6700410 := by
    simpa [prefixWord, tailWord_6700410, baseEnd_6700410] using wordTrace_append hprefix tailTrace_6700410
  have hstable : (prefixWord ++ tailWord_6700410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700410).length < 2 ^ (prefixWord ++ tailWord_6700410).sum := by decide
  have hdescent : baseEnd_6700410 < baseStart_6700410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700447 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_6700447 : Nat := 118140960795 + 6700447 * 2 ^ 59
def prefixEnd_6700447 : Nat := 4983230072969 + 3 ^ 40 * 6700447 * 2
def baseEnd_6700447 : Nat := 3440549910976451203997711

theorem tailTrace_6700447 : CollatzResearch.WordTrace tailWord_6700447 prefixEnd_6700447 3440549910976451203997711 := by
  unfold tailWord_6700447
  simp only [CollatzResearch.WordTrace]
  refine ⟨244385379156432339086731595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162923586104288226057821063 244385379156432339086731595)
  ·
    refine ⟨366578068734648508630097393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244385379156432339086731595 366578068734648508630097393)
    ·
      refine ⟨274933551550986381472573045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366578068734648508630097393 274933551550986381472573045)
      ·
        refine ⟨25775020457904973263053723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274933551550986381472573045 25775020457904973263053723)
        ·
          refine ⟨38662530686857459894580585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25775020457904973263053723 38662530686857459894580585)
          ·
            refine ⟨28996898015143094920935439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38662530686857459894580585 28996898015143094920935439)
            ·
              refine ⟨43495347022714642381403159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28996898015143094920935439 43495347022714642381403159)
              ·
                refine ⟨65243020534071963572104739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43495347022714642381403159 65243020534071963572104739)
                ·
                  refine ⟨97864530801107945358157109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65243020534071963572104739 97864530801107945358157109)
                  ·
                    refine ⟨9174799762603869877327229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97864530801107945358157109 9174799762603869877327229)
                    ·
                      refine ⟨3440549910976451203997711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9174799762603869877327229 3440549910976451203997711)
                      ·
                        rfl

theorem cell23_6700447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_6700447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700447 prefixEnd_6700447 := by exact prefixLift 6700447
  have htrace : WordTrace (prefixWord ++ tailWord_6700447) baseStart_6700447 baseEnd_6700447 := by
    simpa [prefixWord, tailWord_6700447, baseEnd_6700447] using wordTrace_append hprefix tailTrace_6700447
  have hstable : (prefixWord ++ tailWord_6700447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700447).length < 2 ^ (prefixWord ++ tailWord_6700447).sum := by decide
  have hdescent : baseEnd_6700447 < baseStart_6700447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700460 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6700460 : Nat := 118140960795 + 6700460 * 2 ^ 59
def prefixEnd_6700460 : Nat := 4983230072969 + 3 ^ 40 * 6700460 * 2
def baseEnd_6700460 : Nat := 3440556586224959653135151

theorem tailTrace_6700460 : CollatzResearch.WordTrace tailWord_6700460 prefixEnd_6700460 3440556586224959653135151 := by
  unfold tailWord_6700460
  simp only [CollatzResearch.WordTrace]
  refine ⟨122192926652692621153477417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162923902203590161537969889 122192926652692621153477417)
  ·
    refine ⟨91644694989519465865108063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122192926652692621153477417 91644694989519465865108063)
    ·
      refine ⟨137467042484279198797662095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91644694989519465865108063 137467042484279198797662095)
      ·
        refine ⟨206200563726418798196493143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137467042484279198797662095 206200563726418798196493143)
        ·
          refine ⟨309300845589628197294739715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206200563726418798196493143 309300845589628197294739715)
          ·
            refine ⟨463951268384442295942109573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309300845589628197294739715 463951268384442295942109573)
            ·
              refine ⟨86990862822082930489145545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 463951268384442295942109573 86990862822082930489145545)
              ·
                refine ⟨65243147116562197866859159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86990862822082930489145545 65243147116562197866859159)
                ·
                  refine ⟨97864720674843296800288739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65243147116562197866859159 97864720674843296800288739)
                  ·
                    refine ⟨146797081012264945200433109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97864720674843296800288739 146797081012264945200433109)
                    ·
                      refine ⟨3440556586224959653135151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146797081012264945200433109 3440556586224959653135151)
                      ·
                        rfl

theorem cell23_6700460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6700460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700460 prefixEnd_6700460 := by exact prefixLift 6700460
  have htrace : WordTrace (prefixWord ++ tailWord_6700460) baseStart_6700460 baseEnd_6700460 := by
    simpa [prefixWord, tailWord_6700460, baseEnd_6700460] using wordTrace_append hprefix tailTrace_6700460
  have hstable : (prefixWord ++ tailWord_6700460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700460).length < 2 ^ (prefixWord ++ tailWord_6700460).sum := by decide
  have hdescent : baseEnd_6700460 < baseStart_6700460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700487 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_6700487 : Nat := 118140960795 + 6700487 * 2 ^ 59
def prefixEnd_6700487 : Nat := 4983230072969 + 3 ^ 40 * 6700487 * 2
def baseEnd_6700487 : Nat := 3440570450202631047497527

theorem tailTrace_6700487 : CollatzResearch.WordTrace tailWord_6700487 prefixEnd_6700487 3440570450202631047497527 := by
  unfold tailWord_6700487
  simp only [CollatzResearch.WordTrace]
  refine ⟨244386838076287425918187715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162924558717524950612125143 244386838076287425918187715)
  ·
    refine ⟨366580257114431138877281573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244386838076287425918187715 366580257114431138877281573)
    ·
      refine ⟨68733798208955838539490295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366580257114431138877281573 68733798208955838539490295)
      ·
        refine ⟨103100697313433757809235443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68733798208955838539490295 103100697313433757809235443)
        ·
          refine ⟨154651045970150636713853165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103100697313433757809235443 154651045970150636713853165)
          ·
            refine ⟨57994142238806488767694937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154651045970150636713853165 57994142238806488767694937)
            ·
              refine ⟨43495606679104866575771203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57994142238806488767694937 43495606679104866575771203)
              ·
                refine ⟨65243410018657299863656805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43495606679104866575771203 65243410018657299863656805)
                ·
                  refine ⟨12233139378498243724435651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65243410018657299863656805 12233139378498243724435651)
                  ·
                    refine ⟨18349709067747365586653477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12233139378498243724435651 18349709067747365586653477)
                    ·
                      refine ⟨3440570450202631047497527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18349709067747365586653477 3440570450202631047497527)
                      ·
                        rfl

theorem cell23_6700487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_6700487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700487 prefixEnd_6700487 := by exact prefixLift 6700487
  have htrace : WordTrace (prefixWord ++ tailWord_6700487) baseStart_6700487 baseEnd_6700487 := by
    simpa [prefixWord, tailWord_6700487, baseEnd_6700487] using wordTrace_append hprefix tailTrace_6700487
  have hstable : (prefixWord ++ tailWord_6700487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700487).length < 2 ^ (prefixWord ++ tailWord_6700487).sum := by decide
  have hdescent : baseEnd_6700487 < baseStart_6700487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700504 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_6700504 : Nat := 118140960795 + 6700504 * 2 ^ 59
def prefixEnd_6700504 : Nat := 4983230072969 + 3 ^ 40 * 6700504 * 2
def baseEnd_6700504 : Nat := 3440579179373757480984949

theorem tailTrace_6700504 : CollatzResearch.WordTrace tailWord_6700504 prefixEnd_6700504 3440579179373757480984949 := by
  unfold tailWord_6700504
  simp only [CollatzResearch.WordTrace]
  refine ⟨122193729058612918910778283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162924972078150558547704377 122193729058612918910778283)
  ·
    refine ⟨183290593587919378366167425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122193729058612918910778283 183290593587919378366167425)
    ·
      refine ⟨137467945190939533774625569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183290593587919378366167425 137467945190939533774625569)
      ·
        refine ⟨103100958893204650330969177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137467945190939533774625569 103100958893204650330969177)
        ·
          refine ⟨77325719169903487748226883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103100958893204650330969177 77325719169903487748226883)
          ·
            refine ⟨115988578754855231622340325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77325719169903487748226883 115988578754855231622340325)
            ·
              refine ⟨21747858516535355929188811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115988578754855231622340325 21747858516535355929188811)
              ·
                refine ⟨32621787774803033893783217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21747858516535355929188811 32621787774803033893783217)
                ·
                  refine ⟨24466340831102275420337413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32621787774803033893783217 24466340831102275420337413)
                  ·
                    refine ⟨4587438905831676641313265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24466340831102275420337413 4587438905831676641313265)
                    ·
                      refine ⟨3440579179373757480984949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587438905831676641313265 3440579179373757480984949)
                      ·
                        rfl

theorem cell23_6700504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_6700504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700504 prefixEnd_6700504 := by exact prefixLift 6700504
  have htrace : WordTrace (prefixWord ++ tailWord_6700504) baseStart_6700504 baseEnd_6700504 := by
    simpa [prefixWord, tailWord_6700504, baseEnd_6700504] using wordTrace_append hprefix tailTrace_6700504
  have hstable : (prefixWord ++ tailWord_6700504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700504).length < 2 ^ (prefixWord ++ tailWord_6700504).sum := by decide
  have hdescent : baseEnd_6700504 < baseStart_6700504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700548 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_6700548 : Nat := 118140960795 + 6700548 * 2 ^ 59
def prefixEnd_6700548 : Nat := 4983230072969 + 3 ^ 40 * 6700548 * 2
def baseEnd_6700548 : Nat := 1146867257507518436278249

theorem tailTrace_6700548 : CollatzResearch.WordTrace tailWord_6700548 prefixEnd_6700548 1146867257507518436278249 := by
  unfold tailWord_6700548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122194531464533216668079149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162926041952710955557438865 122194531464533216668079149)
  ·
    refine ⟨45822949299199956250529681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122194531464533216668079149 45822949299199956250529681)
    ·
      refine ⟨34367211974399967187897261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45822949299199956250529681 34367211974399967187897261)
      ·
        refine ⟨12887704490399987695461473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34367211974399967187897261 12887704490399987695461473)
        ·
          refine ⟨9665778367799990771596105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12887704490399987695461473 9665778367799990771596105)
          ·
            refine ⟨7249333775849993078697079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9665778367799990771596105 7249333775849993078697079)
            ·
              refine ⟨10874000663774989618045619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249333775849993078697079 10874000663774989618045619)
              ·
                refine ⟨16311000995662484427068429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874000663774989618045619 16311000995662484427068429)
                ·
                  refine ⟨6116625373373431660150661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16311000995662484427068429 6116625373373431660150661)
                  ·
                    refine ⟨1146867257507518436278249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116625373373431660150661 1146867257507518436278249)
                    ·
                      rfl

theorem cell23_6700548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_6700548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700548 prefixEnd_6700548 := by exact prefixLift 6700548
  have htrace : WordTrace (prefixWord ++ tailWord_6700548) baseStart_6700548 baseEnd_6700548 := by
    simpa [prefixWord, tailWord_6700548, baseEnd_6700548] using wordTrace_append hprefix tailTrace_6700548
  have hstable : (prefixWord ++ tailWord_6700548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700548).length < 2 ^ (prefixWord ++ tailWord_6700548).sum := by decide
  have hdescent : baseEnd_6700548 < baseStart_6700548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700605 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6700605 : Nat := 118140960795 + 6700605 * 2 ^ 59
def prefixEnd_6700605 : Nat := 4983230072969 + 3 ^ 40 * 6700605 * 2
def baseEnd_6700605 : Nat := 3440631040919861585821985

theorem tailTrace_6700605 : CollatzResearch.WordTrace tailWord_6700605 prefixEnd_6700605 3440631040919861585821985 := by
  unfold tailWord_6700605
  simp only [CollatzResearch.WordTrace]
  refine ⟨244391141889859932070983269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162927427926573288047322179 244391141889859932070983269)
  ·
    refine ⟨45823339104348737263309363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244391141889859932070983269 45823339104348737263309363)
    ·
      refine ⟨68735008656523105894964045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45823339104348737263309363 68735008656523105894964045)
      ·
        refine ⟨25775628246196164710611517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68735008656523105894964045 25775628246196164710611517)
        ·
          refine ⟨9665860592323561766479319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25775628246196164710611517 9665860592323561766479319)
          ·
            refine ⟨14498790888485342649718979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665860592323561766479319 14498790888485342649718979)
            ·
              refine ⟨21748186332728013974578469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498790888485342649718979 21748186332728013974578469)
              ·
                refine ⟨4077784937386502620233463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21748186332728013974578469 4077784937386502620233463)
                ·
                  refine ⟨6116677406079753930350195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077784937386502620233463 6116677406079753930350195)
                  ·
                    refine ⟨9175016109119630895525293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116677406079753930350195 9175016109119630895525293)
                    ·
                      refine ⟨3440631040919861585821985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175016109119630895525293 3440631040919861585821985)
                      ·
                        rfl

theorem cell23_6700605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6700605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700605 prefixEnd_6700605 := by exact prefixLift 6700605
  have htrace : WordTrace (prefixWord ++ tailWord_6700605) baseStart_6700605 baseEnd_6700605 := by
    simpa [prefixWord, tailWord_6700605, baseEnd_6700605] using wordTrace_append hprefix tailTrace_6700605
  have hstable : (prefixWord ++ tailWord_6700605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700605).length < 2 ^ (prefixWord ++ tailWord_6700605).sum := by decide
  have hdescent : baseEnd_6700605 < baseStart_6700605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700624 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_6700624 : Nat := 118140960795 + 6700624 * 2 ^ 59
def prefixEnd_6700624 : Nat := 4983230072969 + 3 ^ 40 * 6700624 * 2
def baseEnd_6700624 : Nat := 3440640797052297011484397

theorem tailTrace_6700624 : CollatzResearch.WordTrace tailWord_6700624 prefixEnd_6700624 3440640797052297011484397 := by
  unfold tailWord_6700624
  simp only [CollatzResearch.WordTrace]
  refine ⟨122195917438395549157962463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162927889917860732210616617 122195917438395549157962463)
  ·
    refine ⟨183293876157593323736943695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122195917438395549157962463 183293876157593323736943695)
    ·
      refine ⟨274940814236389985605415543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183293876157593323736943695 274940814236389985605415543)
      ·
        refine ⟨412411221354584978408123315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274940814236389985605415543 412411221354584978408123315)
        ·
          refine ⟨618616832031877467612184973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412411221354584978408123315 618616832031877467612184973)
          ·
            refine ⟨231981312011954050354569365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618616832031877467612184973 231981312011954050354569365)
            ·
              refine ⟨10874124000560346110370439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231981312011954050354569365 10874124000560346110370439)
              ·
                refine ⟨16311186000840519165555659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874124000560346110370439 16311186000840519165555659)
                ·
                  refine ⟨24466779001260778748333489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16311186000840519165555659 24466779001260778748333489)
                  ·
                    refine ⟨18350084250945584061250117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24466779001260778748333489 18350084250945584061250117)
                    ·
                      refine ⟨3440640797052297011484397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18350084250945584061250117 3440640797052297011484397)
                      ·
                        rfl

theorem cell23_6700624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_6700624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700624 prefixEnd_6700624 := by exact prefixLift 6700624
  have htrace : WordTrace (prefixWord ++ tailWord_6700624) baseStart_6700624 baseEnd_6700624 := by
    simpa [prefixWord, tailWord_6700624, baseEnd_6700624] using wordTrace_append hprefix tailTrace_6700624
  have hstable : (prefixWord ++ tailWord_6700624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700624).length < 2 ^ (prefixWord ++ tailWord_6700624).sum := by decide
  have hdescent : baseEnd_6700624 < baseStart_6700624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700628 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_6700628 : Nat := 118140960795 + 6700628 * 2 ^ 59
def prefixEnd_6700628 : Nat := 4983230072969 + 3 ^ 40 * 6700628 * 2
def baseEnd_6700628 : Nat := 3440642850974914995834379

theorem tailTrace_6700628 : CollatzResearch.WordTrace tailWord_6700628 prefixEnd_6700628 3440642850974914995834379 := by
  unfold tailWord_6700628
  simp only [CollatzResearch.WordTrace]
  refine ⟨122195990384388303499535269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162927987179184404666047025 122195990384388303499535269)
  ·
    refine ⟨22911748197072806906162863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122195990384388303499535269 22911748197072806906162863)
    ·
      refine ⟨34367622295609210359244295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911748197072806906162863 34367622295609210359244295)
      ·
        refine ⟨51551433443413815538866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34367622295609210359244295 51551433443413815538866443)
        ·
          refine ⟨77327150165120723308299665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51551433443413815538866443 77327150165120723308299665)
          ·
            refine ⟨57995362623840542481224749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77327150165120723308299665 57995362623840542481224749)
            ·
              refine ⟨21748260983940203430459281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57995362623840542481224749 21748260983940203430459281)
              ·
                refine ⟨16311195737955152572844461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21748260983940203430459281 16311195737955152572844461)
                ·
                  refine ⟨6116698401733182214816673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16311195737955152572844461 6116698401733182214816673)
                  ·
                    refine ⟨4587523801299886661112505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116698401733182214816673 4587523801299886661112505)
                    ·
                      refine ⟨3440642850974914995834379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587523801299886661112505 3440642850974914995834379)
                      ·
                        rfl

theorem cell23_6700628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_6700628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700628 prefixEnd_6700628 := by exact prefixLift 6700628
  have htrace : WordTrace (prefixWord ++ tailWord_6700628) baseStart_6700628 baseEnd_6700628 := by
    simpa [prefixWord, tailWord_6700628, baseEnd_6700628] using wordTrace_append hprefix tailTrace_6700628
  have hstable : (prefixWord ++ tailWord_6700628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700628).length < 2 ^ (prefixWord ++ tailWord_6700628).sum := by decide
  have hdescent : baseEnd_6700628 < baseStart_6700628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700645 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_6700645 : Nat := 118140960795 + 6700645 * 2 ^ 59
def prefixEnd_6700645 : Nat := 4983230072969 + 3 ^ 40 * 6700645 * 2
def baseEnd_6700645 : Nat := 3440651580146041429321801

theorem tailTrace_6700645 : CollatzResearch.WordTrace tailWord_6700645 prefixEnd_6700645 3440651580146041429321801 := by
  unfold tailWord_6700645
  simp only [CollatzResearch.WordTrace]
  refine ⟨244392600809715018902439389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162928400539810012601626259 244392600809715018902439389)
  ·
    refine ⟨91647225303643132088414771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244392600809715018902439389 91647225303643132088414771)
    ·
      refine ⟨137470837955464698132622157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91647225303643132088414771 137470837955464698132622157)
      ·
        refine ⟨51551564233299261799733309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137470837955464698132622157 51551564233299261799733309)
        ·
          refine ⟨19331836587487223174899991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51551564233299261799733309 19331836587487223174899991)
          ·
            refine ⟨28997754881230834762349987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331836587487223174899991 28997754881230834762349987)
            ·
              refine ⟨43496632321846252143524981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28997754881230834762349987 43496632321846252143524981)
              ·
                refine ⟨4077809280173086138455467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43496632321846252143524981 4077809280173086138455467)
                ·
                  refine ⟨6116713920259629207683201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077809280173086138455467 6116713920259629207683201)
                  ·
                    refine ⟨4587535440194721905762401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116713920259629207683201 4587535440194721905762401)
                    ·
                      refine ⟨3440651580146041429321801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587535440194721905762401 3440651580146041429321801)
                      ·
                        rfl

theorem cell23_6700645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_6700645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700645 prefixEnd_6700645 := by exact prefixLift 6700645
  have htrace : WordTrace (prefixWord ++ tailWord_6700645) baseStart_6700645 baseEnd_6700645 := by
    simpa [prefixWord, tailWord_6700645, baseEnd_6700645] using wordTrace_append hprefix tailTrace_6700645
  have hstable : (prefixWord ++ tailWord_6700645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700645).length < 2 ^ (prefixWord ++ tailWord_6700645).sum := by decide
  have hdescent : baseEnd_6700645 < baseStart_6700645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700648 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6700648 : Nat := 118140960795 + 6700648 * 2 ^ 59
def prefixEnd_6700648 : Nat := 4983230072969 + 3 ^ 40 * 6700648 * 2
def baseEnd_6700648 : Nat := 3440653120588004917584287

theorem tailTrace_6700648 : CollatzResearch.WordTrace tailWord_6700648 prefixEnd_6700648 3440653120588004917584287 := by
  unfold tailWord_6700648
  simp only [CollatzResearch.WordTrace]
  refine ⟨122196355114352075207399299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162928473485802766943199065 122196355114352075207399299)
  ·
    refine ⟨183294532671528112811098949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122196355114352075207399299 183294532671528112811098949)
    ·
      refine ⟨34367724875911521152081053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183294532671528112811098949 34367724875911521152081053)
      ·
        refine ⟨12887896828466820432030395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34367724875911521152081053 12887896828466820432030395)
        ·
          refine ⟨19331845242700230648045593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12887896828466820432030395 19331845242700230648045593)
          ·
            refine ⟨14498883932025172986034195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19331845242700230648045593 14498883932025172986034195)
            ·
              refine ⟨21748325898037759479051293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498883932025172986034195 21748325898037759479051293)
              ·
                refine ⟨8155622211764159804644235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21748325898037759479051293 8155622211764159804644235)
                ·
                  refine ⟨12233433317646239706966353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8155622211764159804644235 12233433317646239706966353)
                  ·
                    refine ⟨9175074988234679780224765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12233433317646239706966353 9175074988234679780224765)
                    ·
                      refine ⟨3440653120588004917584287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175074988234679780224765 3440653120588004917584287)
                      ·
                        rfl

theorem cell23_6700648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6700648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700648 prefixEnd_6700648 := by exact prefixLift 6700648
  have htrace : WordTrace (prefixWord ++ tailWord_6700648) baseStart_6700648 baseEnd_6700648 := by
    simpa [prefixWord, tailWord_6700648, baseEnd_6700648] using wordTrace_append hprefix tailTrace_6700648
  have hstable : (prefixWord ++ tailWord_6700648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700648).length < 2 ^ (prefixWord ++ tailWord_6700648).sum := by decide
  have hdescent : baseEnd_6700648 < baseStart_6700648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700662 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6700662 : Nat := 118140960795 + 6700662 * 2 ^ 59
def prefixEnd_6700662 : Nat := 4983230072969 + 3 ^ 40 * 6700662 * 2
def baseEnd_6700662 : Nat := 3440660309317167862809223

theorem tailTrace_6700662 : CollatzResearch.WordTrace tailWord_6700662 prefixEnd_6700662 3440660309317167862809223 := by
  unfold tailWord_6700662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274576303165839425363015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162928813900435620537205493 15274576303165839425363015)
  ·
    refine ⟨22911864454748759138044523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15274576303165839425363015 22911864454748759138044523)
    ·
      refine ⟨34367796682123138707066785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911864454748759138044523 34367796682123138707066785)
      ·
        refine ⟨25775847511592354030300089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34367796682123138707066785 25775847511592354030300089)
        ·
          refine ⟨19331885633694265522725067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25775847511592354030300089 19331885633694265522725067)
          ·
            refine ⟨28997828450541398284087601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331885633694265522725067 28997828450541398284087601)
            ·
              refine ⟨21748371337906048713065701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28997828450541398284087601 21748371337906048713065701)
              ·
                refine ⟨4077819625857384133699819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21748371337906048713065701 4077819625857384133699819)
                ·
                  refine ⟨6116729438786076200549729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077819625857384133699819 6116729438786076200549729)
                  ·
                    refine ⟨4587547079089557150412297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116729438786076200549729 4587547079089557150412297)
                    ·
                      refine ⟨3440660309317167862809223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587547079089557150412297 3440660309317167862809223)
                      ·
                        rfl

theorem cell23_6700662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6700662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700662 prefixEnd_6700662 := by exact prefixLift 6700662
  have htrace : WordTrace (prefixWord ++ tailWord_6700662) baseStart_6700662 baseEnd_6700662 := by
    simpa [prefixWord, tailWord_6700662, baseEnd_6700662] using wordTrace_append hprefix tailTrace_6700662
  have hstable : (prefixWord ++ tailWord_6700662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700662).length < 2 ^ (prefixWord ++ tailWord_6700662).sum := by decide
  have hdescent : baseEnd_6700662 < baseStart_6700662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700701 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_6700701 : Nat := 118140960795 + 6700701 * 2 ^ 59
def prefixEnd_6700701 : Nat := 4983230072969 + 3 ^ 40 * 6700701 * 2
def baseEnd_6700701 : Nat := 3440680335062693210221543

theorem tailTrace_6700701 : CollatzResearch.WordTrace tailWord_6700701 prefixEnd_6700701 3440680335062693210221543 := by
  unfold tailWord_6700701
  simp only [CollatzResearch.WordTrace]
  refine ⟨244394643297512140466477957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162929762198341426977651971 244394643297512140466477957)
  ·
    refine ⟨45823995618283526337464617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244394643297512140466477957 45823995618283526337464617)
    ·
      refine ⟨34367996713712644753098463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45823995618283526337464617 34367996713712644753098463)
      ·
        refine ⟨51551995070568967129647695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34367996713712644753098463 51551995070568967129647695)
        ·
          refine ⟨77327992605853450694471543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51551995070568967129647695 77327992605853450694471543)
          ·
            refine ⟨115991988908780176041707315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77327992605853450694471543 115991988908780176041707315)
            ·
              refine ⟨173987983363170264062560973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115991988908780176041707315 173987983363170264062560973)
              ·
                refine ⟨65245493761188849023460365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173987983363170264062560973 65245493761188849023460365)
                ·
                  refine ⟨24467060160445818383797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65245493761188849023460365 24467060160445818383797637)
                  ·
                    refine ⟨4587573780083590946962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24467060160445818383797637 4587573780083590946962057)
                    ·
                      refine ⟨3440680335062693210221543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587573780083590946962057 3440680335062693210221543)
                      ·
                        rfl

theorem cell23_6700701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_6700701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700701 prefixEnd_6700701 := by exact prefixLift 6700701
  have htrace : WordTrace (prefixWord ++ tailWord_6700701) baseStart_6700701 baseEnd_6700701 := by
    simpa [prefixWord, tailWord_6700701, baseEnd_6700701] using wordTrace_append hprefix tailTrace_6700701
  have hstable : (prefixWord ++ tailWord_6700701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700701).length < 2 ^ (prefixWord ++ tailWord_6700701).sum := by decide
  have hdescent : baseEnd_6700701 < baseStart_6700701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700704 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_6700704 : Nat := 118140960795 + 6700704 * 2 ^ 59
def prefixEnd_6700704 : Nat := 4983230072969 + 3 ^ 40 * 6700704 * 2
def baseEnd_6700704 : Nat := 3440681875504656698484029

theorem tailTrace_6700704 : CollatzResearch.WordTrace tailWord_6700704 prefixEnd_6700704 3440681875504656698484029 := by
  unfold tailWord_6700704
  simp only [CollatzResearch.WordTrace]
  refine ⟨122197376358250635989418583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162929835144334181319224777 122197376358250635989418583)
  ·
    refine ⟨183296064537375953984127875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122197376358250635989418583 183296064537375953984127875)
    ·
      refine ⟨274944096806063930976191813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183296064537375953984127875 274944096806063930976191813)
      ·
        refine ⟨51552018151136987058035965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274944096806063930976191813 51552018151136987058035965)
        ·
          refine ⟨19332006806676370146763487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51552018151136987058035965 19332006806676370146763487)
          ·
            refine ⟨28998010210014555220145231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19332006806676370146763487 28998010210014555220145231)
            ·
              refine ⟨43497015315021832830217847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28998010210014555220145231 43497015315021832830217847)
              ·
                refine ⟨65245522972532749245326771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43497015315021832830217847 65245522972532749245326771)
                ·
                  refine ⟨97868284458799123867990157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65245522972532749245326771 97868284458799123867990157)
                  ·
                    refine ⟨36700606672049671450496309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97868284458799123867990157 36700606672049671450496309)
                    ·
                      refine ⟨3440681875504656698484029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36700606672049671450496309 3440681875504656698484029)
                      ·
                        rfl

theorem cell23_6700704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_6700704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700704 prefixEnd_6700704 := by exact prefixLift 6700704
  have htrace : WordTrace (prefixWord ++ tailWord_6700704) baseStart_6700704 baseEnd_6700704 := by
    simpa [prefixWord, tailWord_6700704, baseEnd_6700704] using wordTrace_append hprefix tailTrace_6700704
  have hstable : (prefixWord ++ tailWord_6700704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700704).length < 2 ^ (prefixWord ++ tailWord_6700704).sum := by decide
  have hdescent : baseEnd_6700704 < baseStart_6700704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700775 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 5]
def baseStart_6700775 : Nat := 118140960795 + 6700775 * 2 ^ 59
def prefixEnd_6700775 : Nat := 4983230072969 + 3 ^ 40 * 6700775 * 2
def baseEnd_6700775 : Nat := 382302036959013991188467

theorem tailTrace_6700775 : CollatzResearch.WordTrace tailWord_6700775 prefixEnd_6700775 382302036959013991188467 := by
  unfold tailWord_6700775
  simp only [CollatzResearch.WordTrace]
  refine ⟨244397342299244051104671779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162931561532829367403114519 244397342299244051104671779)
  ·
    refine ⟨366596013448866076657007669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244397342299244051104671779 366596013448866076657007669)
    ·
      refine ⟨34368376260831194686594469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366596013448866076657007669 34368376260831194686594469)
      ·
        refine ⟨6444070548905849003736463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34368376260831194686594469 6444070548905849003736463)
        ·
          refine ⟨9666105823358773505604695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444070548905849003736463 9666105823358773505604695)
          ·
            refine ⟨14499158735038160258407043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666105823358773505604695 14499158735038160258407043)
            ·
              refine ⟨21748738102557240387610565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499158735038160258407043 21748738102557240387610565)
              ·
                refine ⟨4077888394229482572676981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21748738102557240387610565 4077888394229482572676981)
                ·
                  refine ⟨382302036959013991188467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4077888394229482572676981 382302036959013991188467)
                  ·
                    rfl

theorem cell23_6700775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 5].length) (baseStart_6700775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700775 prefixEnd_6700775 := by exact prefixLift 6700775
  have htrace : WordTrace (prefixWord ++ tailWord_6700775) baseStart_6700775 baseEnd_6700775 := by
    simpa [prefixWord, tailWord_6700775, baseEnd_6700775] using wordTrace_append hprefix tailTrace_6700775
  have hstable : (prefixWord ++ tailWord_6700775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700775).length < 2 ^ (prefixWord ++ tailWord_6700775).sum := by decide
  have hdescent : baseEnd_6700775 < baseStart_6700775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700781 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6700781 : Nat := 118140960795 + 6700781 * 2 ^ 59
def prefixEnd_6700781 : Nat := 4983230072969 + 3 ^ 40 * 6700781 * 2
def baseEnd_6700781 : Nat := 3440721413515052897221175

theorem tailTrace_6700781 : CollatzResearch.WordTrace tailWord_6700781 prefixEnd_6700781 3440721413515052897221175 := by
  unfold tailWord_6700781
  simp only [CollatzResearch.WordTrace]
  refine ⟨244397561137222314129390197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162931707424814876086260131 244397561137222314129390197)
  ·
    refine ⟨22912271356614591949630331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244397561137222314129390197 22912271356614591949630331)
    ·
      refine ⟨34368407034921887924445497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22912271356614591949630331 34368407034921887924445497)
      ·
        refine ⟨25776305276191415943334123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34368407034921887924445497 25776305276191415943334123)
        ·
          refine ⟨38664457914287123915001185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25776305276191415943334123 38664457914287123915001185)
          ·
            refine ⟨28998343435715342936250889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38664457914287123915001185 28998343435715342936250889)
            ·
              refine ⟨21748757576786507202188167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28998343435715342936250889 21748757576786507202188167)
              ·
                refine ⟨32623136365179760803282251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21748757576786507202188167 32623136365179760803282251)
                ·
                  refine ⟨48934704547769641204923377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32623136365179760803282251 48934704547769641204923377)
                  ·
                    refine ⟨36701028410827230903692533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48934704547769641204923377 36701028410827230903692533)
                    ·
                      refine ⟨3440721413515052897221175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36701028410827230903692533 3440721413515052897221175)
                      ·
                        rfl

theorem cell23_6700781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6700781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700781 prefixEnd_6700781 := by exact prefixLift 6700781
  have htrace : WordTrace (prefixWord ++ tailWord_6700781) baseStart_6700781 baseEnd_6700781 := by
    simpa [prefixWord, tailWord_6700781, baseEnd_6700781] using wordTrace_append hprefix tailTrace_6700781
  have hstable : (prefixWord ++ tailWord_6700781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700781).length < 2 ^ (prefixWord ++ tailWord_6700781).sum := by decide
  have hdescent : baseEnd_6700781 < baseStart_6700781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700791 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_6700791 : Nat := 118140960795 + 6700791 * 2 ^ 59
def prefixEnd_6700791 : Nat := 4983230072969 + 3 ^ 40 * 6700791 * 2
def baseEnd_6700791 : Nat := 3440726548321597858096129

theorem tailTrace_6700791 : CollatzResearch.WordTrace tailWord_6700791 prefixEnd_6700791 3440726548321597858096129 := by
  unfold tailWord_6700791
  simp only [CollatzResearch.WordTrace]
  refine ⟨244397925867186085837254227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162931950578124057224836151 244397925867186085837254227)
  ·
    refine ⟨366596888800779128755881341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244397925867186085837254227 366596888800779128755881341)
    ·
      refine ⟨137473833300292173283455503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366596888800779128755881341 137473833300292173283455503)
      ·
        refine ⟨206210749950438259925183255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137473833300292173283455503 206210749950438259925183255)
        ·
          refine ⟨309316124925657389887774883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206210749950438259925183255 309316124925657389887774883)
          ·
            refine ⟨463974187388486084831662325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309316124925657389887774883 463974187388486084831662325)
            ·
              refine ⟨43497580067670570452968343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 463974187388486084831662325 43497580067670570452968343)
              ·
                refine ⟨65246370101505855679452515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43497580067670570452968343 65246370101505855679452515)
                ·
                  refine ⟨97869555152258783519178773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65246370101505855679452515 97869555152258783519178773)
                  ·
                    refine ⟨4587635397762130477461505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97869555152258783519178773 4587635397762130477461505)
                    ·
                      refine ⟨3440726548321597858096129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587635397762130477461505 3440726548321597858096129)
                      ·
                        rfl

theorem cell23_6700791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_6700791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700791 prefixEnd_6700791 := by exact prefixLift 6700791
  have htrace : WordTrace (prefixWord ++ tailWord_6700791) baseStart_6700791 baseEnd_6700791 := by
    simpa [prefixWord, tailWord_6700791, baseEnd_6700791] using wordTrace_append hprefix tailTrace_6700791
  have hstable : (prefixWord ++ tailWord_6700791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700791).length < 2 ^ (prefixWord ++ tailWord_6700791).sum := by decide
  have hdescent : baseEnd_6700791 < baseStart_6700791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700801 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_6700801 : Nat := 118140960795 + 6700801 * 2 ^ 59
def prefixEnd_6700801 : Nat := 4983230072969 + 3 ^ 40 * 6700801 * 2
def baseEnd_6700801 : Nat := 1146910561042714272990361

theorem tailTrace_6700801 : CollatzResearch.WordTrace tailWord_6700801 prefixEnd_6700801 1146910561042714272990361 := by
  unfold tailWord_6700801
  simp only [CollatzResearch.WordTrace]
  refine ⟨244398290597149857545118257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162932193731433238363412171 244398290597149857545118257)
  ·
    refine ⟨183298717947862393158838693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244398290597149857545118257 183298717947862393158838693)
    ·
      refine ⟨34368509615224198717282255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183298717947862393158838693 34368509615224198717282255)
      ·
        refine ⟨51552764422836298075923383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34368509615224198717282255 51552764422836298075923383)
        ·
          refine ⟨77329146634254447113885075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51552764422836298075923383 77329146634254447113885075)
          ·
            refine ⟨115993719951381670670827613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77329146634254447113885075 115993719951381670670827613)
            ·
              refine ⟨43497644981768126501560355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115993719951381670670827613 43497644981768126501560355)
              ·
                refine ⟨65246467472652189752340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43497644981768126501560355 65246467472652189752340533)
                ·
                  refine ⟨6116856325561142789281925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65246467472652189752340533 6116856325561142789281925)
                  ·
                    refine ⟨1146910561042714272990361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116856325561142789281925 1146910561042714272990361)
                    ·
                      rfl

theorem cell23_6700801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_6700801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700801 prefixEnd_6700801 := by exact prefixLift 6700801
  have htrace : WordTrace (prefixWord ++ tailWord_6700801) baseStart_6700801 baseEnd_6700801 := by
    simpa [prefixWord, tailWord_6700801, baseEnd_6700801] using wordTrace_append hprefix tailTrace_6700801
  have hstable : (prefixWord ++ tailWord_6700801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700801).length < 2 ^ (prefixWord ++ tailWord_6700801).sum := by decide
  have hdescent : baseEnd_6700801 < baseStart_6700801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700885 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6700885 : Nat := 118140960795 + 6700885 * 2 ^ 59
def prefixEnd_6700885 : Nat := 4983230072969 + 3 ^ 40 * 6700885 * 2
def baseEnd_6700885 : Nat := 3440774815503120490320697

theorem tailTrace_6700885 : CollatzResearch.WordTrace tailWord_6700885 prefixEnd_6700885 3440774815503120490320697 := by
  unfold tailWord_6700885
  simp only [CollatzResearch.WordTrace]
  refine ⟨244401354328845539891176109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162934236219230359927450739 244401354328845539891176109)
  ·
    refine ⟨91650507873317077459191041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244401354328845539891176109 91650507873317077459191041)
    ·
      refine ⟨68737880904987808094393281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91650507873317077459191041 68737880904987808094393281)
      ·
        refine ⟨51553410678740856070794961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68737880904987808094393281 51553410678740856070794961)
        ·
          refine ⟨38665058009055642053096221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51553410678740856070794961 38665058009055642053096221)
          ·
            refine ⟨14499396753395865769911083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38665058009055642053096221 14499396753395865769911083)
            ·
              refine ⟨21749095130093798654866625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499396753395865769911083 21749095130093798654866625)
              ·
                refine ⟨16311821347570348991149969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21749095130093798654866625 16311821347570348991149969)
                ·
                  refine ⟨12233866010677761743362477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16311821347570348991149969 12233866010677761743362477)
                  ·
                    refine ⟨4587699754004160653760929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12233866010677761743362477 4587699754004160653760929)
                    ·
                      refine ⟨3440774815503120490320697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587699754004160653760929 3440774815503120490320697)
                      ·
                        rfl

theorem cell23_6700885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6700885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700885 prefixEnd_6700885 := by exact prefixLift 6700885
  have htrace : WordTrace (prefixWord ++ tailWord_6700885) baseStart_6700885 baseEnd_6700885 := by
    simpa [prefixWord, tailWord_6700885, baseEnd_6700885] using wordTrace_append hprefix tailTrace_6700885
  have hstable : (prefixWord ++ tailWord_6700885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700885).length < 2 ^ (prefixWord ++ tailWord_6700885).sum := by decide
  have hdescent : baseEnd_6700885 < baseStart_6700885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700901 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_6700901 : Nat := 118140960795 + 6700901 * 2 ^ 59
def prefixEnd_6700901 : Nat := 4983230072969 + 3 ^ 40 * 6700901 * 2
def baseEnd_6700901 : Nat := 3440783031193592427720623

theorem tailTrace_6700901 : CollatzResearch.WordTrace tailWord_6700901 prefixEnd_6700901 3440783031193592427720623 := by
  unfold tailWord_6700901
  simp only [CollatzResearch.WordTrace]
  refine ⟨244401937896787574623758557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162934625264525049749172371 244401937896787574623758557)
  ·
    refine ⟨91650726711295340483909459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244401937896787574623758557 91650726711295340483909459)
    ·
      refine ⟨137476090066943010725864189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91650726711295340483909459 137476090066943010725864189)
      ·
        refine ⟨51553533775103629022199071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137476090066943010725864189 51553533775103629022199071)
        ·
          refine ⟨77330300662655443533298607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51553533775103629022199071 77330300662655443533298607)
          ·
            refine ⟨115995450993983165299947911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77330300662655443533298607 115995450993983165299947911)
            ·
              refine ⟨173993176490974747949921867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115995450993983165299947911 173993176490974747949921867)
              ·
                refine ⟨260989764736462121924882801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173993176490974747949921867 260989764736462121924882801)
                ·
                  refine ⟨195742323552346591443662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260989764736462121924882801 195742323552346591443662101)
                  ·
                    refine ⟨9175421416516246473921661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195742323552346591443662101 9175421416516246473921661)
                    ·
                      refine ⟨3440783031193592427720623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175421416516246473921661 3440783031193592427720623)
                      ·
                        rfl

theorem cell23_6700901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_6700901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700901 prefixEnd_6700901 := by exact prefixLift 6700901
  have htrace : WordTrace (prefixWord ++ tailWord_6700901) baseStart_6700901 baseEnd_6700901 := by
    simpa [prefixWord, tailWord_6700901, baseEnd_6700901] using wordTrace_append hprefix tailTrace_6700901
  have hstable : (prefixWord ++ tailWord_6700901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700901).length < 2 ^ (prefixWord ++ tailWord_6700901).sum := by decide
  have hdescent : baseEnd_6700901 < baseStart_6700901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700935 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_6700935 : Nat := 118140960795 + 6700935 * 2 ^ 59
def prefixEnd_6700935 : Nat := 4983230072969 + 3 ^ 40 * 6700935 * 2
def baseEnd_6700935 : Nat := 3440800489535845294695467

theorem tailTrace_6700935 : CollatzResearch.WordTrace tailWord_6700935 prefixEnd_6700935 3440800489535845294695467 := by
  unfold tailWord_6700935
  simp only [CollatzResearch.WordTrace]
  refine ⟨244403177978664398430496259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162935451985776265620330839 244403177978664398430496259)
  ·
    refine ⟨366604766967996597645744389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244403177978664398430496259 366604766967996597645744389)
    ·
      refine ⟨68738393806499362058577073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366604766967996597645744389 68738393806499362058577073)
      ·
        refine ⟨51553795354874521543932805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68738393806499362058577073 51553795354874521543932805)
        ·
          refine ⟨9666336629038972789487401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51553795354874521543932805 9666336629038972789487401)
          ·
            refine ⟨7249752471779229592115551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9666336629038972789487401 7249752471779229592115551)
            ·
              refine ⟨10874628707668844388173327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249752471779229592115551 10874628707668844388173327)
              ·
                refine ⟨16311943061503266582259991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874628707668844388173327 16311943061503266582259991)
                ·
                  refine ⟨24467914592254899873389987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16311943061503266582259991 24467914592254899873389987)
                  ·
                    refine ⟨36701871888382349810084981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24467914592254899873389987 36701871888382349810084981)
                    ·
                      refine ⟨3440800489535845294695467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36701871888382349810084981 3440800489535845294695467)
                      ·
                        rfl

theorem cell23_6700935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_6700935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700935 prefixEnd_6700935 := by exact prefixLift 6700935
  have htrace : WordTrace (prefixWord ++ tailWord_6700935) baseStart_6700935 baseEnd_6700935 := by
    simpa [prefixWord, tailWord_6700935, baseEnd_6700935] using wordTrace_append hprefix tailTrace_6700935
  have hstable : (prefixWord ++ tailWord_6700935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700935).length < 2 ^ (prefixWord ++ tailWord_6700935).sum := by decide
  have hdescent : baseEnd_6700935 < baseStart_6700935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700938 : List Nat := [3, 1, 2, 4, 3, 10]
def baseStart_6700938 : Nat := 118140960795 + 6700938 * 2 ^ 59
def prefixEnd_6700938 : Nat := 4983230072969 + 3 ^ 40 * 6700938 * 2
def baseEnd_6700938 : Nat := 14159679135711147254971

theorem tailTrace_6700938 : CollatzResearch.WordTrace tailWord_6700938 prefixEnd_6700938 14159679135711147254971 := by
  unfold tailWord_6700938
  simp only [CollatzResearch.WordTrace]
  refine ⟨61100821849413382485713867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162935524931769019961903645 61100821849413382485713867)
  ·
    refine ⟨91651232774120073728570801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61100821849413382485713867 91651232774120073728570801)
    ·
      refine ⟨68738424580590055296428101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91651232774120073728570801 68738424580590055296428101)
      ·
        refine ⟨12888454608860635368080269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68738424580590055296428101 12888454608860635368080269)
        ·
          refine ⟨4833170478322738263030101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12888454608860635368080269 4833170478322738263030101)
          ·
            refine ⟨14159679135711147254971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4833170478322738263030101 14159679135711147254971)
            ·
              rfl

theorem cell23_6700938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 10].length) (baseStart_6700938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700938 prefixEnd_6700938 := by exact prefixLift 6700938
  have htrace : WordTrace (prefixWord ++ tailWord_6700938) baseStart_6700938 baseEnd_6700938 := by
    simpa [prefixWord, tailWord_6700938, baseEnd_6700938] using wordTrace_append hprefix tailTrace_6700938
  have hstable : (prefixWord ++ tailWord_6700938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700938).length < 2 ^ (prefixWord ++ tailWord_6700938).sum := by decide
  have hdescent : baseEnd_6700938 < baseStart_6700938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700951 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 7]
def baseStart_6700951 : Nat := 118140960795 + 6700951 * 2 ^ 59
def prefixEnd_6700951 : Nat := 4983230072969 + 3 ^ 40 * 6700951 * 2
def baseEnd_6700951 : Nat := 1146936235075439077365131

theorem tailTrace_6700951 : CollatzResearch.WordTrace tailWord_6700951 prefixEnd_6700951 1146936235075439077365131 := by
  unfold tailWord_6700951
  simp only [CollatzResearch.WordTrace]
  refine ⟨244403761546606433163078707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162935841031070955442052471 244403761546606433163078707)
  ·
    refine ⟨366605642319909649744618061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244403761546606433163078707 366605642319909649744618061)
    ·
      refine ⟨137477115869966118654231773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366605642319909649744618061 137477115869966118654231773)
      ·
        refine ⟨51553918451237294495336915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137477115869966118654231773 51553918451237294495336915)
        ·
          refine ⟨77330877676855941743005373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51553918451237294495336915 77330877676855941743005373)
          ·
            refine ⟨28999079128820978153627015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77330877676855941743005373 28999079128820978153627015)
            ·
              refine ⟨43498618693231467230440523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28999079128820978153627015 43498618693231467230440523)
              ·
                refine ⟨65247928039847200845660785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43498618693231467230440523 65247928039847200845660785)
                ·
                  refine ⟨48935946029885400634245589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65247928039847200845660785 48935946029885400634245589)
                  ·
                    refine ⟨1146936235075439077365131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48935946029885400634245589 1146936235075439077365131)
                    ·
                      rfl

theorem cell23_6700951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_6700951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700951 prefixEnd_6700951 := by exact prefixLift 6700951
  have htrace : WordTrace (prefixWord ++ tailWord_6700951) baseStart_6700951 baseEnd_6700951 := by
    simpa [prefixWord, tailWord_6700951, baseEnd_6700951] using wordTrace_append hprefix tailTrace_6700951
  have hstable : (prefixWord ++ tailWord_6700951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700951).length < 2 ^ (prefixWord ++ tailWord_6700951).sum := by decide
  have hdescent : baseEnd_6700951 < baseStart_6700951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700975 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 1, 3, 2]
def baseStart_6700975 : Nat := 118140960795 + 6700975 * 2 ^ 59
def prefixEnd_6700975 : Nat := 4983230072969 + 3 ^ 40 * 6700975 * 2
def baseEnd_6700975 : Nat := 3440821028762025138195283

theorem tailTrace_6700975 : CollatzResearch.WordTrace tailWord_6700975 prefixEnd_6700975 3440821028762025138195283 := by
  unfold tailWord_6700975
  simp only [CollatzResearch.WordTrace]
  refine ⟨244404636898519485261952379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162936424599012990174634919 244404636898519485261952379)
  ·
    refine ⟨366606955347779227892928569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244404636898519485261952379 366606955347779227892928569)
    ·
      refine ⟨274955216510834420919696427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366606955347779227892928569 274955216510834420919696427)
      ·
        refine ⟨412432824766251631379544641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274955216510834420919696427 412432824766251631379544641)
        ·
          refine ⟨309324618574688723534658481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412432824766251631379544641 309324618574688723534658481)
          ·
            refine ⟨231993463931016542650993861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309324618574688723534658481 231993463931016542650993861)
            ·
              refine ⟨43498774487065601747061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231993463931016542650993861 43498774487065601747061349)
              ·
                refine ⟨8156020216324800327574003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43498774487065601747061349 8156020216324800327574003)
                ·
                  refine ⟨12234030324487200491361005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156020216324800327574003 12234030324487200491361005)
                  ·
                    refine ⟨4587761371682700184260377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12234030324487200491361005 4587761371682700184260377)
                    ·
                      refine ⟨3440821028762025138195283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587761371682700184260377 3440821028762025138195283)
                      ·
                        rfl

theorem cell23_6700975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3, 2].length) (baseStart_6700975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700975 prefixEnd_6700975 := by exact prefixLift 6700975
  have htrace : WordTrace (prefixWord ++ tailWord_6700975) baseStart_6700975 baseEnd_6700975 := by
    simpa [prefixWord, tailWord_6700975, baseEnd_6700975] using wordTrace_append hprefix tailTrace_6700975
  have hstable : (prefixWord ++ tailWord_6700975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700975).length < 2 ^ (prefixWord ++ tailWord_6700975).sum := by decide
  have hdescent : baseEnd_6700975 < baseStart_6700975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6700991 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_6700991 : Nat := 118140960795 + 6700991 * 2 ^ 59
def prefixEnd_6700991 : Nat := 4983230072969 + 3 ^ 40 * 6700991 * 2
def baseEnd_6700991 : Nat := 3440829244452497075595209

theorem tailTrace_6700991 : CollatzResearch.WordTrace tailWord_6700991 prefixEnd_6700991 3440829244452497075595209 := by
  unfold tailWord_6700991
  simp only [CollatzResearch.WordTrace]
  refine ⟨244405220466461519994534827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162936813644307679996356551 244405220466461519994534827)
  ·
    refine ⟨366607830699692279991802241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244405220466461519994534827 366607830699692279991802241)
    ·
      refine ⟨274955873024769209993851681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366607830699692279991802241 274955873024769209993851681)
      ·
        refine ⟨206216904768576907495388761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274955873024769209993851681 206216904768576907495388761)
        ·
          refine ⟨154662678576432680621541571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206216904768576907495388761 154662678576432680621541571)
          ·
            refine ⟨231994017864649020932312357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154662678576432680621541571 231994017864649020932312357)
            ·
              refine ⟨43498878349621691424808567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231994017864649020932312357 43498878349621691424808567)
              ·
                refine ⟨65248317524432537137212851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43498878349621691424808567 65248317524432537137212851)
                ·
                  refine ⟨97872476286648805705819277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65248317524432537137212851 97872476286648805705819277)
                  ·
                    refine ⟨36702178607493302139682229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97872476286648805705819277 36702178607493302139682229)
                    ·
                      refine ⟨3440829244452497075595209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36702178607493302139682229 3440829244452497075595209)
                      ·
                        rfl

theorem cell23_6700991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_6700991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6700991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6700991 prefixEnd_6700991 := by exact prefixLift 6700991
  have htrace : WordTrace (prefixWord ++ tailWord_6700991) baseStart_6700991 baseEnd_6700991 := by
    simpa [prefixWord, tailWord_6700991, baseEnd_6700991] using wordTrace_append hprefix tailTrace_6700991
  have hstable : (prefixWord ++ tailWord_6700991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6700991).length < 2 ^ (prefixWord ++ tailWord_6700991).sum := by decide
  have hdescent : baseEnd_6700991 < baseStart_6700991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6700991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701001 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_6701001 : Nat := 118140960795 + 6701001 * 2 ^ 59
def prefixEnd_6701001 : Nat := 4983230072969 + 3 ^ 40 * 6701001 * 2
def baseEnd_6701001 : Nat := 3440834379259042036470163

theorem tailTrace_6701001 : CollatzResearch.WordTrace tailWord_6701001 prefixEnd_6701001 3440834379259042036470163 := by
  unfold tailWord_6701001
  simp only [CollatzResearch.WordTrace]
  refine ⟨244405585196425291702398857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162937056797616861134932571 244405585196425291702398857)
  ·
    refine ⟨183304188897318968776799143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244405585196425291702398857 183304188897318968776799143)
    ·
      refine ⟨274956283345978453165198715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183304188897318968776799143 274956283345978453165198715)
      ·
        refine ⟨412434425018967679747798073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274956283345978453165198715 412434425018967679747798073)
        ·
          refine ⟨309325818764225759810848555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412434425018967679747798073 309325818764225759810848555)
          ·
            refine ⟨463988728146338639716272833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309325818764225759810848555 463988728146338639716272833)
            ·
              refine ⟨347991546109753979787204625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463988728146338639716272833 347991546109753979787204625)
              ·
                refine ⟨260993659582315484840403469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347991546109753979787204625 260993659582315484840403469)
                ·
                  refine ⟨97872622343368306815151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260993659582315484840403469 97872622343368306815151301)
                  ·
                    refine ⟨18351116689381557527840869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97872622343368306815151301 18351116689381557527840869)
                    ·
                      refine ⟨3440834379259042036470163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18351116689381557527840869 3440834379259042036470163)
                      ·
                        rfl

theorem cell23_6701001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_6701001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701001 prefixEnd_6701001 := by exact prefixLift 6701001
  have htrace : WordTrace (prefixWord ++ tailWord_6701001) baseStart_6701001 baseEnd_6701001 := by
    simpa [prefixWord, tailWord_6701001, baseEnd_6701001] using wordTrace_append hprefix tailTrace_6701001
  have hstable : (prefixWord ++ tailWord_6701001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701001).length < 2 ^ (prefixWord ++ tailWord_6701001).sum := by decide
  have hdescent : baseEnd_6701001 < baseStart_6701001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701026 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6701026 : Nat := 118140960795 + 6701026 * 2 ^ 59
def prefixEnd_6701026 : Nat := 4983230072969 + 3 ^ 40 * 6701026 * 2
def baseEnd_6701026 : Nat := 3440847216275404438657549

theorem tailTrace_6701026 : CollatzResearch.WordTrace tailWord_6701026 prefixEnd_6701026 3440847216275404438657549 := by
  unfold tailWord_6701026
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101624255333680243014733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162937664680889813981372621 61101624255333680243014733)
  ·
    refine ⟨22913109095750130091130525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61101624255333680243014733 22913109095750130091130525)
    ·
      refine ⟨8592415910906298784173947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22913109095750130091130525 8592415910906298784173947)
      ·
        refine ⟨12888623866359448176260921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592415910906298784173947 12888623866359448176260921)
        ·
          refine ⟨9666467899769586132195691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12888623866359448176260921 9666467899769586132195691)
          ·
            refine ⟨14499701849654379198293537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666467899769586132195691 14499701849654379198293537)
            ·
              refine ⟨10874776387240784398720153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14499701849654379198293537 10874776387240784398720153)
              ·
                refine ⟨8156082290430588299040115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10874776387240784398720153 8156082290430588299040115)
                ·
                  refine ⟨12234123435645882448560173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156082290430588299040115 12234123435645882448560173)
                  ·
                    refine ⟨4587796288367205918210065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12234123435645882448560173 4587796288367205918210065)
                    ·
                      refine ⟨3440847216275404438657549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587796288367205918210065 3440847216275404438657549)
                      ·
                        rfl

theorem cell23_6701026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6701026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701026 prefixEnd_6701026 := by exact prefixLift 6701026
  have htrace : WordTrace (prefixWord ++ tailWord_6701026) baseStart_6701026 baseEnd_6701026 := by
    simpa [prefixWord, tailWord_6701026, baseEnd_6701026] using wordTrace_append hprefix tailTrace_6701026
  have hstable : (prefixWord ++ tailWord_6701026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701026).length < 2 ^ (prefixWord ++ tailWord_6701026).sum := by decide
  have hdescent : baseEnd_6701026 < baseStart_6701026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701068 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6701068 : Nat := 118140960795 + 6701068 * 2 ^ 59
def prefixEnd_6701068 : Nat := 4983230072969 + 3 ^ 40 * 6701068 * 2
def baseEnd_6701068 : Nat := 3440868782462893274332355

theorem tailTrace_6701068 : CollatzResearch.WordTrace tailWord_6701068 prefixEnd_6701068 3440868782462893274332355 := by
  unfold tailWord_6701068
  simp only [CollatzResearch.WordTrace]
  refine ⟨122204014443591281072543929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162938685924788374763391905 122204014443591281072543929)
  ·
    refine ⟨91653010832693460804407947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122204014443591281072543929 91653010832693460804407947)
    ·
      refine ⟨137479516249040191206611921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91653010832693460804407947 137479516249040191206611921)
      ·
        refine ⟨103109637186780143404958941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137479516249040191206611921 103109637186780143404958941)
        ·
          refine ⟨38666113945042553776859603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103109637186780143404958941 38666113945042553776859603)
          ·
            refine ⟨57999170917563830665289405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38666113945042553776859603 57999170917563830665289405)
            ·
              refine ⟨21749689094086436499483527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57999170917563830665289405 21749689094086436499483527)
              ·
                refine ⟨32624533641129654749225291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21749689094086436499483527 32624533641129654749225291)
                ·
                  refine ⟨48936800461694482123837937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32624533641129654749225291 48936800461694482123837937)
                  ·
                    refine ⟨36702600346270861592878453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48936800461694482123837937 36702600346270861592878453)
                    ·
                      refine ⟨3440868782462893274332355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36702600346270861592878453 3440868782462893274332355)
                      ·
                        rfl

theorem cell23_6701068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6701068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701068 prefixEnd_6701068 := by exact prefixLift 6701068
  have htrace : WordTrace (prefixWord ++ tailWord_6701068) baseStart_6701068 baseEnd_6701068 := by
    simpa [prefixWord, tailWord_6701068, baseEnd_6701068] using wordTrace_append hprefix tailTrace_6701068
  have hstable : (prefixWord ++ tailWord_6701068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701068).length < 2 ^ (prefixWord ++ tailWord_6701068).sum := by decide
  have hdescent : baseEnd_6701068 < baseStart_6701068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701092 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_6701092 : Nat := 118140960795 + 6701092 * 2 ^ 59
def prefixEnd_6701092 : Nat := 4983230072969 + 3 ^ 40 * 6701092 * 2
def baseEnd_6701092 : Nat := 1146960368666200393477415

theorem tailTrace_6701092 : CollatzResearch.WordTrace tailWord_6701092 prefixEnd_6701092 1146960368666200393477415 := by
  unfold tailWord_6701092
  simp only [CollatzResearch.WordTrace]
  refine ⟨122204452119547807121980765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162939269492730409495974353 122204452119547807121980765)
  ·
    refine ⟨45826669544830427670742787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122204452119547807121980765 45826669544830427670742787)
    ·
      refine ⟨68740004317245641506114181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45826669544830427670742787 68740004317245641506114181)
      ·
        refine ⟨12888750809483557782396409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68740004317245641506114181 12888750809483557782396409)
        ·
          refine ⟨9666563107112668336797307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12888750809483557782396409 9666563107112668336797307)
          ·
            refine ⟨14499844660669002505195961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666563107112668336797307 14499844660669002505195961)
            ·
              refine ⟨10874883495501751878896971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14499844660669002505195961 10874883495501751878896971)
              ·
                refine ⟨16312325243252627818345457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874883495501751878896971 16312325243252627818345457)
                ·
                  refine ⟨12234243932439470863759093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16312325243252627818345457 12234243932439470863759093)
                  ·
                    refine ⟨1146960368666200393477415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12234243932439470863759093 1146960368666200393477415)
                    ·
                      rfl

theorem cell23_6701092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_6701092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701092 prefixEnd_6701092 := by exact prefixLift 6701092
  have htrace : WordTrace (prefixWord ++ tailWord_6701092) baseStart_6701092 baseEnd_6701092 := by
    simpa [prefixWord, tailWord_6701092, baseEnd_6701092] using wordTrace_append hprefix tailTrace_6701092
  have hstable : (prefixWord ++ tailWord_6701092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701092).length < 2 ^ (prefixWord ++ tailWord_6701092).sum := by decide
  have hdescent : baseEnd_6701092 < baseStart_6701092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701149 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6701149 : Nat := 118140960795 + 6701149 * 2 ^ 59
def prefixEnd_6701149 : Nat := 4983230072969 + 3 ^ 40 * 6701149 * 2
def baseEnd_6701149 : Nat := 3440910374395907457419483

theorem tailTrace_6701149 : CollatzResearch.WordTrace tailWord_6701149 prefixEnd_6701149 3440910374395907457419483 := by
  unfold tailWord_6701149
  simp only [CollatzResearch.WordTrace]
  refine ⟨244410983199889112978786501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162940655466592741985857667 244410983199889112978786501)
  ·
    refine ⟨45827059349979208683522469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244410983199889112978786501 45827059349979208683522469)
    ·
      refine ⟨8592573628121101628160463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45827059349979208683522469 8592573628121101628160463)
      ·
        refine ⟨12888860442181652442240695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592573628121101628160463 12888860442181652442240695)
        ·
          refine ⟨19333290663272478663361043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12888860442181652442240695 19333290663272478663361043)
          ·
            refine ⟨28999935994908717995041565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19333290663272478663361043 28999935994908717995041565)
            ·
              refine ⟨10874975998090769248140587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28999935994908717995041565 10874975998090769248140587)
              ·
                refine ⟨16312463997136153872210881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874975998090769248140587 16312463997136153872210881)
                ·
                  refine ⟨12234347997852115404158161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16312463997136153872210881 12234347997852115404158161)
                  ·
                    refine ⟨9175760998389086553118621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12234347997852115404158161 9175760998389086553118621)
                    ·
                      refine ⟨3440910374395907457419483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175760998389086553118621 3440910374395907457419483)
                      ·
                        rfl

theorem cell23_6701149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6701149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701149 prefixEnd_6701149 := by exact prefixLift 6701149
  have htrace : WordTrace (prefixWord ++ tailWord_6701149) baseStart_6701149 baseEnd_6701149 := by
    simpa [prefixWord, tailWord_6701149, baseEnd_6701149] using wordTrace_append hprefix tailTrace_6701149
  have hstable : (prefixWord ++ tailWord_6701149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701149).length < 2 ^ (prefixWord ++ tailWord_6701149).sum := by decide
  have hdescent : baseEnd_6701149 < baseStart_6701149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701202 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6701202 : Nat := 118140960795 + 6701202 * 2 ^ 59
def prefixEnd_6701202 : Nat := 4983230072969 + 3 ^ 40 * 6701202 * 2
def baseEnd_6701202 : Nat := 3440937588870595750056739

theorem tailTrace_6701202 : CollatzResearch.WordTrace tailWord_6701202 prefixEnd_6701202 3440937588870595750056739 := by
  unfold tailWord_6701202
  simp only [CollatzResearch.WordTrace]
  refine ⟨61103229067174275757616465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162941944179131402020310573 61103229067174275757616465)
  ·
    refine ⟨45827421800380706818212349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61103229067174275757616465 45827421800380706818212349)
    ·
      refine ⟨17185283175142765056829631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45827421800380706818212349 17185283175142765056829631)
      ·
        refine ⟨25777924762714147585244447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17185283175142765056829631 25777924762714147585244447)
        ·
          refine ⟨38666887144071221377866671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25777924762714147585244447 38666887144071221377866671)
          ·
            refine ⟨58000330716106832066800007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38666887144071221377866671 58000330716106832066800007)
            ·
              refine ⟨87000496074160248100200011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58000330716106832066800007 87000496074160248100200011)
              ·
                refine ⟨130500744111240372150300017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87000496074160248100200011 130500744111240372150300017)
                ·
                  refine ⟨97875558083430279112725013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130500744111240372150300017 97875558083430279112725013)
                  ·
                    refine ⟨4587916785160794333408985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97875558083430279112725013 4587916785160794333408985)
                    ·
                      refine ⟨3440937588870595750056739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587916785160794333408985 3440937588870595750056739)
                      ·
                        rfl

theorem cell23_6701202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6701202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701202 prefixEnd_6701202 := by exact prefixLift 6701202
  have htrace : WordTrace (prefixWord ++ tailWord_6701202) baseStart_6701202 baseEnd_6701202 := by
    simpa [prefixWord, tailWord_6701202, baseEnd_6701202] using wordTrace_append hprefix tailTrace_6701202
  have hstable : (prefixWord ++ tailWord_6701202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701202).length < 2 ^ (prefixWord ++ tailWord_6701202).sum := by decide
  have hdescent : baseEnd_6701202 < baseStart_6701202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701230 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6701230 : Nat := 118140960795 + 6701230 * 2 ^ 59
def prefixEnd_6701230 : Nat := 4983230072969 + 3 ^ 40 * 6701230 * 2
def baseEnd_6701230 : Nat := 3440951966328921640506611

theorem tailTrace_6701230 : CollatzResearch.WordTrace tailWord_6701230 prefixEnd_6701230 3440951966328921640506611 := by
  unfold tailWord_6701230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551742189074457976560643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162942625008397109208323429 30551742189074457976560643)
  ·
    refine ⟨45827613283611686964840965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30551742189074457976560643 45827613283611686964840965)
    ·
      refine ⟨8592677490677191305907681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45827613283611686964840965 8592677490677191305907681)
      ·
        refine ⟨6444508118007893479430761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8592677490677191305907681 6444508118007893479430761)
        ·
          refine ⟨4833381088505920109573071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6444508118007893479430761 4833381088505920109573071)
          ·
            refine ⟨7250071632758880164359607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833381088505920109573071 7250071632758880164359607)
            ·
              refine ⟨10875107449138320246539411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250071632758880164359607 10875107449138320246539411)
              ·
                refine ⟨16312661173707480369809117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10875107449138320246539411 16312661173707480369809117)
                ·
                  refine ⟨6117247940140305138678419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16312661173707480369809117 6117247940140305138678419)
                  ·
                    refine ⟨9175871910210457708017629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6117247940140305138678419 9175871910210457708017629)
                    ·
                      refine ⟨3440951966328921640506611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175871910210457708017629 3440951966328921640506611)
                      ·
                        rfl

theorem cell23_6701230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6701230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701230 prefixEnd_6701230 := by exact prefixLift 6701230
  have htrace : WordTrace (prefixWord ++ tailWord_6701230) baseStart_6701230 baseEnd_6701230 := by
    simpa [prefixWord, tailWord_6701230, baseEnd_6701230] using wordTrace_append hprefix tailTrace_6701230
  have hstable : (prefixWord ++ tailWord_6701230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701230).length < 2 ^ (prefixWord ++ tailWord_6701230).sum := by decide
  have hdescent : baseEnd_6701230 < baseStart_6701230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701269 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6701269 : Nat := 118140960795 + 6701269 * 2 ^ 59
def prefixEnd_6701269 : Nat := 4983230072969 + 3 ^ 40 * 6701269 * 2
def baseEnd_6701269 : Nat := 3440971992074446987918931

theorem tailTrace_6701269 : CollatzResearch.WordTrace tailWord_6701269 prefixEnd_6701269 3440971992074446987918931 := by
  unfold tailWord_6701269
  simp only [CollatzResearch.WordTrace]
  refine ⟨244415359959454373473154861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162943573306302915648769907 244415359959454373473154861)
  ·
    refine ⟨91655759984795390052433073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244415359959454373473154861 91655759984795390052433073)
    ·
      refine ⟨68741819988596542539324805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91655759984795390052433073 68741819988596542539324805)
      ·
        refine ⟨12889091247861851726123401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68741819988596542539324805 12889091247861851726123401)
        ·
          refine ⟨9666818435896388794592551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12889091247861851726123401 9666818435896388794592551)
          ·
            refine ⟨14500227653844583191888827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666818435896388794592551 14500227653844583191888827)
            ·
              refine ⟨21750341480766874787833241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14500227653844583191888827 21750341480766874787833241)
              ·
                refine ⟨16312756110575156090874931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21750341480766874787833241 16312756110575156090874931)
                ·
                  refine ⟨24469134165862734136312397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16312756110575156090874931 24469134165862734136312397)
                  ·
                    refine ⟨9175925312198525301117149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24469134165862734136312397 9175925312198525301117149)
                    ·
                      refine ⟨3440971992074446987918931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9175925312198525301117149 3440971992074446987918931)
                      ·
                        rfl

theorem cell23_6701269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6701269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701269 prefixEnd_6701269 := by exact prefixLift 6701269
  have htrace : WordTrace (prefixWord ++ tailWord_6701269) baseStart_6701269 baseEnd_6701269 := by
    simpa [prefixWord, tailWord_6701269, baseEnd_6701269] using wordTrace_append hprefix tailTrace_6701269
  have hstable : (prefixWord ++ tailWord_6701269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701269).length < 2 ^ (prefixWord ++ tailWord_6701269).sum := by decide
  have hdescent : baseEnd_6701269 < baseStart_6701269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701292 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_6701292 : Nat := 118140960795 + 6701292 * 2 ^ 59
def prefixEnd_6701292 : Nat := 4983230072969 + 3 ^ 40 * 6701292 * 2
def baseEnd_6701292 : Nat := 3440983802129500397931325

theorem tailTrace_6701292 : CollatzResearch.WordTrace tailWord_6701292 prefixEnd_6701292 3440983802129500397931325 := by
  unfold tailWord_6701292
  simp only [CollatzResearch.WordTrace]
  refine ⟨122208099419185524200621065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162944132558914032267494753 122208099419185524200621065)
  ·
    refine ⟨91656074564389143150465799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122208099419185524200621065 91656074564389143150465799)
    ·
      refine ⟨137484111846583714725698699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91656074564389143150465799 137484111846583714725698699)
      ·
        refine ⟨206226167769875572088548049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137484111846583714725698699 206226167769875572088548049)
        ·
          refine ⟨154669625827406679066411037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206226167769875572088548049 154669625827406679066411037)
          ·
            refine ⟨58001109685277504649904139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154669625827406679066411037 58001109685277504649904139)
            ·
              refine ⟨87001664527916256974856209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58001109685277504649904139 87001664527916256974856209)
              ·
                refine ⟨65251248395937192731142157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87001664527916256974856209 65251248395937192731142157)
                ·
                  refine ⟨24469218148476447274178309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65251248395937192731142157 24469218148476447274178309)
                  ·
                    refine ⟨4587978402839333863908433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24469218148476447274178309 4587978402839333863908433)
                    ·
                      refine ⟨3440983802129500397931325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4587978402839333863908433 3440983802129500397931325)
                      ·
                        rfl

theorem cell23_6701292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_6701292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701292 prefixEnd_6701292 := by exact prefixLift 6701292
  have htrace : WordTrace (prefixWord ++ tailWord_6701292) baseStart_6701292 baseEnd_6701292 := by
    simpa [prefixWord, tailWord_6701292, baseEnd_6701292] using wordTrace_append hprefix tailTrace_6701292
  have hstable : (prefixWord ++ tailWord_6701292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701292).length < 2 ^ (prefixWord ++ tailWord_6701292).sum := by decide
  have hdescent : baseEnd_6701292 < baseStart_6701292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701315 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 7]
def baseStart_6701315 : Nat := 118140960795 + 6701315 * 2 ^ 59
def prefixEnd_6701315 : Nat := 4983230072969 + 3 ^ 40 * 6701315 * 2
def baseEnd_6701315 : Nat := 382332845798283756438191

theorem tailTrace_6701315 : CollatzResearch.WordTrace tailWord_6701315 prefixEnd_6701315 382332845798283756438191 := by
  unfold tailWord_6701315
  simp only [CollatzResearch.WordTrace]
  refine ⟨244417037717287723329329399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162944691811525148886219599 244417037717287723329329399)
  ·
    refine ⟨366625556575931584993994099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244417037717287723329329399 366625556575931584993994099)
    ·
      refine ⟨549938334863897377490991149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366625556575931584993994099 549938334863897377490991149)
      ·
        refine ⟨206226875573961516559121681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549938334863897377490991149 206226875573961516559121681)
        ·
          refine ⟨154670156680471137419341261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206226875573961516559121681 154670156680471137419341261)
          ·
            refine ⟨58001308755176676532252973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154670156680471137419341261 58001308755176676532252973)
            ·
              refine ⟨21750490783191253699594865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58001308755176676532252973 21750490783191253699594865)
              ·
                refine ⟨16312868087393440274696149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21750490783191253699594865 16312868087393440274696149)
                ·
                  refine ⟨382332845798283756438191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16312868087393440274696149 382332845798283756438191)
                  ·
                    rfl

theorem cell23_6701315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 7].length) (baseStart_6701315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701315 prefixEnd_6701315 := by exact prefixLift 6701315
  have htrace : WordTrace (prefixWord ++ tailWord_6701315) baseStart_6701315 baseEnd_6701315 := by
    simpa [prefixWord, tailWord_6701315, baseEnd_6701315] using wordTrace_append hprefix tailTrace_6701315
  have hstable : (prefixWord ++ tailWord_6701315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701315).length < 2 ^ (prefixWord ++ tailWord_6701315).sum := by decide
  have hdescent : baseEnd_6701315 < baseStart_6701315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701343 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 2, 2, 2]
def baseStart_6701343 : Nat := 118140960795 + 6701343 * 2 ^ 59
def prefixEnd_6701343 : Nat := 4983230072969 + 3 ^ 40 * 6701343 * 2
def baseEnd_6701343 : Nat := 3441009989642879698393591

theorem tailTrace_6701343 : CollatzResearch.WordTrace tailWord_6701343 prefixEnd_6701343 3441009989642879698393591 := by
  unfold tailWord_6701343
  simp only [CollatzResearch.WordTrace]
  refine ⟨244418058961186284111348683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162945372640790856074232455 244418058961186284111348683)
  ·
    refine ⟨366627088441779426167023025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244418058961186284111348683 366627088441779426167023025)
    ·
      refine ⟨274970316331334569625267269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366627088441779426167023025 274970316331334569625267269)
      ·
        refine ⟨51556934312125231804737613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274970316331334569625267269 51556934312125231804737613)
        ·
          refine ⟨19333850367046961926776605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51556934312125231804737613 19333850367046961926776605)
          ·
            refine ⟨7250193887642610722541227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19333850367046961926776605 7250193887642610722541227)
            ·
              refine ⟨10875290831463916083811841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250193887642610722541227 10875290831463916083811841)
              ·
                refine ⟨8156468123597937062858881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10875290831463916083811841 8156468123597937062858881)
                ·
                  refine ⟨6117351092698452797144161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8156468123597937062858881 6117351092698452797144161)
                  ·
                    refine ⟨4588013319523839597858121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117351092698452797144161 4588013319523839597858121)
                    ·
                      refine ⟨3441009989642879698393591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588013319523839597858121 3441009989642879698393591)
                      ·
                        rfl

theorem cell23_6701343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_6701343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701343 prefixEnd_6701343 := by exact prefixLift 6701343
  have htrace : WordTrace (prefixWord ++ tailWord_6701343) baseStart_6701343 baseEnd_6701343 := by
    simpa [prefixWord, tailWord_6701343, baseEnd_6701343] using wordTrace_append hprefix tailTrace_6701343
  have hstable : (prefixWord ++ tailWord_6701343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701343).length < 2 ^ (prefixWord ++ tailWord_6701343).sum := by decide
  have hdescent : baseEnd_6701343 < baseStart_6701343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701375 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 8]
def baseStart_6701375 : Nat := 118140960795 + 6701375 * 2 ^ 59
def prefixEnd_6701375 : Nat := 4983230072969 + 3 ^ 40 * 6701375 * 2
def baseEnd_6701375 : Nat := 1147008807007941191064481

theorem tailTrace_6701375 : CollatzResearch.WordTrace tailWord_6701375 prefixEnd_6701375 1147008807007941191064481 := by
  unfold tailWord_6701375
  simp only [CollatzResearch.WordTrace]
  refine ⟨244419226097070353576513579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162946150731380235717675719 244419226097070353576513579)
  ·
    refine ⟨366628839145605530364770369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244419226097070353576513579 366628839145605530364770369)
    ·
      refine ⟨274971629359204147773577777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366628839145605530364770369 274971629359204147773577777)
      ·
        refine ⟨206228722019403110830183333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274971629359204147773577777 206228722019403110830183333)
        ·
          refine ⟨38667885378638083280659375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206228722019403110830183333 38667885378638083280659375)
          ·
            refine ⟨58001828067957124920989063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38667885378638083280659375 58001828067957124920989063)
            ·
              refine ⟨87002742101935687381483595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58001828067957124920989063 87002742101935687381483595)
              ·
                refine ⟨130504113152903531072225393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87002742101935687381483595 130504113152903531072225393)
                ·
                  refine ⟨97878084864677648304169045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130504113152903531072225393 97878084864677648304169045)
                  ·
                    refine ⟨1147008807007941191064481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97878084864677648304169045 1147008807007941191064481)
                    ·
                      rfl

theorem cell23_6701375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_6701375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701375 prefixEnd_6701375 := by exact prefixLift 6701375
  have htrace : WordTrace (prefixWord ++ tailWord_6701375) baseStart_6701375 baseEnd_6701375 := by
    simpa [prefixWord, tailWord_6701375, baseEnd_6701375] using wordTrace_append hprefix tailTrace_6701375
  have hstable : (prefixWord ++ tailWord_6701375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701375).length < 2 ^ (prefixWord ++ tailWord_6701375).sum := by decide
  have hdescent : baseEnd_6701375 < baseStart_6701375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701385 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_6701385 : Nat := 118140960795 + 6701385 * 2 ^ 59
def prefixEnd_6701385 : Nat := 4983230072969 + 3 ^ 40 * 6701385 * 2
def baseEnd_6701385 : Nat := 3441031555830368534068397

theorem tailTrace_6701385 : CollatzResearch.WordTrace tailWord_6701385 prefixEnd_6701385 3441031555830368534068397 := by
  unfold tailWord_6701385
  simp only [CollatzResearch.WordTrace]
  refine ⟨244419590827034125284377609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162946393884689416856251739 244419590827034125284377609)
  ·
    refine ⟨183314693120275593963283207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244419590827034125284377609 183314693120275593963283207)
    ·
      refine ⟨274972039680413390944924811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183314693120275593963283207 274972039680413390944924811)
      ·
        refine ⟨412458059520620086417387217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274972039680413390944924811 412458059520620086417387217)
        ·
          refine ⟨309343544640465064813040413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412458059520620086417387217 309343544640465064813040413)
          ·
            refine ⟨116003829240174399304890155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309343544640465064813040413 116003829240174399304890155)
            ·
              refine ⟨174005743860261598957335233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116003829240174399304890155 174005743860261598957335233)
              ·
                refine ⟨130504307895196199218001425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174005743860261598957335233 130504307895196199218001425)
                ·
                  refine ⟨97878230921397149413501069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130504307895196199218001425 97878230921397149413501069)
                  ·
                    refine ⟨36704336595523931030062901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97878230921397149413501069 36704336595523931030062901)
                    ·
                      refine ⟨3441031555830368534068397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36704336595523931030062901 3441031555830368534068397)
                      ·
                        rfl

theorem cell23_6701385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_6701385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701385 prefixEnd_6701385 := by exact prefixLift 6701385
  have htrace : WordTrace (prefixWord ++ tailWord_6701385) baseStart_6701385 baseEnd_6701385 := by
    simpa [prefixWord, tailWord_6701385, baseEnd_6701385] using wordTrace_append hprefix tailTrace_6701385
  have hstable : (prefixWord ++ tailWord_6701385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701385).length < 2 ^ (prefixWord ++ tailWord_6701385).sum := by decide
  have hdescent : baseEnd_6701385 < baseStart_6701385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701395 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_6701395 : Nat := 118140960795 + 6701395 * 2 ^ 59
def prefixEnd_6701395 : Nat := 4983230072969 + 3 ^ 40 * 6701395 * 2
def baseEnd_6701395 : Nat := 3441036690636913494943351

theorem tailTrace_6701395 : CollatzResearch.WordTrace tailWord_6701395 prefixEnd_6701395 3441036690636913494943351 := by
  unfold tailWord_6701395
  simp only [CollatzResearch.WordTrace]
  refine ⟨244419955556997896992241639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162946637037998597994827759 244419955556997896992241639)
  ·
    refine ⟨366629933335496845488362459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244419955556997896992241639 366629933335496845488362459)
    ·
      refine ⟨549944900003245268232543689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366629933335496845488362459 549944900003245268232543689)
      ·
        refine ⟨412458675002433951174407767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549944900003245268232543689 412458675002433951174407767)
        ·
          refine ⟨618688012503650926761611651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412458675002433951174407767 618688012503650926761611651)
          ·
            refine ⟨928032018755476390142417477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618688012503650926761611651 928032018755476390142417477)
            ·
              refine ⟨174006003516651823151703277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928032018755476390142417477 174006003516651823151703277)
              ·
                refine ⟨65252251318744433681888729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174006003516651823151703277 65252251318744433681888729)
                ·
                  refine ⟨48939188489058325261416547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65252251318744433681888729 48939188489058325261416547)
                  ·
                    refine ⟨73408782733587487892124821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48939188489058325261416547 73408782733587487892124821)
                    ·
                      refine ⟨3441036690636913494943351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73408782733587487892124821 3441036690636913494943351)
                      ·
                        rfl

theorem cell23_6701395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_6701395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701395 prefixEnd_6701395 := by exact prefixLift 6701395
  have htrace : WordTrace (prefixWord ++ tailWord_6701395) baseStart_6701395 baseEnd_6701395 := by
    simpa [prefixWord, tailWord_6701395, baseEnd_6701395] using wordTrace_append hprefix tailTrace_6701395
  have hstable : (prefixWord ++ tailWord_6701395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701395).length < 2 ^ (prefixWord ++ tailWord_6701395).sum := by decide
  have hdescent : baseEnd_6701395 < baseStart_6701395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701489 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6701489 : Nat := 118140960795 + 6701489 * 2 ^ 59
def prefixEnd_6701489 : Nat := 4983230072969 + 3 ^ 40 * 6701489 * 2
def baseEnd_6701489 : Nat := 3441084957818436127167919

theorem tailTrace_6701489 : CollatzResearch.WordTrace tailWord_6701489 prefixEnd_6701489 3441084957818436127167919 := by
  unfold tailWord_6701489
  simp only [CollatzResearch.WordTrace]
  refine ⟨244423384018657351046163521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162948922679104900697442347 244423384018657351046163521)
  ·
    refine ⟨183317538013993013284622641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244423384018657351046163521 183317538013993013284622641)
    ·
      refine ⟨137488153510494759963466981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183317538013993013284622641 137488153510494759963466981)
      ·
        refine ⟨25779028783217767493150059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137488153510494759963466981 25779028783217767493150059)
        ·
          refine ⟨38668543174826651239725089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25779028783217767493150059 38668543174826651239725089)
          ·
            refine ⟨29001407381119988429793817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38668543174826651239725089 29001407381119988429793817)
            ·
              refine ⟨21751055535839991322345363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29001407381119988429793817 21751055535839991322345363)
              ·
                refine ⟨32626583303759986983518045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21751055535839991322345363 32626583303759986983518045)
                ·
                  refine ⟨12234968738909995118819267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32626583303759986983518045 12234968738909995118819267)
                  ·
                    refine ⟨18352453108364992678228901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12234968738909995118819267 18352453108364992678228901)
                    ·
                      refine ⟨3441084957818436127167919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18352453108364992678228901 3441084957818436127167919)
                      ·
                        rfl

theorem cell23_6701489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6701489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701489 prefixEnd_6701489 := by exact prefixLift 6701489
  have htrace : WordTrace (prefixWord ++ tailWord_6701489) baseStart_6701489 baseEnd_6701489 := by
    simpa [prefixWord, tailWord_6701489, baseEnd_6701489] using wordTrace_append hprefix tailTrace_6701489
  have hstable : (prefixWord ++ tailWord_6701489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701489).length < 2 ^ (prefixWord ++ tailWord_6701489).sum := by decide
  have hdescent : baseEnd_6701489 < baseStart_6701489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701500 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6701500 : Nat := 118140960795 + 6701500 * 2 ^ 59
def prefixEnd_6701500 : Nat := 4983230072969 + 3 ^ 40 * 6701500 * 2
def baseEnd_6701500 : Nat := 3441090606105635584130369

theorem tailTrace_6701500 : CollatzResearch.WordTrace tailWord_6701500 prefixEnd_6701500 3441090606105635584130369 := by
  unfold tailWord_6701500
  simp only [CollatzResearch.WordTrace]
  refine ⟨122211892610808749962406977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162949190147744999949875969 122211892610808749962406977)
  ·
    refine ⟨91658919458106562471805233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122211892610808749962406977 91658919458106562471805233)
    ·
      refine ⟨68744189593579921853853925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91658919458106562471805233 68744189593579921853853925)
      ·
        refine ⟨12889535548796235347597611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68744189593579921853853925 12889535548796235347597611)
        ·
          refine ⟨19334303323194353021396417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889535548796235347597611 19334303323194353021396417)
          ·
            refine ⟨14500727492395764766047313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19334303323194353021396417 14500727492395764766047313)
            ·
              refine ⟨10875545619296823574535485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14500727492395764766047313 10875545619296823574535485)
              ·
                refine ⟨4078329607236308840450807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10875545619296823574535485 4078329607236308840450807)
                ·
                  refine ⟨6117494410854463260676211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078329607236308840450807 6117494410854463260676211)
                  ·
                    refine ⟨9176241616281694891014317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6117494410854463260676211 9176241616281694891014317)
                    ·
                      refine ⟨3441090606105635584130369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9176241616281694891014317 3441090606105635584130369)
                      ·
                        rfl

theorem cell23_6701500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6701500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701500 prefixEnd_6701500 := by exact prefixLift 6701500
  have htrace : WordTrace (prefixWord ++ tailWord_6701500) baseStart_6701500 baseEnd_6701500 := by
    simpa [prefixWord, tailWord_6701500, baseEnd_6701500] using wordTrace_append hprefix tailTrace_6701500
  have hstable : (prefixWord ++ tailWord_6701500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701500).length < 2 ^ (prefixWord ++ tailWord_6701500).sum := by decide
  have hdescent : baseEnd_6701500 < baseStart_6701500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701512 : List Nat := [2, 1, 3, 1, 3, 3, 10]
def baseStart_6701512 : Nat := 118140960795 + 6701512 * 2 ^ 59
def prefixEnd_6701512 : Nat := 4983230072969 + 3 ^ 40 * 6701512 * 2
def baseEnd_6701512 : Nat := 42482676146586290582473

theorem tailTrace_6701512 : CollatzResearch.WordTrace tailWord_6701512 prefixEnd_6701512 42482676146586290582473 := by
  unfold tailWord_6701512
  simp only [CollatzResearch.WordTrace]
  refine ⟨122212111448787012987125395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162949481931716017316167193 122212111448787012987125395)
  ·
    refine ⟨183318167173180519480688093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122212111448787012987125395 183318167173180519480688093)
    ·
      refine ⟨68744312689942694805258035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183318167173180519480688093 68744312689942694805258035)
      ·
        refine ⟨103116469034914042207887053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68744312689942694805258035 103116469034914042207887053)
        ·
          refine ⟨38668675888092765827957645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103116469034914042207887053 38668675888092765827957645)
          ·
            refine ⟨14500753458034787185484117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38668675888092765827957645 14500753458034787185484117)
            ·
              refine ⟨42482676146586290582473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14500753458034787185484117 42482676146586290582473)
              ·
                rfl

theorem cell23_6701512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 10].length) (baseStart_6701512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701512 prefixEnd_6701512 := by exact prefixLift 6701512
  have htrace : WordTrace (prefixWord ++ tailWord_6701512) baseStart_6701512 baseEnd_6701512 := by
    simpa [prefixWord, tailWord_6701512, baseEnd_6701512] using wordTrace_append hprefix tailTrace_6701512
  have hstable : (prefixWord ++ tailWord_6701512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701512).length < 2 ^ (prefixWord ++ tailWord_6701512).sum := by decide
  have hdescent : baseEnd_6701512 < baseStart_6701512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701516 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_6701516 : Nat := 118140960795 + 6701516 * 2 ^ 59
def prefixEnd_6701516 : Nat := 4983230072969 + 3 ^ 40 * 6701516 * 2
def baseEnd_6701516 : Nat := 1147032940598702507176765

theorem tailTrace_6701516 : CollatzResearch.WordTrace tailWord_6701516 prefixEnd_6701516 1147032940598702507176765 := by
  unfold tailWord_6701516
  simp only [CollatzResearch.WordTrace]
  refine ⟨122212184394779767328698201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162949579193039689771597601 122212184394779767328698201)
  ·
    refine ⟨91659138296084825496523651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122212184394779767328698201 91659138296084825496523651)
    ·
      refine ⟨137488707444127238244785477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91659138296084825496523651 137488707444127238244785477)
      ·
        refine ⟨25779132645773857170897277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137488707444127238244785477 25779132645773857170897277)
        ·
          refine ⟨9667174742165196439086479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25779132645773857170897277 9667174742165196439086479)
          ·
            refine ⟨14500762113247794658629719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9667174742165196439086479 14500762113247794658629719)
            ·
              refine ⟨21751143169871691987944579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14500762113247794658629719 21751143169871691987944579)
              ·
                refine ⟨32626714754807537981916869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21751143169871691987944579 32626714754807537981916869)
                ·
                  refine ⟨6117509016526413371609413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32626714754807537981916869 6117509016526413371609413)
                  ·
                    refine ⟨1147032940598702507176765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117509016526413371609413 1147032940598702507176765)
                    ·
                      rfl

theorem cell23_6701516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_6701516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701516 prefixEnd_6701516 := by exact prefixLift 6701516
  have htrace : WordTrace (prefixWord ++ tailWord_6701516) baseStart_6701516 baseEnd_6701516 := by
    simpa [prefixWord, tailWord_6701516, baseEnd_6701516] using wordTrace_append hprefix tailTrace_6701516
  have hstable : (prefixWord ++ tailWord_6701516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701516).length < 2 ^ (prefixWord ++ tailWord_6701516).sum := by decide
  have hdescent : baseEnd_6701516 < baseStart_6701516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701526 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6701526 : Nat := 118140960795 + 6701526 * 2 ^ 59
def prefixEnd_6701526 : Nat := 4983230072969 + 3 ^ 40 * 6701526 * 2
def baseEnd_6701526 : Nat := 3441103956602652482405249

theorem tailTrace_6701526 : CollatzResearch.WordTrace tailWord_6701526 prefixEnd_6701526 3441103956602652482405249 := by
  unfold tailWord_6701526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276545844970206647828777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162949822346348870910173621 15276545844970206647828777)
  ·
    refine ⟨11457409383727654985871583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15276545844970206647828777 11457409383727654985871583)
    ·
      refine ⟨17186114075591482478807375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457409383727654985871583 17186114075591482478807375)
      ·
        refine ⟨25779171113387223718211063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186114075591482478807375 25779171113387223718211063)
        ·
          refine ⟨38668756670080835577316595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25779171113387223718211063 38668756670080835577316595)
          ·
            refine ⟨58003135005121253365974893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38668756670080835577316595 58003135005121253365974893)
            ·
              refine ⟨21751175626920470012240585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58003135005121253365974893 21751175626920470012240585)
              ·
                refine ⟨16313381720190352509180439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21751175626920470012240585 16313381720190352509180439)
                ·
                  refine ⟨24470072580285528763770659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16313381720190352509180439 24470072580285528763770659)
                  ·
                    refine ⟨36705108870428293145655989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24470072580285528763770659 36705108870428293145655989)
                    ·
                      refine ⟨3441103956602652482405249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36705108870428293145655989 3441103956602652482405249)
                      ·
                        rfl

theorem cell23_6701526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6701526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701526 prefixEnd_6701526 := by exact prefixLift 6701526
  have htrace : WordTrace (prefixWord ++ tailWord_6701526) baseStart_6701526 baseEnd_6701526 := by
    simpa [prefixWord, tailWord_6701526, baseEnd_6701526] using wordTrace_append hprefix tailTrace_6701526
  have hstable : (prefixWord ++ tailWord_6701526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701526).length < 2 ^ (prefixWord ++ tailWord_6701526).sum := by decide
  have hdescent : baseEnd_6701526 < baseStart_6701526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701533 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6701533 : Nat := 118140960795 + 6701533 * 2 ^ 59
def prefixEnd_6701533 : Nat := 4983230072969 + 3 ^ 40 * 6701533 * 2
def baseEnd_6701533 : Nat := 1147035850322411318339239

theorem tailTrace_6701533 : CollatzResearch.WordTrace tailWord_6701533 prefixEnd_6701533 1147035850322411318339239 := by
  unfold tailWord_6701533
  simp only [CollatzResearch.WordTrace]
  refine ⟨244424988830497946560765253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162949992553665297707176835 244424988830497946560765253)
  ·
    refine ⟨45829685405718364980143485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244424988830497946560765253 45829685405718364980143485)
    ·
      refine ⟨17186132027144386867553807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45829685405718364980143485 17186132027144386867553807)
      ·
        refine ⟨25779198040716580301330711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186132027144386867553807 25779198040716580301330711)
        ·
          refine ⟨38668797061074870451996067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25779198040716580301330711 38668797061074870451996067)
          ·
            refine ⟨58003195591612305677994101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38668797061074870451996067 58003195591612305677994101)
            ·
              refine ⟨5437799586713653657311947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58003195591612305677994101 5437799586713653657311947)
              ·
                refine ⟨8156699380070480485967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437799586713653657311947 8156699380070480485967921)
                ·
                  refine ⟨6117524535052860364475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8156699380070480485967921 6117524535052860364475941)
                  ·
                    refine ⟨1147035850322411318339239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117524535052860364475941 1147035850322411318339239)
                    ·
                      rfl

theorem cell23_6701533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6701533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701533 prefixEnd_6701533 := by exact prefixLift 6701533
  have htrace : WordTrace (prefixWord ++ tailWord_6701533) baseStart_6701533 baseEnd_6701533 := by
    simpa [prefixWord, tailWord_6701533, baseEnd_6701533] using wordTrace_append hprefix tailTrace_6701533
  have hstable : (prefixWord ++ tailWord_6701533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701533).length < 2 ^ (prefixWord ++ tailWord_6701533).sum := by decide
  have hdescent : baseEnd_6701533 < baseStart_6701533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701546 : List Nat := [3, 1, 3, 1, 3, 3, 2, 7]
def baseStart_6701546 : Nat := 118140960795 + 6701546 * 2 ^ 59
def prefixEnd_6701546 : Nat := 4983230072969 + 3 ^ 40 * 6701546 * 2
def baseEnd_6701546 : Nat := 127448675045027496450191

theorem tailTrace_6701546 : CollatzResearch.WordTrace tailWord_6701546 prefixEnd_6701546 127448675045027496450191 := by
  unfold tailWord_6701546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61106365744862712445247123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162950308652967233187325661 61106365744862712445247123)
  ·
    refine ⟨91659548617294068667870685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61106365744862712445247123 91659548617294068667870685)
    ·
      refine ⟨34372330731485275750451507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91659548617294068667870685 34372330731485275750451507)
      ·
        refine ⟨51558496097227913625677261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34372330731485275750451507 51558496097227913625677261)
        ·
          refine ⟨19334436036460467609628973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51558496097227913625677261 19334436036460467609628973)
          ·
            refine ⟨7250413513672675353610865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19334436036460467609628973 7250413513672675353610865)
            ·
              refine ⟨5437810135254506515208149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7250413513672675353610865 5437810135254506515208149)
              ·
                refine ⟨127448675045027496450191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5437810135254506515208149 127448675045027496450191)
                ·
                  rfl

theorem cell23_6701546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_6701546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701546 prefixEnd_6701546 := by exact prefixLift 6701546
  have htrace : WordTrace (prefixWord ++ tailWord_6701546) baseStart_6701546 baseEnd_6701546 := by
    simpa [prefixWord, tailWord_6701546, baseEnd_6701546] using wordTrace_append hprefix tailTrace_6701546
  have hstable : (prefixWord ++ tailWord_6701546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701546).length < 2 ^ (prefixWord ++ tailWord_6701546).sum := by decide
  have hdescent : baseEnd_6701546 < baseStart_6701546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701552 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_6701552 : Nat := 118140960795 + 6701552 * 2 ^ 59
def prefixEnd_6701552 : Nat := 4983230072969 + 3 ^ 40 * 6701552 * 2
def baseEnd_6701552 : Nat := 3441117307099669380680129

theorem tailTrace_6701552 : CollatzResearch.WordTrace tailWord_6701552 prefixEnd_6701552 3441117307099669380680129 := by
  unfold tailWord_6701552
  simp only [CollatzResearch.WordTrace]
  refine ⟨122212840908714556402853455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162950454544952741870471273 122212840908714556402853455)
  ·
    refine ⟨183319261363071834604280183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122212840908714556402853455 183319261363071834604280183)
    ·
      refine ⟨274978892044607751906420275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183319261363071834604280183 274978892044607751906420275)
      ·
        refine ⟨412468338066911627859630413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274978892044607751906420275 412468338066911627859630413)
        ·
          refine ⟨154675626775091860447361405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412468338066911627859630413 154675626775091860447361405)
          ·
            refine ⟨58003360040659447667760527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154675626775091860447361405 58003360040659447667760527)
            ·
              refine ⟨87005040060989171501640791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58003360040659447667760527 87005040060989171501640791)
              ·
                refine ⟨130507560091483757252461187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87005040060989171501640791 130507560091483757252461187)
                ·
                  refine ⟨195761340137225635878691781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130507560091483757252461187 195761340137225635878691781)
                  ·
                    refine ⟨36705251275729806727254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195761340137225635878691781 36705251275729806727254709)
                    ·
                      refine ⟨3441117307099669380680129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36705251275729806727254709 3441117307099669380680129)
                      ·
                        rfl

theorem cell23_6701552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_6701552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701552 prefixEnd_6701552 := by exact prefixLift 6701552
  have htrace : WordTrace (prefixWord ++ tailWord_6701552) baseStart_6701552 baseEnd_6701552 := by
    simpa [prefixWord, tailWord_6701552, baseEnd_6701552] using wordTrace_append hprefix tailTrace_6701552
  have hstable : (prefixWord ++ tailWord_6701552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701552).length < 2 ^ (prefixWord ++ tailWord_6701552).sum := by decide
  have hdescent : baseEnd_6701552 < baseStart_6701552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701574 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6701574 : Nat := 118140960795 + 6701574 * 2 ^ 59
def prefixEnd_6701574 : Nat := 4983230072969 + 3 ^ 40 * 6701574 * 2
def baseEnd_6701574 : Nat := 3441128603674068294605029

theorem tailTrace_6701574 : CollatzResearch.WordTrace tailWord_6701574 prefixEnd_6701574 3441128603674068294605029 := by
  unfold tailWord_6701574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638327631979669080093993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162950989482232940375338517 7638327631979669080093993)
  ·
    refine ⟨5728745723984751810070495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638327631979669080093993 5728745723984751810070495)
    ·
      refine ⟨8593118585977127715105743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728745723984751810070495 8593118585977127715105743)
      ·
        refine ⟨12889677878965691572658615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593118585977127715105743 12889677878965691572658615)
        ·
          refine ⟨19334516818448537358987923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889677878965691572658615 19334516818448537358987923)
          ·
            refine ⟨29001775227672806038481885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19334516818448537358987923 29001775227672806038481885)
            ·
              refine ⟨10875665710377302264430707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29001775227672806038481885 10875665710377302264430707)
              ·
                refine ⟨16313498565565953396646061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10875665710377302264430707 16313498565565953396646061)
                ·
                  refine ⟨6117561962087232523742273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16313498565565953396646061 6117561962087232523742273)
                  ·
                    refine ⟨4588171471565424392806705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117561962087232523742273 4588171471565424392806705)
                    ·
                      refine ⟨3441128603674068294605029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588171471565424392806705 3441128603674068294605029)
                      ·
                        rfl

theorem cell23_6701574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6701574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701574 prefixEnd_6701574 := by exact prefixLift 6701574
  have htrace : WordTrace (prefixWord ++ tailWord_6701574) baseStart_6701574 baseEnd_6701574 := by
    simpa [prefixWord, tailWord_6701574, baseEnd_6701574] using wordTrace_append hprefix tailTrace_6701574
  have hstable : (prefixWord ++ tailWord_6701574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701574).length < 2 ^ (prefixWord ++ tailWord_6701574).sum := by decide
  have hdescent : baseEnd_6701574 < baseStart_6701574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701696 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_6701696 : Nat := 118140960795 + 6701696 * 2 ^ 59
def prefixEnd_6701696 : Nat := 4983230072969 + 3 ^ 40 * 6701696 * 2
def baseEnd_6701696 : Nat := 1147063749437972272426489

theorem tailTrace_6701696 : CollatzResearch.WordTrace tailWord_6701696 prefixEnd_6701696 1147063749437972272426489 := by
  unfold tailWord_6701696
  simp only [CollatzResearch.WordTrace]
  refine ⟨122215466964453712699474471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162953955952604950265965961 122215466964453712699474471)
  ·
    refine ⟨183323200446680569049211707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122215466964453712699474471 183323200446680569049211707)
    ·
      refine ⟨274984800670020853573817561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183323200446680569049211707 274984800670020853573817561)
      ·
        refine ⟨206238600502515640180363171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274984800670020853573817561 206238600502515640180363171)
        ·
          refine ⟨309357900753773460270544757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206238600502515640180363171 309357900753773460270544757)
          ·
            refine ⟨29002303195666261900363571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309357900753773460270544757 29002303195666261900363571)
            ·
              refine ⟨43503454793499392850545357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29002303195666261900363571 43503454793499392850545357)
              ·
                refine ⟨16313795547562272318954509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43503454793499392850545357 16313795547562272318954509)
                ·
                  refine ⟨6117673330335852119607941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16313795547562272318954509 6117673330335852119607941)
                  ·
                    refine ⟨1147063749437972272426489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117673330335852119607941 1147063749437972272426489)
                    ·
                      rfl

theorem cell23_6701696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_6701696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701696 prefixEnd_6701696 := by exact prefixLift 6701696
  have htrace : WordTrace (prefixWord ++ tailWord_6701696) baseStart_6701696 baseEnd_6701696 := by
    simpa [prefixWord, tailWord_6701696, baseEnd_6701696] using wordTrace_append hprefix tailTrace_6701696
  have hstable : (prefixWord ++ tailWord_6701696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701696).length < 2 ^ (prefixWord ++ tailWord_6701696).sum := by decide
  have hdescent : baseEnd_6701696 < baseStart_6701696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701698 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6701698 : Nat := 118140960795 + 6701698 * 2 ^ 59
def prefixEnd_6701698 : Nat := 4983230072969 + 3 ^ 40 * 6701698 * 2
def baseEnd_6701698 : Nat := 3441192275275225809454459

theorem tailTrace_6701698 : CollatzResearch.WordTrace tailWord_6701698 prefixEnd_6701698 3441192275275225809454459 := by
  unfold tailWord_6701698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61107751718725044935130437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162954004583266786493681165 61107751718725044935130437)
  ·
    refine ⟨11457703447260945925336957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61107751718725044935130437 11457703447260945925336957)
    ·
      refine ⟨4296638792722854722001359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11457703447260945925336957 4296638792722854722001359)
      ·
        refine ⟨6444958189084282083002039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296638792722854722001359 6444958189084282083002039)
        ·
          refine ⟨9667437283626423124503059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444958189084282083002039 9667437283626423124503059)
          ·
            refine ⟨14501155925439634686754589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9667437283626423124503059 14501155925439634686754589)
            ·
              refine ⟨5437933472039863007532971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14501155925439634686754589 5437933472039863007532971)
              ·
                refine ⟨8156900208059794511299457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437933472039863007532971 8156900208059794511299457)
                ·
                  refine ⟨6117675156044845883474593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8156900208059794511299457 6117675156044845883474593)
                  ·
                    refine ⟨4588256367033634412605945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117675156044845883474593 4588256367033634412605945)
                    ·
                      refine ⟨3441192275275225809454459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588256367033634412605945 3441192275275225809454459)
                      ·
                        rfl

theorem cell23_6701698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6701698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701698 prefixEnd_6701698 := by exact prefixLift 6701698
  have htrace : WordTrace (prefixWord ++ tailWord_6701698) baseStart_6701698 baseEnd_6701698 := by
    simpa [prefixWord, tailWord_6701698, baseEnd_6701698] using wordTrace_append hprefix tailTrace_6701698
  have hstable : (prefixWord ++ tailWord_6701698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701698).length < 2 ^ (prefixWord ++ tailWord_6701698).sum := by decide
  have hdescent : baseEnd_6701698 < baseStart_6701698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701726 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_6701726 : Nat := 118140960795 + 6701726 * 2 ^ 59
def prefixEnd_6701726 : Nat := 4983230072969 + 3 ^ 40 * 6701726 * 2
def baseEnd_6701726 : Nat := 382356294748172411100481

theorem tailTrace_6701726 : CollatzResearch.WordTrace tailWord_6701726 prefixEnd_6701726 382356294748172411100481 := by
  unfold tailWord_6701726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554003514849842565317629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162954685412532493681694021 30554003514849842565317629)
  ·
    refine ⟨11457751318068690961994111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30554003514849842565317629 11457751318068690961994111)
    ·
      refine ⟨17186626977103036442991167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457751318068690961994111 17186626977103036442991167)
      ·
        refine ⟨25779940465654554664486751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186626977103036442991167 25779940465654554664486751)
        ·
          refine ⟨38669910698481831996730127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25779940465654554664486751 38669910698481831996730127)
          ·
            refine ⟨58004866047722747995095191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38669910698481831996730127 58004866047722747995095191)
            ·
              refine ⟨87007299071584121992642787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58004866047722747995095191 87007299071584121992642787)
              ·
                refine ⟨130510948607376182988964181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87007299071584121992642787 130510948607376182988964181)
                ·
                  refine ⟨382356294748172411100481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130510948607376182988964181 382356294748172411100481)
                  ·
                    rfl

theorem cell23_6701726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_6701726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701726 prefixEnd_6701726 := by exact prefixLift 6701726
  have htrace : WordTrace (prefixWord ++ tailWord_6701726) baseStart_6701726 baseEnd_6701726 := by
    simpa [prefixWord, tailWord_6701726, baseEnd_6701726] using wordTrace_append hprefix tailTrace_6701726
  have hstable : (prefixWord ++ tailWord_6701726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701726).length < 2 ^ (prefixWord ++ tailWord_6701726).sum := by decide
  have hdescent : baseEnd_6701726 < baseStart_6701726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701756 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_6701756 : Nat := 118140960795 + 6701756 * 2 ^ 59
def prefixEnd_6701756 : Nat := 4983230072969 + 3 ^ 40 * 6701756 * 2
def baseEnd_6701756 : Nat := 1147074019051062194176397

theorem tailTrace_6701756 : CollatzResearch.WordTrace tailWord_6701756 prefixEnd_6701756 1147074019051062194176397 := by
  unfold tailWord_6701756
  simp only [CollatzResearch.WordTrace]
  refine ⟨122216561154345027823066561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162955414872460037097422081 122216561154345027823066561)
  ·
    refine ⟨91662420865758770867299921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122216561154345027823066561 91662420865758770867299921)
    ·
      refine ⟨68746815649319078150474941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91662420865758770867299921 68746815649319078150474941)
      ·
        refine ⟨25780055868494654306428103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68746815649319078150474941 25780055868494654306428103)
        ·
          refine ⟨38670083802741981459642155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25780055868494654306428103 38670083802741981459642155)
          ·
            refine ⟨58005125704112972189463233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38670083802741981459642155 58005125704112972189463233)
            ·
              refine ⟨43503844278084729142097425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58005125704112972189463233 43503844278084729142097425)
              ·
                refine ⟨32627883208563546856573069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43503844278084729142097425 32627883208563546856573069)
                ·
                  refine ⟨12235456203211330071214901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32627883208563546856573069 12235456203211330071214901)
                  ·
                    refine ⟨1147074019051062194176397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12235456203211330071214901 1147074019051062194176397)
                    ·
                      rfl

theorem cell23_6701756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_6701756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701756 prefixEnd_6701756 := by exact prefixLift 6701756
  have htrace : WordTrace (prefixWord ++ tailWord_6701756) baseStart_6701756 baseEnd_6701756 := by
    simpa [prefixWord, tailWord_6701756, baseEnd_6701756] using wordTrace_append hprefix tailTrace_6701756
  have hstable : (prefixWord ++ tailWord_6701756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701756).length < 2 ^ (prefixWord ++ tailWord_6701756).sum := by decide
  have hdescent : baseEnd_6701756 < baseStart_6701756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701769 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_6701769 : Nat := 118140960795 + 6701769 * 2 ^ 59
def prefixEnd_6701769 : Nat := 4983230072969 + 3 ^ 40 * 6701769 * 2
def baseEnd_6701769 : Nat := 1147076244133898343888877

theorem tailTrace_6701769 : CollatzResearch.WordTrace tailWord_6701769 prefixEnd_6701769 1147076244133898343888877 := by
  unfold tailWord_6701769
  simp only [CollatzResearch.WordTrace]
  refine ⟨244433596457642958866356361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162955730971761972577570907 244433596457642958866356361)
  ·
    refine ⟨183325197343232219149767271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244433596457642958866356361 183325197343232219149767271)
    ·
      refine ⟨274987796014848328724650907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183325197343232219149767271 274987796014848328724650907)
      ·
        refine ⟨412481694022272493086976361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274987796014848328724650907 412481694022272493086976361)
        ·
          refine ⟨309361270516704369815232271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412481694022272493086976361 309361270516704369815232271)
          ·
            refine ⟨464041905775056554722848407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309361270516704369815232271 464041905775056554722848407)
            ·
              refine ⟨696062858662584832084272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464041905775056554722848407 696062858662584832084272611)
              ·
                refine ⟨1044094287993877248126408917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696062858662584832084272611 1044094287993877248126408917)
                ·
                  refine ⟨24470959874856498002962709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1044094287993877248126408917 24470959874856498002962709)
                  ·
                    refine ⟨1147076244133898343888877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24470959874856498002962709 1147076244133898343888877)
                    ·
                      rfl

theorem cell23_6701769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_6701769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701769 prefixEnd_6701769 := by exact prefixLift 6701769
  have htrace : WordTrace (prefixWord ++ tailWord_6701769) baseStart_6701769 baseEnd_6701769 := by
    simpa [prefixWord, tailWord_6701769, baseEnd_6701769] using wordTrace_append hprefix tailTrace_6701769
  have hstable : (prefixWord ++ tailWord_6701769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701769).length < 2 ^ (prefixWord ++ tailWord_6701769).sum := by decide
  have hdescent : baseEnd_6701769 < baseStart_6701769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701786 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_6701786 : Nat := 118140960795 + 6701786 * 2 ^ 59
def prefixEnd_6701786 : Nat := 4983230072969 + 3 ^ 40 * 6701786 * 2
def baseEnd_6701786 : Nat := 1147079153857607155051351

theorem tailTrace_6701786 : CollatzResearch.WordTrace tailWord_6701786 prefixEnd_6701786 1147079153857607155051351 := by
  unfold tailWord_6701786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61108554124645342692431303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162956144332387580513150141 61108554124645342692431303)
  ·
    refine ⟨91662831186968014038646955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61108554124645342692431303 91662831186968014038646955)
    ·
      refine ⟨137494246780452021057970433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91662831186968014038646955 137494246780452021057970433)
      ·
        refine ⟨103120685085339015793477825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137494246780452021057970433 103120685085339015793477825)
        ·
          refine ⟨77340513814004261845108369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103120685085339015793477825 77340513814004261845108369)
          ·
            refine ⟨58005385360503196383831277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77340513814004261845108369 58005385360503196383831277)
            ·
              refine ⟨21752019510188698643936729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58005385360503196383831277 21752019510188698643936729)
              ·
                refine ⟨16314014632641523982952547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21752019510188698643936729 16314014632641523982952547)
                ·
                  refine ⟨24471021948962285974428821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16314014632641523982952547 24471021948962285974428821)
                  ·
                    refine ⟨1147079153857607155051351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24471021948962285974428821 1147079153857607155051351)
                    ·
                      rfl

theorem cell23_6701786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_6701786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701786 prefixEnd_6701786 := by exact prefixLift 6701786
  have htrace : WordTrace (prefixWord ++ tailWord_6701786) baseStart_6701786 baseEnd_6701786 := by
    simpa [prefixWord, tailWord_6701786, baseEnd_6701786] using wordTrace_append hprefix tailTrace_6701786
  have hstable : (prefixWord ++ tailWord_6701786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701786).length < 2 ^ (prefixWord ++ tailWord_6701786).sum := by decide
  have hdescent : baseEnd_6701786 < baseStart_6701786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701799 : List Nat := [1, 1, 5, 16]
def baseStart_6701799 : Nat := 118140960795 + 6701799 * 2 ^ 59
def prefixEnd_6701799 : Nat := 4983230072969 + 3 ^ 40 * 6701799 * 2
def baseEnd_6701799 : Nat := 1573499833937507962639

theorem tailTrace_6701799 : CollatzResearch.WordTrace tailWord_6701799 prefixEnd_6701799 1573499833937507962639 := by
  unfold tailWord_6701799
  simp only [CollatzResearch.WordTrace]
  refine ⟨244434690647534273989948451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162956460431689515993298967 244434690647534273989948451)
  ·
    refine ⟨366652035971301410984922677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244434690647534273989948451 366652035971301410984922677)
    ·
      refine ⟨34373628372309507279836501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366652035971301410984922677 34373628372309507279836501)
      ·
        refine ⟨1573499833937507962639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 34373628372309507279836501 1573499833937507962639)
        ·
          rfl

theorem cell23_6701799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 16].length) (baseStart_6701799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701799 prefixEnd_6701799 := by exact prefixLift 6701799
  have htrace : WordTrace (prefixWord ++ tailWord_6701799) baseStart_6701799 baseEnd_6701799 := by
    simpa [prefixWord, tailWord_6701799, baseEnd_6701799] using wordTrace_append hprefix tailTrace_6701799
  have hstable : (prefixWord ++ tailWord_6701799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701799).length < 2 ^ (prefixWord ++ tailWord_6701799).sum := by decide
  have hdescent : baseEnd_6701799 < baseStart_6701799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701843 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 3]
def baseStart_6701843 : Nat := 118140960795 + 6701843 * 2 ^ 59
def prefixEnd_6701843 : Nat := 4983230072969 + 3 ^ 40 * 6701843 * 2
def baseEnd_6701843 : Nat := 3441266729970127742141291

theorem tailTrace_6701843 : CollatzResearch.WordTrace tailWord_6701843 prefixEnd_6701843 3441266729970127742141291 := by
  unfold tailWord_6701843
  simp only [CollatzResearch.WordTrace]
  refine ⟨244436295459374869504550183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162957530306249913003033455 244436295459374869504550183)
  ·
    refine ⟨366654443189062304256825275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244436295459374869504550183 366654443189062304256825275)
    ·
      refine ⟨549981664783593456385237913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366654443189062304256825275 549981664783593456385237913)
      ·
        refine ⟨412486248587695092288928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549981664783593456385237913 412486248587695092288928435)
        ·
          refine ⟨618729372881542638433392653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412486248587695092288928435 618729372881542638433392653)
          ·
            refine ⟨232023514830578489412522245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618729372881542638433392653 232023514830578489412522245)
            ·
              refine ⟨43504409030733466764847921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232023514830578489412522245 43504409030733466764847921)
              ·
                refine ⟨32628306773050100073635941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43504409030733466764847921 32628306773050100073635941)
                ·
                  refine ⟨6117807519946893763806739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32628306773050100073635941 6117807519946893763806739)
                  ·
                    refine ⟨9176711279920340645710109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6117807519946893763806739 9176711279920340645710109)
                    ·
                      refine ⟨3441266729970127742141291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9176711279920340645710109 3441266729970127742141291)
                      ·
                        rfl

theorem cell23_6701843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_6701843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701843 prefixEnd_6701843 := by exact prefixLift 6701843
  have htrace : WordTrace (prefixWord ++ tailWord_6701843) baseStart_6701843 baseEnd_6701843 := by
    simpa [prefixWord, tailWord_6701843, baseEnd_6701843] using wordTrace_append hprefix tailTrace_6701843
  have hstable : (prefixWord ++ tailWord_6701843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701843).length < 2 ^ (prefixWord ++ tailWord_6701843).sum := by decide
  have hdescent : baseEnd_6701843 < baseStart_6701843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701887 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 1, 3, 2]
def baseStart_6701887 : Nat := 118140960795 + 6701887 * 2 ^ 59
def prefixEnd_6701887 : Nat := 4983230072969 + 3 ^ 40 * 6701887 * 2
def baseEnd_6701887 : Nat := 3441289323118925569991089

theorem tailTrace_6701887 : CollatzResearch.WordTrace tailWord_6701887 prefixEnd_6701887 3441289323118925569991089 := by
  unfold tailWord_6701887
  simp only [CollatzResearch.WordTrace]
  refine ⟨244437900271215465019151915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162958600180810310012767943 244437900271215465019151915)
  ·
    refine ⟨366656850406823197528727873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244437900271215465019151915 366656850406823197528727873)
    ·
      refine ⟨274992637805117398146545905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366656850406823197528727873 274992637805117398146545905)
      ·
        refine ⟨206244478353838048609909429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274992637805117398146545905 206244478353838048609909429)
        ·
          refine ⟨19335419845672317057179009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206244478353838048609909429 19335419845672317057179009)
          ·
            refine ⟨14501564884254237792884257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19335419845672317057179009 14501564884254237792884257)
            ·
              refine ⟨10876173663190678344663193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14501564884254237792884257 10876173663190678344663193)
              ·
                refine ⟨8157130247393008758497395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10876173663190678344663193 8157130247393008758497395)
                ·
                  refine ⟨12235695371089513137746093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157130247393008758497395 12235695371089513137746093)
                  ·
                    refine ⟨4588385764158567426654785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12235695371089513137746093 4588385764158567426654785)
                    ·
                      refine ⟨3441289323118925569991089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588385764158567426654785 3441289323118925569991089)
                      ·
                        rfl

theorem cell23_6701887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_6701887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701887 prefixEnd_6701887 := by exact prefixLift 6701887
  have htrace : WordTrace (prefixWord ++ tailWord_6701887) baseStart_6701887 baseEnd_6701887 := by
    simpa [prefixWord, tailWord_6701887, baseEnd_6701887] using wordTrace_append hprefix tailTrace_6701887
  have hstable : (prefixWord ++ tailWord_6701887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701887).length < 2 ^ (prefixWord ++ tailWord_6701887).sum := by decide
  have hdescent : baseEnd_6701887 < baseStart_6701887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701923 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 7]
def baseStart_6701923 : Nat := 118140960795 + 6701923 * 2 ^ 59
def prefixEnd_6701923 : Nat := 4983230072969 + 3 ^ 40 * 6701923 * 2
def baseEnd_6701923 : Nat := 382367534269165269904547

theorem tailTrace_6701923 : CollatzResearch.WordTrace tailWord_6701923 prefixEnd_6701923 382367534269165269904547 := by
  unfold tailWord_6701923
  simp only [CollatzResearch.WordTrace]
  refine ⟨244439213299085043167462423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162959475532723362111641615 244439213299085043167462423)
  ·
    refine ⟨366658819948627564751193635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244439213299085043167462423 366658819948627564751193635)
    ·
      refine ⟨549988229922941347126790453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366658819948627564751193635 549988229922941347126790453)
      ·
        refine ⟨51561396555275751293136605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 549988229922941347126790453 51561396555275751293136605)
        ·
          refine ⟨19335523708228406734926227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51561396555275751293136605 19335523708228406734926227)
          ·
            refine ⟨29003285562342610102389341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335523708228406734926227 29003285562342610102389341)
            ·
              refine ⟨10876232085878478788396003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29003285562342610102389341 10876232085878478788396003)
              ·
                refine ⟨16314348128817718182594005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876232085878478788396003 16314348128817718182594005)
                ·
                  refine ⟨382367534269165269904547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16314348128817718182594005 382367534269165269904547)
                  ·
                    rfl

theorem cell23_6701923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 7].length) (baseStart_6701923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701923 prefixEnd_6701923 := by exact prefixLift 6701923
  have htrace : WordTrace (prefixWord ++ tailWord_6701923) baseStart_6701923 baseEnd_6701923 := by
    simpa [prefixWord, tailWord_6701923, baseEnd_6701923] using wordTrace_append hprefix tailTrace_6701923
  have hstable : (prefixWord ++ tailWord_6701923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701923).length < 2 ^ (prefixWord ++ tailWord_6701923).sum := by decide
  have hdescent : baseEnd_6701923 < baseStart_6701923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701933 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6701933 : Nat := 118140960795 + 6701933 * 2 ^ 59
def prefixEnd_6701933 : Nat := 4983230072969 + 3 ^ 40 * 6701933 * 2
def baseEnd_6701933 : Nat := 3441312943229032390015877

theorem tailTrace_6701933 : CollatzResearch.WordTrace tailWord_6701933 prefixEnd_6701933 3441312943229032390015877 := by
  unfold tailWord_6701933
  simp only [CollatzResearch.WordTrace]
  refine ⟨244439578029048814875326453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162959718686032543250217635 244439578029048814875326453)
  ·
    refine ⟨22916210440223326394561855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244439578029048814875326453 22916210440223326394561855)
    ·
      refine ⟨34374315660334989591842783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22916210440223326394561855 34374315660334989591842783)
      ·
        refine ⟨51561473490502484387764175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34374315660334989591842783 51561473490502484387764175)
        ·
          refine ⟨77342210235753726581646263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51561473490502484387764175 77342210235753726581646263)
          ·
            refine ⟨116013315353630589872469395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77342210235753726581646263 116013315353630589872469395)
            ·
              refine ⟨174019973030445884808704093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116013315353630589872469395 174019973030445884808704093)
              ·
                refine ⟨65257489886417206803264035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174019973030445884808704093 65257489886417206803264035)
                ·
                  refine ⟨97886234829625810204896053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65257489886417206803264035 97886234829625810204896053)
                  ·
                    refine ⟨9176834515277419706709005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97886234829625810204896053 9176834515277419706709005)
                    ·
                      refine ⟨3441312943229032390015877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9176834515277419706709005 3441312943229032390015877)
                      ·
                        rfl

theorem cell23_6701933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6701933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701933 prefixEnd_6701933 := by exact prefixLift 6701933
  have htrace : WordTrace (prefixWord ++ tailWord_6701933) baseStart_6701933 baseEnd_6701933 := by
    simpa [prefixWord, tailWord_6701933, baseEnd_6701933] using wordTrace_append hprefix tailTrace_6701933
  have hstable : (prefixWord ++ tailWord_6701933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701933).length < 2 ^ (prefixWord ++ tailWord_6701933).sum := by decide
  have hdescent : baseEnd_6701933 < baseStart_6701933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701936 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_6701936 : Nat := 118140960795 + 6701936 * 2 ^ 59
def prefixEnd_6701936 : Nat := 4983230072969 + 3 ^ 40 * 6701936 * 2
def baseEnd_6701936 : Nat := 1147104827890331959426121

theorem tailTrace_6701936 : CollatzResearch.WordTrace tailWord_6701936 prefixEnd_6701936 1147104827890331959426121 := by
  unfold tailWord_6701936
  simp only [CollatzResearch.WordTrace]
  refine ⟨122219843724018973193842831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162959791632025297591790441 122219843724018973193842831)
  ·
    refine ⟨183329765586028459790764247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122219843724018973193842831 183329765586028459790764247)
    ·
      refine ⟨274994648379042689686146371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183329765586028459790764247 274994648379042689686146371)
      ·
        refine ⟨412491972568564034529219557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274994648379042689686146371 412491972568564034529219557)
        ·
          refine ⟨77342244856605756474228667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412491972568564034529219557 77342244856605756474228667)
          ·
            refine ⟨116013367284908634711343001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77342244856605756474228667 116013367284908634711343001)
            ·
              refine ⟨87010025463681476033507251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116013367284908634711343001 87010025463681476033507251)
              ·
                refine ⟨130515038195522214050260877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87010025463681476033507251 130515038195522214050260877)
                ·
                  refine ⟨48943139323320830268847829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130515038195522214050260877 48943139323320830268847829)
                  ·
                    refine ⟨1147104827890331959426121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48943139323320830268847829 1147104827890331959426121)
                    ·
                      rfl

theorem cell23_6701936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_6701936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701936 prefixEnd_6701936 := by exact prefixLift 6701936
  have htrace : WordTrace (prefixWord ++ tailWord_6701936) baseStart_6701936 baseEnd_6701936 := by
    simpa [prefixWord, tailWord_6701936, baseEnd_6701936] using wordTrace_append hprefix tailTrace_6701936
  have hstable : (prefixWord ++ tailWord_6701936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701936).length < 2 ^ (prefixWord ++ tailWord_6701936).sum := by decide
  have hdescent : baseEnd_6701936 < baseStart_6701936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701946 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_6701946 : Nat := 118140960795 + 6701946 * 2 ^ 59
def prefixEnd_6701946 : Nat := 4983230072969 + 3 ^ 40 * 6701946 * 2
def baseEnd_6701946 : Nat := 3441319618477540839153317

theorem tailTrace_6701946 : CollatzResearch.WordTrace tailWord_6701946 prefixEnd_6701946 3441319618477540839153317 := by
  unfold tailWord_6701946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61110013044500429523887423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162960034785334478730366461 61110013044500429523887423)
  ·
    refine ⟨91665019566750644285831135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61110013044500429523887423 91665019566750644285831135)
    ·
      refine ⟨137497529350125966428746703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91665019566750644285831135 137497529350125966428746703)
      ·
        refine ⟨206246294025188949643120055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137497529350125966428746703 206246294025188949643120055)
        ·
          refine ⟨309369441037783424464680083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206246294025188949643120055 309369441037783424464680083)
          ·
            refine ⟨464054161556675136697020125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309369441037783424464680083 464054161556675136697020125)
            ·
              refine ⟨174020310583753176261382547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464054161556675136697020125 174020310583753176261382547)
              ·
                refine ⟨261030465875629764392073821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174020310583753176261382547 261030465875629764392073821)
                ·
                  refine ⟨97886424703361161647027683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261030465875629764392073821 97886424703361161647027683)
                  ·
                    refine ⟨146829637055041742470541525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97886424703361161647027683 146829637055041742470541525)
                    ·
                      refine ⟨3441319618477540839153317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146829637055041742470541525 3441319618477540839153317)
                      ·
                        rfl

theorem cell23_6701946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_6701946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701946 prefixEnd_6701946 := by exact prefixLift 6701946
  have htrace : WordTrace (prefixWord ++ tailWord_6701946) baseStart_6701946 baseEnd_6701946 := by
    simpa [prefixWord, tailWord_6701946, baseEnd_6701946] using wordTrace_append hprefix tailTrace_6701946
  have hstable : (prefixWord ++ tailWord_6701946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701946).length < 2 ^ (prefixWord ++ tailWord_6701946).sum := by decide
  have hdescent : baseEnd_6701946 < baseStart_6701946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6701993 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_6701993 : Nat := 118140960795 + 6701993 * 2 ^ 59
def prefixEnd_6701993 : Nat := 4983230072969 + 3 ^ 40 * 6701993 * 2
def baseEnd_6701993 : Nat := 3441343752068302155265601

theorem tailTrace_6701993 : CollatzResearch.WordTrace tailWord_6701993 prefixEnd_6701993 3441343752068302155265601 := by
  unfold tailWord_6701993
  simp only [CollatzResearch.WordTrace]
  refine ⟨244441766408831445122510633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162961177605887630081673755 244441766408831445122510633)
  ·
    refine ⟨183331324806623583841882975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244441766408831445122510633 183331324806623583841882975)
    ·
      refine ⟨274996987209935375762824463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183331324806623583841882975 274996987209935375762824463)
      ·
        refine ⟨412495480814903063644236695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274996987209935375762824463 412495480814903063644236695)
        ·
          refine ⟨618743221222354595466355043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412495480814903063644236695 618743221222354595466355043)
          ·
            refine ⟨928114831833531893199532565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618743221222354595466355043 928114831833531893199532565)
            ·
              refine ⟨43505382742196807493728089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 928114831833531893199532565 43505382742196807493728089)
              ·
                refine ⟨32629037056647605620296067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43505382742196807493728089 32629037056647605620296067)
                ·
                  refine ⟨48943555584971408430444101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32629037056647605620296067 48943555584971408430444101)
                  ·
                    refine ⟨9176916672182139080708269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48943555584971408430444101 9176916672182139080708269)
                    ·
                      refine ⟨3441343752068302155265601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9176916672182139080708269 3441343752068302155265601)
                      ·
                        rfl

theorem cell23_6701993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_6701993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6701993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6701993 prefixEnd_6701993 := by exact prefixLift 6701993
  have htrace : WordTrace (prefixWord ++ tailWord_6701993) baseStart_6701993 baseEnd_6701993 := by
    simpa [prefixWord, tailWord_6701993, baseEnd_6701993] using wordTrace_append hprefix tailTrace_6701993
  have hstable : (prefixWord ++ tailWord_6701993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6701993).length < 2 ^ (prefixWord ++ tailWord_6701993).sum := by decide
  have hdescent : baseEnd_6701993 < baseStart_6701993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6701993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702004 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6702004 : Nat := 118140960795 + 6702004 * 2 ^ 59
def prefixEnd_6702004 : Nat := 4983230072969 + 3 ^ 40 * 6702004 * 2
def baseEnd_6702004 : Nat := 1147116466785167204076017

theorem tailTrace_6702004 : CollatzResearch.WordTrace tailWord_6702004 prefixEnd_6702004 1147116466785167204076017 := by
  unfold tailWord_6702004
  simp only [CollatzResearch.WordTrace]
  refine ⟨122221083805895797000580533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162961445074527729334107377 122221083805895797000580533)
  ·
    refine ⟨11458226606802730968804425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122221083805895797000580533 11458226606802730968804425)
    ·
      refine ⟨8593669955102048226603319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11458226606802730968804425 8593669955102048226603319)
      ·
        refine ⟨12890504932653072339904979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593669955102048226603319 12890504932653072339904979)
        ·
          refine ⟨19335757398979608509857469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890504932653072339904979 19335757398979608509857469)
          ·
            refine ⟨7250909024617353191196551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19335757398979608509857469 7250909024617353191196551)
            ·
              refine ⟨10876363536926029786794827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250909024617353191196551 10876363536926029786794827)
              ·
                refine ⟨16314545305389044680192241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876363536926029786794827 16314545305389044680192241)
                ·
                  refine ⟨12235908979041783510144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16314545305389044680192241 12235908979041783510144181)
                  ·
                    refine ⟨1147116466785167204076017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12235908979041783510144181 1147116466785167204076017)
                    ·
                      rfl

theorem cell23_6702004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6702004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702004 prefixEnd_6702004 := by exact prefixLift 6702004
  have htrace : WordTrace (prefixWord ++ tailWord_6702004) baseStart_6702004 baseEnd_6702004 := by
    simpa [prefixWord, tailWord_6702004, baseEnd_6702004] using wordTrace_append hprefix tailTrace_6702004
  have hstable : (prefixWord ++ tailWord_6702004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702004).length < 2 ^ (prefixWord ++ tailWord_6702004).sum := by decide
  have hdescent : baseEnd_6702004 < baseStart_6702004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702030 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_6702030 : Nat := 118140960795 + 6702030 * 2 ^ 59
def prefixEnd_6702030 : Nat := 4983230072969 + 3 ^ 40 * 6702030 * 2
def baseEnd_6702030 : Nat := 382373638983613167833659

theorem tailTrace_6702030 : CollatzResearch.WordTrace tailWord_6702030 prefixEnd_6702030 382373638983613167833659 := by
  unfold tailWord_6702030
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555389488712175055200943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162962077273131600294405029 30555389488712175055200943)
  ·
    refine ⟨45833084233068262582801415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30555389488712175055200943 45833084233068262582801415)
    ·
      refine ⟨68749626349602393874202123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45833084233068262582801415 68749626349602393874202123)
      ·
        refine ⟨103124439524403590811303185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68749626349602393874202123 103124439524403590811303185)
        ·
          refine ⟨77343329643302693108477389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103124439524403590811303185 77343329643302693108477389)
          ·
            refine ⟨29003748616238509915679021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77343329643302693108477389 29003748616238509915679021)
            ·
              refine ⟨10876405731089441218379633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29003748616238509915679021 10876405731089441218379633)
              ·
                refine ⟨8157304298317080913784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10876405731089441218379633 8157304298317080913784725)
                ·
                  refine ⟨382373638983613167833659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157304298317080913784725 382373638983613167833659)
                  ·
                    rfl

theorem cell23_6702030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_6702030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702030 prefixEnd_6702030 := by exact prefixLift 6702030
  have htrace : WordTrace (prefixWord ++ tailWord_6702030) baseStart_6702030 baseEnd_6702030 := by
    simpa [prefixWord, tailWord_6702030, baseEnd_6702030] using wordTrace_append hprefix tailTrace_6702030
  have hstable : (prefixWord ++ tailWord_6702030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702030).length < 2 ^ (prefixWord ++ tailWord_6702030).sum := by decide
  have hdescent : baseEnd_6702030 < baseStart_6702030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702034 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_6702034 : Nat := 118140960795 + 6702034 * 2 ^ 59
def prefixEnd_6702034 : Nat := 4983230072969 + 3 ^ 40 * 6702034 * 2
def baseEnd_6702034 : Nat := 1147121601591712164950971

theorem tailTrace_6702034 : CollatzResearch.WordTrace tailWord_6702034 prefixEnd_6702034 1147121601591712164950971 := by
  unfold tailWord_6702034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61110815450420727281188289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162962174534455272749835437 61110815450420727281188289)
  ·
    refine ⟨45833111587815545460891217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61110815450420727281188289 45833111587815545460891217)
    ·
      refine ⟨34374833690861659095668413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45833111587815545460891217 34374833690861659095668413)
      ·
        refine ⟨12890562634073122160875655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34374833690861659095668413 12890562634073122160875655)
        ·
          refine ⟨19335843951109683241313483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890562634073122160875655 19335843951109683241313483)
          ·
            refine ⟨29003765926664524861970225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335843951109683241313483 29003765926664524861970225)
            ·
              refine ⟨21752824444998393646477669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29003765926664524861970225 21752824444998393646477669)
              ·
                refine ⟨4078654583437198808714563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21752824444998393646477669 4078654583437198808714563)
                ·
                  refine ⟨6117981875155798213071845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078654583437198808714563 6117981875155798213071845)
                  ·
                    refine ⟨1147121601591712164950971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117981875155798213071845 1147121601591712164950971)
                    ·
                      rfl

theorem cell23_6702034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_6702034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702034 prefixEnd_6702034 := by exact prefixLift 6702034
  have htrace : WordTrace (prefixWord ++ tailWord_6702034) baseStart_6702034 baseEnd_6702034 := by
    simpa [prefixWord, tailWord_6702034, baseEnd_6702034] using wordTrace_append hprefix tailTrace_6702034
  have hstable : (prefixWord ++ tailWord_6702034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702034).length < 2 ^ (prefixWord ++ tailWord_6702034).sum := by decide
  have hdescent : baseEnd_6702034 < baseStart_6702034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702047 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 6]
def baseStart_6702047 : Nat := 118140960795 + 6702047 * 2 ^ 59
def prefixEnd_6702047 : Nat := 4983230072969 + 3 ^ 40 * 6702047 * 2
def baseEnd_6702047 : Nat := 382374608891516104887817

theorem tailTrace_6702047 : CollatzResearch.WordTrace tailWord_6702047 prefixEnd_6702047 382374608891516104887817 := by
  unfold tailWord_6702047
  simp only [CollatzResearch.WordTrace]
  refine ⟨244443735950635812344976395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162962490633757208229984263 244443735950635812344976395)
  ·
    refine ⟨366665603925953718517464593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244443735950635812344976395 366665603925953718517464593)
    ·
      refine ⟨274999202944465288888098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366665603925953718517464593 274999202944465288888098445)
      ·
        refine ⟨103124701104174483333036917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274999202944465288888098445 103124701104174483333036917)
        ·
          refine ⟨9667940728516357812472211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103124701104174483333036917 9667940728516357812472211)
          ·
            refine ⟨14501911092774536718708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9667940728516357812472211 14501911092774536718708317)
            ·
              refine ⟨5438216659790451269515619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14501911092774536718708317 5438216659790451269515619)
              ·
                refine ⟨8157324989685676904273429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438216659790451269515619 8157324989685676904273429)
                ·
                  refine ⟨382374608891516104887817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157324989685676904273429 382374608891516104887817)
                  ·
                    rfl

theorem cell23_6702047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 6].length) (baseStart_6702047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702047 prefixEnd_6702047 := by exact prefixLift 6702047
  have htrace : WordTrace (prefixWord ++ tailWord_6702047) baseStart_6702047 baseEnd_6702047 := by
    simpa [prefixWord, tailWord_6702047, baseEnd_6702047] using wordTrace_append hprefix tailTrace_6702047
  have hstable : (prefixWord ++ tailWord_6702047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702047).length < 2 ^ (prefixWord ++ tailWord_6702047).sum := by decide
  have hdescent : baseEnd_6702047 < baseStart_6702047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702073 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_6702073 : Nat := 118140960795 + 6702073 * 2 ^ 59
def prefixEnd_6702073 : Nat := 4983230072969 + 3 ^ 40 * 6702073 * 2
def baseEnd_6702073 : Nat := 1147128276840220614088411

theorem tailTrace_6702073 : CollatzResearch.WordTrace tailWord_6702073 prefixEnd_6702073 1147128276840220614088411 := by
  unfold tailWord_6702073
  simp only [CollatzResearch.WordTrace]
  refine ⟨244444684248541618785422873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162963122832361079190281915 244444684248541618785422873)
  ·
    refine ⟨183333513186406214089067155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244444684248541618785422873 183333513186406214089067155)
    ·
      refine ⟨275000269779609321133600733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183333513186406214089067155 275000269779609321133600733)
      ·
        refine ⟨103125101167353495425100275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275000269779609321133600733 103125101167353495425100275)
        ·
          refine ⟨154687651751030243137650413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103125101167353495425100275 154687651751030243137650413)
          ·
            refine ⟨58007869406636341176618905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154687651751030243137650413 58007869406636341176618905)
            ·
              refine ⟨43505902054977255882464179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58007869406636341176618905 43505902054977255882464179)
              ·
                refine ⟨65258853082465883823696269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43505902054977255882464179 65258853082465883823696269)
                ·
                  refine ⟨24472069905924706433886101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65258853082465883823696269 24472069905924706433886101)
                  ·
                    refine ⟨1147128276840220614088411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24472069905924706433886101 1147128276840220614088411)
                    ·
                      rfl

theorem cell23_6702073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_6702073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702073 prefixEnd_6702073 := by exact prefixLift 6702073
  have htrace : WordTrace (prefixWord ++ tailWord_6702073) baseStart_6702073 baseEnd_6702073 := by
    simpa [prefixWord, tailWord_6702073, baseEnd_6702073] using wordTrace_append hprefix tailTrace_6702073
  have hstable : (prefixWord ++ tailWord_6702073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702073).length < 2 ^ (prefixWord ++ tailWord_6702073).sum := by decide
  have hdescent : baseEnd_6702073 < baseStart_6702073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702091 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 1, 1, 3]
def baseStart_6702091 : Nat := 118140960795 + 6702091 * 2 ^ 59
def prefixEnd_6702091 : Nat := 4983230072969 + 3 ^ 40 * 6702091 * 2
def baseEnd_6702091 : Nat := 3441394073172442771840151

theorem tailTrace_6702091 : CollatzResearch.WordTrace tailWord_6702091 prefixEnd_6702091 3441394073172442771840151 := by
  unfold tailWord_6702091
  simp only [CollatzResearch.WordTrace]
  refine ⟨244445340762476407859578127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162963560508317605239718751 244445340762476407859578127)
  ·
    refine ⟨366668011143714611789367191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244445340762476407859578127 366668011143714611789367191)
    ·
      refine ⟨550002016715571917684050787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366668011143714611789367191 550002016715571917684050787)
      ·
        refine ⟨825003025073357876526076181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550002016715571917684050787 825003025073357876526076181)
        ·
          refine ⟨38672016800313650462159821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 825003025073357876526076181 38672016800313650462159821)
          ·
            refine ⟨14502006300117618923309933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38672016800313650462159821 14502006300117618923309933)
            ·
              refine ⟨5438252362544107096241225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14502006300117618923309933 5438252362544107096241225)
              ·
                refine ⟨4078689271908080322180919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438252362544107096241225 4078689271908080322180919)
                ·
                  refine ⟨6118033907862120483271379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078689271908080322180919 6118033907862120483271379)
                  ·
                    refine ⟨9177050861793180724907069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118033907862120483271379 9177050861793180724907069)
                    ·
                      refine ⟨3441394073172442771840151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177050861793180724907069 3441394073172442771840151)
                      ·
                        rfl

theorem cell23_6702091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 1, 3].length) (baseStart_6702091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702091 prefixEnd_6702091 := by exact prefixLift 6702091
  have htrace : WordTrace (prefixWord ++ tailWord_6702091) baseStart_6702091 baseEnd_6702091 := by
    simpa [prefixWord, tailWord_6702091, baseEnd_6702091] using wordTrace_append hprefix tailTrace_6702091
  have hstable : (prefixWord ++ tailWord_6702091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702091).length < 2 ^ (prefixWord ++ tailWord_6702091).sum := by decide
  have hdescent : baseEnd_6702091 < baseStart_6702091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702098 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_6702098 : Nat := 118140960795 + 6702098 * 2 ^ 59
def prefixEnd_6702098 : Nat := 4983230072969 + 3 ^ 40 * 6702098 * 2
def baseEnd_6702098 : Nat := 382377518615224916050291

theorem tailTrace_6702098 : CollatzResearch.WordTrace tailWord_6702098 prefixEnd_6702098 382377518615224916050291 := by
  unfold tailWord_6702098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61111399018362762013770737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162963730715634032036721965 61111399018362762013770737)
  ·
    refine ⟨45833549263772071510328053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61111399018362762013770737 45833549263772071510328053)
    ·
      refine ⟨4296895243478631704093255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45833549263772071510328053 4296895243478631704093255)
      ·
        refine ⟨6445342865217947556139883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296895243478631704093255 6445342865217947556139883)
        ·
          refine ⟨9668014297826921334209825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6445342865217947556139883 9668014297826921334209825)
          ·
            refine ⟨7251010723370191000657369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9668014297826921334209825 7251010723370191000657369)
            ·
              refine ⟨5438258042527643250493027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7251010723370191000657369 5438258042527643250493027)
              ·
                refine ⟨8157387063791464875739541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438258042527643250493027 8157387063791464875739541)
                ·
                  refine ⟨382377518615224916050291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157387063791464875739541 382377518615224916050291)
                  ·
                    rfl

theorem cell23_6702098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_6702098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702098 prefixEnd_6702098 := by exact prefixLift 6702098
  have htrace : WordTrace (prefixWord ++ tailWord_6702098) baseStart_6702098 baseEnd_6702098 := by
    simpa [prefixWord, tailWord_6702098, baseEnd_6702098] using wordTrace_append hprefix tailTrace_6702098
  have hstable : (prefixWord ++ tailWord_6702098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702098).length < 2 ^ (prefixWord ++ tailWord_6702098).sum := by decide
  have hdescent : baseEnd_6702098 < baseStart_6702098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702114 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_6702114 : Nat := 118140960795 + 6702114 * 2 ^ 59
def prefixEnd_6702114 : Nat := 4983230072969 + 3 ^ 40 * 6702114 * 2
def baseEnd_6702114 : Nat := 3441405883227496181852545

theorem tailTrace_6702114 : CollatzResearch.WordTrace tailWord_6702114 prefixEnd_6702114 3441405883227496181852545 := by
  unfold tailWord_6702114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61111544910348270696916349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162964119760928721858443597 61111544910348270696916349)
  ·
    refine ⟨22916829341380601511343631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61111544910348270696916349 22916829341380601511343631)
    ·
      refine ⟨34375244012070902267015447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22916829341380601511343631 34375244012070902267015447)
      ·
        refine ⟨51562866018106353400523171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34375244012070902267015447 51562866018106353400523171)
        ·
          refine ⟨77344299027159530100784757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51562866018106353400523171 77344299027159530100784757)
          ·
            refine ⟨7251028033796205946948571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77344299027159530100784757 7251028033796205946948571)
            ·
              refine ⟨10876542050694308920422857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251028033796205946948571 10876542050694308920422857)
              ·
                refine ⟨8157406538020731690317143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10876542050694308920422857 8157406538020731690317143)
                ·
                  refine ⟨12236109807031097535475715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157406538020731690317143 12236109807031097535475715)
                  ·
                    refine ⟨18354164710546646303213573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12236109807031097535475715 18354164710546646303213573)
                    ·
                      refine ⟨3441405883227496181852545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18354164710546646303213573 3441405883227496181852545)
                      ·
                        rfl

theorem cell23_6702114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_6702114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702114 prefixEnd_6702114 := by exact prefixLift 6702114
  have htrace : WordTrace (prefixWord ++ tailWord_6702114) baseStart_6702114 baseEnd_6702114 := by
    simpa [prefixWord, tailWord_6702114, baseEnd_6702114] using wordTrace_append hprefix tailTrace_6702114
  have hstable : (prefixWord ++ tailWord_6702114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702114).length < 2 ^ (prefixWord ++ tailWord_6702114).sum := by decide
  have hdescent : baseEnd_6702114 < baseStart_6702114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702134 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6702134 : Nat := 118140960795 + 6702134 * 2 ^ 59
def prefixEnd_6702134 : Nat := 4983230072969 + 3 ^ 40 * 6702134 * 2
def baseEnd_6702134 : Nat := 3441416152840586103602453

theorem tailTrace_6702134 : CollatzResearch.WordTrace tailWord_6702134 prefixEnd_6702134 3441416152840586103602453 := by
  unfold tailWord_6702134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15277931818832539137712091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162964606067547084135595637 15277931818832539137712091)
  ·
    refine ⟨22916897728248808706568137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15277931818832539137712091 22916897728248808706568137)
    ·
      refine ⟨17187673296186606529926103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22916897728248808706568137 17187673296186606529926103)
      ·
        refine ⟨25781509944279909794889155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187673296186606529926103 25781509944279909794889155)
        ·
          refine ⟨38672264916419864692333733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25781509944279909794889155 38672264916419864692333733)
          ·
            refine ⟨7251049671828724629812575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38672264916419864692333733 7251049671828724629812575)
            ·
              refine ⟨10876574507743086944718863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251049671828724629812575 10876574507743086944718863)
              ·
                refine ⟨16314861761614630417078295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876574507743086944718863 16314861761614630417078295)
                ·
                  refine ⟨24472292642421945625617443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16314861761614630417078295 24472292642421945625617443)
                  ·
                    refine ⟨36708438963632918438426165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24472292642421945625617443 36708438963632918438426165)
                    ·
                      refine ⟨3441416152840586103602453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36708438963632918438426165 3441416152840586103602453)
                      ·
                        rfl

theorem cell23_6702134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6702134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702134 prefixEnd_6702134 := by exact prefixLift 6702134
  have htrace : WordTrace (prefixWord ++ tailWord_6702134) baseStart_6702134 baseEnd_6702134 := by
    simpa [prefixWord, tailWord_6702134, baseEnd_6702134] using wordTrace_append hprefix tailTrace_6702134
  have hstable : (prefixWord ++ tailWord_6702134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702134).length < 2 ^ (prefixWord ++ tailWord_6702134).sum := by decide
  have hdescent : baseEnd_6702134 < baseStart_6702134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702163 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 8]
def baseStart_6702163 : Nat := 118140960795 + 6702163 * 2 ^ 59
def prefixEnd_6702163 : Nat := 4983230072969 + 3 ^ 40 * 6702163 * 2
def baseEnd_6702163 : Nat := 1147143681259855496713273

theorem tailTrace_6702163 : CollatzResearch.WordTrace tailWord_6702163 prefixEnd_6702163 1147143681259855496713273 := by
  unfold tailWord_6702163
  simp only [CollatzResearch.WordTrace]
  refine ⟨244447966818215564156199143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162965311212143709437466095 244447966818215564156199143)
  ·
    refine ⟨366671950227323346234298715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244447966818215564156199143 366671950227323346234298715)
    ·
      refine ⟨550007925340985019351448073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366671950227323346234298715 550007925340985019351448073)
      ·
        refine ⟨412505944005738764513586055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550007925340985019351448073 412505944005738764513586055)
        ·
          refine ⟨618758916008608146770379083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412505944005738764513586055 618758916008608146770379083)
          ·
            refine ⟨928138374012912220155568625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618758916008608146770379083 928138374012912220155568625)
            ·
              refine ⟨696103780509684165116676469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928138374012912220155568625 696103780509684165116676469)
              ·
                refine ⟨65259729422782890479688419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 696103780509684165116676469 65259729422782890479688419)
                ·
                  refine ⟨97889594134174335719532629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65259729422782890479688419 97889594134174335719532629)
                  ·
                    refine ⟨1147143681259855496713273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97889594134174335719532629 1147143681259855496713273)
                    ·
                      rfl

theorem cell23_6702163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_6702163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702163 prefixEnd_6702163 := by exact prefixLift 6702163
  have htrace : WordTrace (prefixWord ++ tailWord_6702163) baseStart_6702163 baseEnd_6702163 := by
    simpa [prefixWord, tailWord_6702163, baseEnd_6702163] using wordTrace_append hprefix tailTrace_6702163
  have hstable : (prefixWord ++ tailWord_6702163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702163).length < 2 ^ (prefixWord ++ tailWord_6702163).sum := by decide
  have hdescent : baseEnd_6702163 < baseStart_6702163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702164 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_6702164 : Nat := 118140960795 + 6702164 * 2 ^ 59
def prefixEnd_6702164 : Nat := 4983230072969 + 3 ^ 40 * 6702164 * 2
def baseEnd_6702164 : Nat := 3441431557260220986227315

theorem tailTrace_6702164 : CollatzResearch.WordTrace tailWord_6702164 prefixEnd_6702164 3441431557260220986227315 := by
  unfold tailWord_6702164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122224001645605970663492773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162965335527474627551323697 122224001645605970663492773)
  ·
    refine ⟨22917000308551119499404895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122224001645605970663492773 22917000308551119499404895)
    ·
      refine ⟨34375500462826679249107343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22917000308551119499404895 34375500462826679249107343)
      ·
        refine ⟨51563250694240018873661015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34375500462826679249107343 51563250694240018873661015)
        ·
          refine ⟨77344876041360028310491523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51563250694240018873661015 77344876041360028310491523)
          ·
            refine ⟨116017314062040042465737285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77344876041360028310491523 116017314062040042465737285)
            ·
              refine ⟨21753246386632507962325741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116017314062040042465737285 21753246386632507962325741)
              ·
                refine ⟨8157467394987190485872153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21753246386632507962325741 8157467394987190485872153)
                ·
                  refine ⟨6118100546240392864404115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8157467394987190485872153 6118100546240392864404115)
                  ·
                    refine ⟨9177150819360589296606173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118100546240392864404115 9177150819360589296606173)
                    ·
                      refine ⟨3441431557260220986227315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177150819360589296606173 3441431557260220986227315)
                      ·
                        rfl

theorem cell23_6702164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_6702164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702164 prefixEnd_6702164 := by exact prefixLift 6702164
  have htrace : WordTrace (prefixWord ++ tailWord_6702164) baseStart_6702164 baseEnd_6702164 := by
    simpa [prefixWord, tailWord_6702164, baseEnd_6702164] using wordTrace_append hprefix tailTrace_6702164
  have hstable : (prefixWord ++ tailWord_6702164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702164).length < 2 ^ (prefixWord ++ tailWord_6702164).sum := by decide
  have hdescent : baseEnd_6702164 < baseStart_6702164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702200 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_6702200 : Nat := 118140960795 + 6702200 * 2 ^ 59
def prefixEnd_6702200 : Nat := 4983230072969 + 3 ^ 40 * 6702200 * 2
def baseEnd_6702200 : Nat := 3441450042563782845377149

theorem tailTrace_6702200 : CollatzResearch.WordTrace tailWord_6702200 prefixEnd_6702200 3441450042563782845377149 := by
  unfold tailWord_6702200
  simp only [CollatzResearch.WordTrace]
  refine ⟨122224658159540759737648027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162966210879387679650197369 122224658159540759737648027)
  ·
    refine ⟨183336987239311139606472041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122224658159540759737648027 183336987239311139606472041)
    ·
      refine ⟨137502740429483354704854031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183336987239311139606472041 137502740429483354704854031)
      ·
        refine ⟨206254110644225032057281047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137502740429483354704854031 206254110644225032057281047)
        ·
          refine ⟨309381165966337548085921571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206254110644225032057281047 309381165966337548085921571)
          ·
            refine ⟨464071748949506322128882357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309381165966337548085921571 464071748949506322128882357)
            ·
              refine ⟨43506726464016217699582721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 464071748949506322128882357 43506726464016217699582721)
              ·
                refine ⟨32630044848012163274687041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43506726464016217699582721 32630044848012163274687041)
                ·
                  refine ⟨24472533636009122456015281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32630044848012163274687041 24472533636009122456015281)
                  ·
                    refine ⟨18354400227006841842011461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24472533636009122456015281 18354400227006841842011461)
                    ·
                      refine ⟨3441450042563782845377149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18354400227006841842011461 3441450042563782845377149)
                      ·
                        rfl

theorem cell23_6702200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_6702200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702200 prefixEnd_6702200 := by exact prefixLift 6702200
  have htrace : WordTrace (prefixWord ++ tailWord_6702200) baseStart_6702200 baseEnd_6702200 := by
    simpa [prefixWord, tailWord_6702200, baseEnd_6702200] using wordTrace_append hprefix tailTrace_6702200
  have hstable : (prefixWord ++ tailWord_6702200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702200).length < 2 ^ (prefixWord ++ tailWord_6702200).sum := by decide
  have hdescent : baseEnd_6702200 < baseStart_6702200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702204 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_6702204 : Nat := 118140960795 + 6702204 * 2 ^ 59
def prefixEnd_6702204 : Nat := 4983230072969 + 3 ^ 40 * 6702204 * 2
def baseEnd_6702204 : Nat := 3441452096486400829727131

theorem tailTrace_6702204 : CollatzResearch.WordTrace tailWord_6702204 prefixEnd_6702204 3441452096486400829727131 := by
  unfold tailWord_6702204
  simp only [CollatzResearch.WordTrace]
  refine ⟨122224731105533514079220833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162966308140711352105627777 122224731105533514079220833)
  ·
    refine ⟨91668548329150135559415625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122224731105533514079220833 91668548329150135559415625)
    ·
      refine ⟨68751411246862601669561719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91668548329150135559415625 68751411246862601669561719)
      ·
        refine ⟨103127116870293902504342579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68751411246862601669561719 103127116870293902504342579)
        ·
          refine ⟨154690675305440853756513869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103127116870293902504342579 154690675305440853756513869)
          ·
            refine ⟨58009003239540320158692701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154690675305440853756513869 58009003239540320158692701)
            ·
              refine ⟨21753376214827620059509763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58009003239540320158692701 21753376214827620059509763)
              ·
                refine ⟨32630064322241430089264645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21753376214827620059509763 32630064322241430089264645)
                ·
                  refine ⟨6118137060420268141737121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32630064322241430089264645 6118137060420268141737121)
                  ·
                    refine ⟨4588602795315201106302841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6118137060420268141737121 4588602795315201106302841)
                    ·
                      refine ⟨3441452096486400829727131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588602795315201106302841 3441452096486400829727131)
                      ·
                        rfl

theorem cell23_6702204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_6702204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702204 prefixEnd_6702204 := by exact prefixLift 6702204
  have htrace : WordTrace (prefixWord ++ tailWord_6702204) baseStart_6702204 baseEnd_6702204 := by
    simpa [prefixWord, tailWord_6702204, baseEnd_6702204] using wordTrace_append hprefix tailTrace_6702204
  have hstable : (prefixWord ++ tailWord_6702204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702204).length < 2 ^ (prefixWord ++ tailWord_6702204).sum := by decide
  have hdescent : baseEnd_6702204 < baseStart_6702204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702240 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_6702240 : Nat := 118140960795 + 6702240 * 2 ^ 59
def prefixEnd_6702240 : Nat := 4983230072969 + 3 ^ 40 * 6702240 * 2
def baseEnd_6702240 : Nat := 1147156860596654229625655

theorem tailTrace_6702240 : CollatzResearch.WordTrace tailWord_6702240 prefixEnd_6702240 1147156860596654229625655 := by
  unfold tailWord_6702240
  simp only [CollatzResearch.WordTrace]
  refine ⟨122225387619468303153376087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162967183492624404204501449 122225387619468303153376087)
  ·
    refine ⟨183338081429202454730064131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122225387619468303153376087 183338081429202454730064131)
    ·
      refine ⟨275007122143803682095096197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183338081429202454730064131 275007122143803682095096197)
      ·
        refine ⟨51563835401963190392830537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275007122143803682095096197 51563835401963190392830537)
        ·
          refine ⟨38672876551472392794622903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51563835401963190392830537 38672876551472392794622903)
          ·
            refine ⟨58009314827208589191934355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38672876551472392794622903 58009314827208589191934355)
            ·
              refine ⟨87013972240812883787901533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58009314827208589191934355 87013972240812883787901533)
              ·
                refine ⟨32630239590304831420463075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87013972240812883787901533 32630239590304831420463075)
                ·
                  refine ⟨48945359385457247130694613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32630239590304831420463075 48945359385457247130694613)
                  ·
                    refine ⟨1147156860596654229625655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48945359385457247130694613 1147156860596654229625655)
                    ·
                      rfl

theorem cell23_6702240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_6702240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702240 prefixEnd_6702240 := by exact prefixLift 6702240
  have htrace : WordTrace (prefixWord ++ tailWord_6702240) baseStart_6702240 baseEnd_6702240 := by
    simpa [prefixWord, tailWord_6702240, baseEnd_6702240] using wordTrace_append hprefix tailTrace_6702240
  have hstable : (prefixWord ++ tailWord_6702240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702240).length < 2 ^ (prefixWord ++ tailWord_6702240).sum := by decide
  have hdescent : baseEnd_6702240 < baseStart_6702240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702244 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 5]
def baseStart_6702244 : Nat := 118140960795 + 6702244 * 2 ^ 59
def prefixEnd_6702244 : Nat := 4983230072969 + 3 ^ 40 * 6702244 * 2
def baseEnd_6702244 : Nat := 382385848412508963691883

theorem tailTrace_6702244 : CollatzResearch.WordTrace tailWord_6702244 prefixEnd_6702244 382385848412508963691883 := by
  unfold tailWord_6702244
  simp only [CollatzResearch.WordTrace]
  refine ⟨122225460565461057494948893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162967280753948076659931857 122225460565461057494948893)
  ·
    refine ⟨45834547712047896560605835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122225460565461057494948893 45834547712047896560605835)
    ·
      refine ⟨68751821568071844840908753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45834547712047896560605835 68751821568071844840908753)
      ·
        refine ⟨51563866176053883630681565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68751821568071844840908753 51563866176053883630681565)
        ·
          refine ⟨19336449816020206361505587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51563866176053883630681565 19336449816020206361505587)
          ·
            refine ⟨29004674724030309542258381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336449816020206361505587 29004674724030309542258381)
            ·
              refine ⟨10876753021511366078346893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29004674724030309542258381 10876753021511366078346893)
              ·
                refine ⟨4078782383066762279380085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10876753021511366078346893 4078782383066762279380085)
                ·
                  refine ⟨382385848412508963691883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078782383066762279380085 382385848412508963691883)
                  ·
                    rfl

theorem cell23_6702244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_6702244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702244 prefixEnd_6702244 := by exact prefixLift 6702244
  have htrace : WordTrace (prefixWord ++ tailWord_6702244) baseStart_6702244 baseEnd_6702244 := by
    simpa [prefixWord, tailWord_6702244, baseEnd_6702244] using wordTrace_append hprefix tailTrace_6702244
  have hstable : (prefixWord ++ tailWord_6702244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702244).length < 2 ^ (prefixWord ++ tailWord_6702244).sum := by decide
  have hdescent : baseEnd_6702244 < baseStart_6702244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702257 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_6702257 : Nat := 118140960795 + 6702257 * 2 ^ 59
def prefixEnd_6702257 : Nat := 4983230072969 + 3 ^ 40 * 6702257 * 2
def baseEnd_6702257 : Nat := 1147159770320363040788129

theorem tailTrace_6702257 : CollatzResearch.WordTrace tailWord_6702257 prefixEnd_6702257 1147159770320363040788129 := by
  unfold tailWord_6702257
  simp only [CollatzResearch.WordTrace]
  refine ⟨244451395279875018210121025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162967596853250012140080683 244451395279875018210121025)
  ·
    refine ⟨183338546459906263657590769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244451395279875018210121025 183338546459906263657590769)
    ·
      refine ⟨137503909844929697743193077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183338546459906263657590769 137503909844929697743193077)
      ·
        refine ⟨12890991547962159163424351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137503909844929697743193077 12890991547962159163424351)
        ·
          refine ⟨19336487321943238745136527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890991547962159163424351 19336487321943238745136527)
          ·
            refine ⟨29004730982914858117704791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336487321943238745136527 29004730982914858117704791)
            ·
              refine ⟨43507096474372287176557187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29004730982914858117704791 43507096474372287176557187)
              ·
                refine ⟨65260644711558430764835781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43507096474372287176557187 65260644711558430764835781)
                ·
                  refine ⟨12236370883417205768406709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65260644711558430764835781 12236370883417205768406709)
                  ·
                    refine ⟨1147159770320363040788129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12236370883417205768406709 1147159770320363040788129)
                    ·
                      rfl

theorem cell23_6702257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_6702257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702257 prefixEnd_6702257 := by exact prefixLift 6702257
  have htrace : WordTrace (prefixWord ++ tailWord_6702257) baseStart_6702257 baseEnd_6702257 := by
    simpa [prefixWord, tailWord_6702257, baseEnd_6702257] using wordTrace_append hprefix tailTrace_6702257
  have hstable : (prefixWord ++ tailWord_6702257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702257).length < 2 ^ (prefixWord ++ tailWord_6702257).sum := by decide
  have hdescent : baseEnd_6702257 < baseStart_6702257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702277 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_6702277 : Nat := 118140960795 + 6702277 * 2 ^ 59
def prefixEnd_6702277 : Nat := 4983230072969 + 3 ^ 40 * 6702277 * 2
def baseEnd_6702277 : Nat := 3441489580574179044114295

theorem tailTrace_6702277 : CollatzResearch.WordTrace tailWord_6702277 prefixEnd_6702277 3441489580574179044114295 := by
  unfold tailWord_6702277
  simp only [CollatzResearch.WordTrace]
  refine ⟨244452124739802561625849085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162968083159868374417232723 244452124739802561625849085)
  ·
    refine ⟨91669546777425960609693407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244452124739802561625849085 91669546777425960609693407)
    ·
      refine ⟨137504320166138940914540111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91669546777425960609693407 137504320166138940914540111)
      ·
        refine ⟨206256480249208411371810167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137504320166138940914540111 206256480249208411371810167)
        ·
          refine ⟨309384720373812617057715251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206256480249208411371810167 309384720373812617057715251)
          ·
            refine ⟨464077080560718925586572877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309384720373812617057715251 464077080560718925586572877)
            ·
              refine ⟨174028905210269597094964829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464077080560718925586572877 174028905210269597094964829)
              ·
                refine ⟨65260839453851098910611811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174028905210269597094964829 65260839453851098910611811)
                ·
                  refine ⟨97891259180776648365917717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65260839453851098910611811 97891259180776648365917717)
                  ·
                    refine ⟨4588652774098905392152393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97891259180776648365917717 4588652774098905392152393)
                    ·
                      refine ⟨3441489580574179044114295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588652774098905392152393 3441489580574179044114295)
                      ·
                        rfl

theorem cell23_6702277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_6702277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702277 prefixEnd_6702277 := by exact prefixLift 6702277
  have htrace : WordTrace (prefixWord ++ tailWord_6702277) baseStart_6702277 baseEnd_6702277 := by
    simpa [prefixWord, tailWord_6702277, baseEnd_6702277] using wordTrace_append hprefix tailTrace_6702277
  have hstable : (prefixWord ++ tailWord_6702277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702277).length < 2 ^ (prefixWord ++ tailWord_6702277).sum := by decide
  have hdescent : baseEnd_6702277 < baseStart_6702277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702314 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_6702314 : Nat := 118140960795 + 6702314 * 2 ^ 59
def prefixEnd_6702314 : Nat := 4983230072969 + 3 ^ 40 * 6702314 * 2
def baseEnd_6702314 : Nat := 3441508579358395399351625

theorem tailTrace_6702314 : CollatzResearch.WordTrace tailWord_6702314 prefixEnd_6702314 3441508579358395399351625 := by
  unfold tailWord_6702314
  simp only [CollatzResearch.WordTrace]
  refine ⟨61113368560167129236236499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162968982827112344629963997 61113368560167129236236499)
  ·
    refine ⟨91670052840250693854354749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61113368560167129236236499 91670052840250693854354749)
    ·
      refine ⟨34376269815094010195383031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91670052840250693854354749 34376269815094010195383031)
      ·
        refine ⟨51564404722641015293074547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34376269815094010195383031 51564404722641015293074547)
        ·
          refine ⟨77346607083961522939611821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51564404722641015293074547 77346607083961522939611821)
          ·
            refine ⟨29004977656485571102354433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77346607083961522939611821 29004977656485571102354433)
            ·
              refine ⟨21753733242364178326765825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29004977656485571102354433 21753733242364178326765825)
              ·
                refine ⟨16315299931773133745074369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21753733242364178326765825 16315299931773133745074369)
                ·
                  refine ⟨12236474948829850308805777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16315299931773133745074369 12236474948829850308805777)
                  ·
                    refine ⟨9177356211622387731604333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12236474948829850308805777 9177356211622387731604333)
                    ·
                      refine ⟨3441508579358395399351625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177356211622387731604333 3441508579358395399351625)
                      ·
                        rfl

theorem cell23_6702314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_6702314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702314 prefixEnd_6702314 := by exact prefixLift 6702314
  have htrace : WordTrace (prefixWord ++ tailWord_6702314) baseStart_6702314 baseEnd_6702314 := by
    simpa [prefixWord, tailWord_6702314, baseEnd_6702314] using wordTrace_append hprefix tailTrace_6702314
  have hstable : (prefixWord ++ tailWord_6702314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702314).length < 2 ^ (prefixWord ++ tailWord_6702314).sum := by decide
  have hdescent : baseEnd_6702314 < baseStart_6702314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702334 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_6702334 : Nat := 118140960795 + 6702334 * 2 ^ 59
def prefixEnd_6702334 : Nat := 4983230072969 + 3 ^ 40 * 6702334 * 2
def baseEnd_6702334 : Nat := 382390983219053924566837

theorem tailTrace_6702334 : CollatzResearch.WordTrace tailWord_6702334 prefixEnd_6702334 382390983219053924566837 := by
  unfold tailWord_6702334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556775462574507545084257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162969469133730706907116037 30556775462574507545084257)
  ·
    refine ⟨22917581596930880658813193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30556775462574507545084257 22917581596930880658813193)
    ·
      refine ⟨17188186197698160494109895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22917581596930880658813193 17188186197698160494109895)
      ·
        refine ⟨25782279296547240741164843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17188186197698160494109895 25782279296547240741164843)
        ·
          refine ⟨38673418944820861111747265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25782279296547240741164843 38673418944820861111747265)
          ·
            refine ⟨29005064208615645833810449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38673418944820861111747265 29005064208615645833810449)
            ·
              refine ⟨21753798156461734375357837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29005064208615645833810449 21753798156461734375357837)
              ·
                refine ⟨8157674308673150390759189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21753798156461734375357837 8157674308673150390759189)
                ·
                  refine ⟨382390983219053924566837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157674308673150390759189 382390983219053924566837)
                  ·
                    rfl

theorem cell23_6702334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_6702334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702334 prefixEnd_6702334 := by exact prefixLift 6702334
  have htrace : WordTrace (prefixWord ++ tailWord_6702334) baseStart_6702334 baseEnd_6702334 := by
    simpa [prefixWord, tailWord_6702334, baseEnd_6702334] using wordTrace_append hprefix tailTrace_6702334
  have hstable : (prefixWord ++ tailWord_6702334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702334).length < 2 ^ (prefixWord ++ tailWord_6702334).sum := by decide
  have hdescent : baseEnd_6702334 < baseStart_6702334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702347 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 3, 5]
def baseStart_6702347 : Nat := 118140960795 + 6702347 * 2 ^ 59
def prefixEnd_6702347 : Nat := 4983230072969 + 3 ^ 40 * 6702347 * 2
def baseEnd_6702347 : Nat := 1147175174739997923412991

theorem tailTrace_6702347 : CollatzResearch.WordTrace tailWord_6702347 prefixEnd_6702347 1147175174739997923412991 := by
  unfold tailWord_6702347
  simp only [CollatzResearch.WordTrace]
  refine ⟨244454677849548963580897295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162969785233032642387264863 244454677849548963580897295)
  ·
    refine ⟨366682016774323445371345943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244454677849548963580897295 366682016774323445371345943)
    ·
      refine ⟨550023025161485168057018915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366682016774323445371345943 550023025161485168057018915)
      ·
        refine ⟨825034537742227752085528373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550023025161485168057018915 825034537742227752085528373)
        ·
          refine ⟨77346987913333851758018285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 825034537742227752085528373 77346987913333851758018285)
          ·
            refine ⟨29005120467500194409256857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77346987913333851758018285 29005120467500194409256857)
            ·
              refine ⟨21753840350625145806942643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29005120467500194409256857 21753840350625145806942643)
              ·
                refine ⟨32630760525937718710413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21753840350625145806942643 32630760525937718710413965)
                ·
                  refine ⟨12236535197226644516405237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32630760525937718710413965 12236535197226644516405237)
                  ·
                    refine ⟨1147175174739997923412991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12236535197226644516405237 1147175174739997923412991)
                    ·
                      rfl

theorem cell23_6702347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].length) (baseStart_6702347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702347 prefixEnd_6702347 := by exact prefixLift 6702347
  have htrace : WordTrace (prefixWord ++ tailWord_6702347) baseStart_6702347 baseEnd_6702347 := by
    simpa [prefixWord, tailWord_6702347, baseEnd_6702347] using wordTrace_append hprefix tailTrace_6702347
  have hstable : (prefixWord ++ tailWord_6702347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702347).length < 2 ^ (prefixWord ++ tailWord_6702347).sum := by decide
  have hdescent : baseEnd_6702347 < baseStart_6702347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702378 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6702378 : Nat := 118140960795 + 6702378 * 2 ^ 59
def prefixEnd_6702378 : Nat := 4983230072969 + 3 ^ 40 * 6702378 * 2
def baseEnd_6702378 : Nat := 3441541442120283148951331

theorem tailTrace_6702378 : CollatzResearch.WordTrace tailWord_6702378 prefixEnd_6702378 3441541442120283148951331 := by
  unfold tailWord_6702378
  simp only [CollatzResearch.WordTrace]
  refine ⟨61113952128109163968818947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162970539008291103916850525 61113952128109163968818947)
  ·
    refine ⟨91670928192163745953228421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61113952128109163968818947 91670928192163745953228421)
    ·
      refine ⟨17188299036030702366230329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91670928192163745953228421 17188299036030702366230329)
      ·
        refine ⟨12891224277023026774672747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17188299036030702366230329 12891224277023026774672747)
        ·
          refine ⟨19336836415534540162009121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12891224277023026774672747 19336836415534540162009121)
          ·
            refine ⟨14502627311650905121506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19336836415534540162009121 14502627311650905121506841)
            ·
              refine ⟨10876970483738178841130131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14502627311650905121506841 10876970483738178841130131)
              ·
                refine ⟨16315455725607268261695197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876970483738178841130131 16315455725607268261695197)
                ·
                  refine ⟨6118295897102725598135699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16315455725607268261695197 6118295897102725598135699)
                  ·
                    refine ⟨9177443845654088397203549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118295897102725598135699 9177443845654088397203549)
                    ·
                      refine ⟨3441541442120283148951331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177443845654088397203549 3441541442120283148951331)
                      ·
                        rfl

theorem cell23_6702378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6702378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702378 prefixEnd_6702378 := by exact prefixLift 6702378
  have htrace : WordTrace (prefixWord ++ tailWord_6702378) baseStart_6702378 baseEnd_6702378 := by
    simpa [prefixWord, tailWord_6702378, baseEnd_6702378] using wordTrace_append hprefix tailTrace_6702378
  have hstable : (prefixWord ++ tailWord_6702378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702378).length < 2 ^ (prefixWord ++ tailWord_6702378).sum := by decide
  have hdescent : baseEnd_6702378 < baseStart_6702378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702387 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_6702387 : Nat := 118140960795 + 6702387 * 2 ^ 59
def prefixEnd_6702387 : Nat := 4983230072969 + 3 ^ 40 * 6702387 * 2
def baseEnd_6702387 : Nat := 3441546063446173613738789

theorem tailTrace_6702387 : CollatzResearch.WordTrace tailWord_6702387 prefixEnd_6702387 3441546063446173613738789 := by
  unfold tailWord_6702387
  simp only [CollatzResearch.WordTrace]
  refine ⟨244456136769404050412353415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162970757846269366941568943 244456136769404050412353415)
  ·
    refine ⟨366684205154106075618530123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244456136769404050412353415 366684205154106075618530123)
    ·
      refine ⟨550026307731159113427795185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366684205154106075618530123 550026307731159113427795185)
      ·
        refine ⟨412519730798369335070846389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550026307731159113427795185 412519730798369335070846389)
        ·
          refine ⟨38673724762347125162891849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412519730798369335070846389 38673724762347125162891849)
          ·
            refine ⟨29005293571760343872168887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38673724762347125162891849 29005293571760343872168887)
            ·
              refine ⟨43507940357640515808253331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29005293571760343872168887 43507940357640515808253331)
              ·
                refine ⟨65261910536460773712379997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43507940357640515808253331 65261910536460773712379997)
                ·
                  refine ⟨24473216451172790142142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65261910536460773712379997 24473216451172790142142499)
                  ·
                    refine ⟨36709824676759185213213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24473216451172790142142499 36709824676759185213213749)
                    ·
                      refine ⟨3441546063446173613738789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36709824676759185213213749 3441546063446173613738789)
                      ·
                        rfl

theorem cell23_6702387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_6702387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702387 prefixEnd_6702387 := by exact prefixLift 6702387
  have htrace : WordTrace (prefixWord ++ tailWord_6702387) baseStart_6702387 baseEnd_6702387 := by
    simpa [prefixWord, tailWord_6702387, baseEnd_6702387] using wordTrace_append hprefix tailTrace_6702387
  have hstable : (prefixWord ++ tailWord_6702387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702387).length < 2 ^ (prefixWord ++ tailWord_6702387).sum := by decide
  have hdescent : baseEnd_6702387 < baseStart_6702387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702401 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6702401 : Nat := 118140960795 + 6702401 * 2 ^ 59
def prefixEnd_6702401 : Nat := 4983230072969 + 3 ^ 40 * 6702401 * 2
def baseEnd_6702401 : Nat := 3441553252175336558963725

theorem tailTrace_6702401 : CollatzResearch.WordTrace tailWord_6702401 prefixEnd_6702401 3441553252175336558963725 := by
  unfold tailWord_6702401
  simp only [CollatzResearch.WordTrace]
  refine ⟨244456647391353330803363057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162971098260902220535575371 244456647391353330803363057)
  ·
    refine ⟨183342485543514998102522293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244456647391353330803363057 183342485543514998102522293)
    ·
      refine ⟨17188358019704531072111465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183342485543514998102522293 17188358019704531072111465)
      ·
        refine ⟨12891268514778398304083599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17188358019704531072111465 12891268514778398304083599)
        ·
          refine ⟨19336902772167597456125399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12891268514778398304083599 19336902772167597456125399)
          ·
            refine ⟨29005354158251396184188099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336902772167597456125399 29005354158251396184188099)
            ·
              refine ⟨43508031237377094276282149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29005354158251396184188099 43508031237377094276282149)
              ·
                refine ⟨8157755857008205176802903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43508031237377094276282149 8157755857008205176802903)
                ·
                  refine ⟨12236633785512307765204355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157755857008205176802903 12236633785512307765204355)
                  ·
                    refine ⟨18354950678268461647806533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12236633785512307765204355 18354950678268461647806533)
                    ·
                      refine ⟨3441553252175336558963725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18354950678268461647806533 3441553252175336558963725)
                      ·
                        rfl

theorem cell23_6702401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6702401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702401 prefixEnd_6702401 := by exact prefixLift 6702401
  have htrace : WordTrace (prefixWord ++ tailWord_6702401) baseStart_6702401 baseEnd_6702401 := by
    simpa [prefixWord, tailWord_6702401, baseEnd_6702401] using wordTrace_append hprefix tailTrace_6702401
  have hstable : (prefixWord ++ tailWord_6702401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702401).length < 2 ^ (prefixWord ++ tailWord_6702401).sum := by decide
  have hdescent : baseEnd_6702401 < baseStart_6702401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702407 : List Nat := [1, 1, 4, 1, 2, 4, 1, 9]
def baseStart_6702407 : Nat := 118140960795 + 6702407 * 2 ^ 59
def prefixEnd_6702407 : Nat := 4983230072969 + 3 ^ 40 * 6702407 * 2
def baseEnd_6702407 : Nat := 127465049372565316129211

theorem tailTrace_6702407 : CollatzResearch.WordTrace tailWord_6702407 prefixEnd_6702407 127465049372565316129211 := by
  unfold tailWord_6702407
  simp only [CollatzResearch.WordTrace]
  refine ⟨244456866229331593828081475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162971244152887729218720983 244456866229331593828081475)
  ·
    refine ⟨366685299343997390742122213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244456866229331593828081475 366685299343997390742122213)
    ·
      refine ⟨68753493626999510764147915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366685299343997390742122213 68753493626999510764147915)
      ·
        refine ⟨103130240440499266146221873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68753493626999510764147915 103130240440499266146221873)
        ·
          refine ⟨77347680330374449609666405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103130240440499266146221873 77347680330374449609666405)
          ·
            refine ⟨14502690061945209301812451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77347680330374449609666405 14502690061945209301812451)
            ·
              refine ⟨21754035092917813952718677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14502690061945209301812451 21754035092917813952718677)
              ·
                refine ⟨127465049372565316129211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21754035092917813952718677 127465049372565316129211)
                ·
                  rfl

theorem cell23_6702407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 9].length) (baseStart_6702407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702407 prefixEnd_6702407 := by exact prefixLift 6702407
  have htrace : WordTrace (prefixWord ++ tailWord_6702407) baseStart_6702407 baseEnd_6702407 := by
    simpa [prefixWord, tailWord_6702407, baseEnd_6702407] using wordTrace_append hprefix tailTrace_6702407
  have hstable : (prefixWord ++ tailWord_6702407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702407).length < 2 ^ (prefixWord ++ tailWord_6702407).sum := by decide
  have hdescent : baseEnd_6702407 < baseStart_6702407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702421 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6702421 : Nat := 118140960795 + 6702421 * 2 ^ 59
def prefixEnd_6702421 : Nat := 4983230072969 + 3 ^ 40 * 6702421 * 2
def baseEnd_6702421 : Nat := 3441563521788426480713633

theorem tailTrace_6702421 : CollatzResearch.WordTrace tailWord_6702421 prefixEnd_6702421 3441563521788426480713633 := by
  unfold tailWord_6702421
  simp only [CollatzResearch.WordTrace]
  refine ⟨244457376851280874219091117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162971584567520582812727411 244457376851280874219091117)
  ·
    refine ⟨91671516319230327832159169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244457376851280874219091117 91671516319230327832159169)
    ·
      refine ⟨68753637239422745874119377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91671516319230327832159169 68753637239422745874119377)
      ·
        refine ⟨51565227929567059405589533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68753637239422745874119377 51565227929567059405589533)
        ·
          refine ⟨19336960473587647277096075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51565227929567059405589533 19336960473587647277096075)
          ·
            refine ⟨29005440710381470915644113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336960473587647277096075 29005440710381470915644113)
            ·
              refine ⟨21754080532786103186733085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29005440710381470915644113 21754080532786103186733085)
              ·
                refine ⟨8157780199794788695024907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21754080532786103186733085 8157780199794788695024907)
                ·
                  refine ⟨12236670299692183042537361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157780199794788695024907 12236670299692183042537361)
                  ·
                    refine ⟨9177502724769137281903021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12236670299692183042537361 9177502724769137281903021)
                    ·
                      refine ⟨3441563521788426480713633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177502724769137281903021 3441563521788426480713633)
                      ·
                        rfl

theorem cell23_6702421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6702421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702421 prefixEnd_6702421 := by exact prefixLift 6702421
  have htrace : WordTrace (prefixWord ++ tailWord_6702421) baseStart_6702421 baseEnd_6702421 := by
    simpa [prefixWord, tailWord_6702421, baseEnd_6702421] using wordTrace_append hprefix tailTrace_6702421
  have hstable : (prefixWord ++ tailWord_6702421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702421).length < 2 ^ (prefixWord ++ tailWord_6702421).sum := by decide
  have hdescent : baseEnd_6702421 < baseStart_6702421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702429 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6702429 : Nat := 118140960795 + 6702429 * 2 ^ 59
def prefixEnd_6702429 : Nat := 4983230072969 + 3 ^ 40 * 6702429 * 2
def baseEnd_6702429 : Nat := 3441567629633662449413597

theorem tailTrace_6702429 : CollatzResearch.WordTrace tailWord_6702429 prefixEnd_6702429 3441567629633662449413597 := by
  unfold tailWord_6702429
  simp only [CollatzResearch.WordTrace]
  refine ⟨244457668635251891585382341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162971779090167927723588227 244457668635251891585382341)
  ·
    refine ⟨45835812869109729672259189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244457668635251891585382341 45835812869109729672259189)
    ·
      refine ⟨4297107456479037156774299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45835812869109729672259189 4297107456479037156774299)
      ·
        refine ⟨6445661184718555735161449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297107456479037156774299 6445661184718555735161449)
        ·
          refine ⟨4834245888538916801371087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6445661184718555735161449 4834245888538916801371087)
          ·
            refine ⟨7251368832808375202056631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834245888538916801371087 7251368832808375202056631)
            ·
              refine ⟨10877053249212562803084947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251368832808375202056631 10877053249212562803084947)
              ·
                refine ⟨16315579873818844204627421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10877053249212562803084947 16315579873818844204627421)
                ·
                  refine ⟨6118342452682066576735283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16315579873818844204627421 6118342452682066576735283)
                  ·
                    refine ⟨9177513679023099865102925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118342452682066576735283 9177513679023099865102925)
                    ·
                      refine ⟨3441567629633662449413597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177513679023099865102925 3441567629633662449413597)
                      ·
                        rfl

theorem cell23_6702429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6702429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702429 prefixEnd_6702429 := by exact prefixLift 6702429
  have htrace : WordTrace (prefixWord ++ tailWord_6702429) baseStart_6702429 baseEnd_6702429 := by
    simpa [prefixWord, tailWord_6702429, baseEnd_6702429] using wordTrace_append hprefix tailTrace_6702429
  have hstable : (prefixWord ++ tailWord_6702429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702429).length < 2 ^ (prefixWord ++ tailWord_6702429).sum := by decide
  have hdescent : baseEnd_6702429 < baseStart_6702429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702437 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_6702437 : Nat := 118140960795 + 6702437 * 2 ^ 59
def prefixEnd_6702437 : Nat := 4983230072969 + 3 ^ 40 * 6702437 * 2
def baseEnd_6702437 : Nat := 1147190579159632806037853

theorem tailTrace_6702437 : CollatzResearch.WordTrace tailWord_6702437 prefixEnd_6702437 1147190579159632806037853 := by
  unfold tailWord_6702437
  simp only [CollatzResearch.WordTrace]
  refine ⟨244457960419222908951673565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162971973612815272634449043 244457960419222908951673565)
  ·
    refine ⟨91671735157208590856877587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244457960419222908951673565 91671735157208590856877587)
    ·
      refine ⟨137507602735812886285316381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91671735157208590856877587 137507602735812886285316381)
      ·
        refine ⟨51565351025929832356993643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137507602735812886285316381 51565351025929832356993643)
        ·
          refine ⟨77348026538894748535490465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51565351025929832356993643 77348026538894748535490465)
          ·
            refine ⟨58011019904171061401617849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77348026538894748535490465 58011019904171061401617849)
            ·
              refine ⟨43508264928128296051213387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58011019904171061401617849 43508264928128296051213387)
              ·
                refine ⟨65262397392192444076820081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43508264928128296051213387 65262397392192444076820081)
                ·
                  refine ⟨48946798044144333057615061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65262397392192444076820081 48946798044144333057615061)
                  ·
                    refine ⟨1147190579159632806037853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48946798044144333057615061 1147190579159632806037853)
                    ·
                      rfl

theorem cell23_6702437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_6702437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702437 prefixEnd_6702437 := by exact prefixLift 6702437
  have htrace : WordTrace (prefixWord ++ tailWord_6702437) baseStart_6702437 baseEnd_6702437 := by
    simpa [prefixWord, tailWord_6702437, baseEnd_6702437] using wordTrace_append hprefix tailTrace_6702437
  have hstable : (prefixWord ++ tailWord_6702437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702437).length < 2 ^ (prefixWord ++ tailWord_6702437).sum := by decide
  have hdescent : baseEnd_6702437 < baseStart_6702437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702461 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_6702461 : Nat := 118140960795 + 6702461 * 2 ^ 59
def prefixEnd_6702461 : Nat := 4983230072969 + 3 ^ 40 * 6702461 * 2
def baseEnd_6702461 : Nat := 3441584061014606324213449

theorem tailTrace_6702461 : CollatzResearch.WordTrace tailWord_6702461 prefixEnd_6702461 3441584061014606324213449 := by
  unfold tailWord_6702461
  simp only [CollatzResearch.WordTrace]
  refine ⟨244458835771135961050547237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162972557180757307367031491 244458835771135961050547237)
  ·
    refine ⟨45836031707087992696977607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244458835771135961050547237 45836031707087992696977607)
    ·
      refine ⟨68754047560631989045466411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45836031707087992696977607 68754047560631989045466411)
      ·
        refine ⟨103131071340947983568199617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68754047560631989045466411 103131071340947983568199617)
        ·
          refine ⟨77348303505710987676149713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103131071340947983568199617 77348303505710987676149713)
          ·
            refine ⟨58011227629283240757112285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77348303505710987676149713 58011227629283240757112285)
            ·
              refine ⟨21754210360981215283917107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58011227629283240757112285 21754210360981215283917107)
              ·
                refine ⟨32631315541471822925875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21754210360981215283917107 32631315541471822925875661)
                ·
                  refine ⟨12236743328051933597203373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32631315541471822925875661 12236743328051933597203373)
                  ·
                    refine ⟨4588778748019475098951265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12236743328051933597203373 4588778748019475098951265)
                    ·
                      refine ⟨3441584061014606324213449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588778748019475098951265 3441584061014606324213449)
                      ·
                        rfl

theorem cell23_6702461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_6702461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702461 prefixEnd_6702461 := by exact prefixLift 6702461
  have htrace : WordTrace (prefixWord ++ tailWord_6702461) baseStart_6702461 baseEnd_6702461 := by
    simpa [prefixWord, tailWord_6702461, baseEnd_6702461] using wordTrace_append hprefix tailTrace_6702461
  have hstable : (prefixWord ++ tailWord_6702461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702461).length < 2 ^ (prefixWord ++ tailWord_6702461).sum := by decide
  have hdescent : baseEnd_6702461 < baseStart_6702461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702487 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6702487 : Nat := 118140960795 + 6702487 * 2 ^ 59
def prefixEnd_6702487 : Nat := 4983230072969 + 3 ^ 40 * 6702487 * 2
def baseEnd_6702487 : Nat := 3441597411511623222488329

theorem tailTrace_6702487 : CollatzResearch.WordTrace tailWord_6702487 prefixEnd_6702487 3441597411511623222488329 := by
  unfold tailWord_6702487
  simp only [CollatzResearch.WordTrace]
  refine ⟨244459784069041767490993715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162973189379361178327329143 244459784069041767490993715)
  ·
    refine ⟨366689676103562651236490573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244459784069041767490993715 366689676103562651236490573)
    ·
      refine ⟨137508628538835994213683965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366689676103562651236490573 137508628538835994213683965)
      ·
        refine ⟨51565735702063497830131487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137508628538835994213683965 51565735702063497830131487)
        ·
          refine ⟨77348603553095246745197231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51565735702063497830131487 77348603553095246745197231)
          ·
            refine ⟨116022905329642870117795847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77348603553095246745197231 116022905329642870117795847)
            ·
              refine ⟨174034357994464305176693771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116022905329642870117795847 174034357994464305176693771)
              ·
                refine ⟨261051536991696457765040657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174034357994464305176693771 261051536991696457765040657)
                ·
                  refine ⟨195788652743772343323780493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261051536991696457765040657 195788652743772343323780493)
                  ·
                    refine ⟨73420744778914628746417685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195788652743772343323780493 73420744778914628746417685)
                    ·
                      refine ⟨3441597411511623222488329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73420744778914628746417685 3441597411511623222488329)
                      ·
                        rfl

theorem cell23_6702487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6702487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702487 prefixEnd_6702487 := by exact prefixLift 6702487
  have htrace : WordTrace (prefixWord ++ tailWord_6702487) baseStart_6702487 baseEnd_6702487 := by
    simpa [prefixWord, tailWord_6702487, baseEnd_6702487] using wordTrace_append hprefix tailTrace_6702487
  have hstable : (prefixWord ++ tailWord_6702487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702487).length < 2 ^ (prefixWord ++ tailWord_6702487).sum := by decide
  have hdescent : baseEnd_6702487 < baseStart_6702487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702508 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_6702508 : Nat := 118140960795 + 6702508 * 2 ^ 59
def prefixEnd_6702508 : Nat := 4983230072969 + 3 ^ 40 * 6702508 * 2
def baseEnd_6702508 : Nat := 3441608194605367640325733

theorem tailTrace_6702508 : CollatzResearch.WordTrace tailWord_6702508 prefixEnd_6702508 3441608194605367640325733 := by
  unfold tailWord_6702508
  simp only [CollatzResearch.WordTrace]
  refine ⟨122230275000982844038754089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162973700001310458718338785 122230275000982844038754089)
  ·
    refine ⟨91672706250737133029065567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122230275000982844038754089 91672706250737133029065567)
    ·
      refine ⟨137509059376105699543598351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91672706250737133029065567 137509059376105699543598351)
      ·
        refine ⟨206263589064158549315397527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137509059376105699543598351 206263589064158549315397527)
        ·
          refine ⟨309395383596237823973096291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206263589064158549315397527 309395383596237823973096291)
          ·
            refine ⟨464093075394356735959644437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309395383596237823973096291 464093075394356735959644437)
            ·
              refine ⟨21754362909110471998108333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 464093075394356735959644437 21754362909110471998108333)
              ·
                refine ⟨8157886090916426999290625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21754362909110471998108333 8157886090916426999290625)
                ·
                  refine ⟨6118414568187320249467969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8157886090916426999290625 6118414568187320249467969)
                  ·
                    refine ⟨4588810926140490187100977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6118414568187320249467969 4588810926140490187100977)
                    ·
                      refine ⟨3441608194605367640325733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588810926140490187100977 3441608194605367640325733)
                      ·
                        rfl

theorem cell23_6702508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_6702508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702508 prefixEnd_6702508 := by exact prefixLift 6702508
  have htrace : WordTrace (prefixWord ++ tailWord_6702508) baseStart_6702508 baseEnd_6702508 := by
    simpa [prefixWord, tailWord_6702508, baseEnd_6702508] using wordTrace_append hprefix tailTrace_6702508
  have hstable : (prefixWord ++ tailWord_6702508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702508).length < 2 ^ (prefixWord ++ tailWord_6702508).sum := by decide
  have hdescent : baseEnd_6702508 < baseStart_6702508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702574 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6702574 : Nat := 118140960795 + 6702574 * 2 ^ 59
def prefixEnd_6702574 : Nat := 4983230072969 + 3 ^ 40 * 6702574 * 2
def baseEnd_6702574 : Nat := 1147214028109521460700143

theorem tailTrace_6702574 : CollatzResearch.WordTrace tailWord_6702574 prefixEnd_6702574 1147214028109521460700143 := by
  unfold tailWord_6702574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557869652465822668676347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162975304813151054232940517 30557869652465822668676347)
  ·
    refine ⟨45836804478698734003014521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30557869652465822668676347 45836804478698734003014521)
    ·
      refine ⟨34377603359024050502260891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45836804478698734003014521 34377603359024050502260891)
      ·
        refine ⟨51566405038536075753391337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34377603359024050502260891 51566405038536075753391337)
        ·
          refine ⟨38674803778902056815043503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51566405038536075753391337 38674803778902056815043503)
          ·
            refine ⟨58012205668353085222565255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38674803778902056815043503 58012205668353085222565255)
            ·
              refine ⟨87018308502529627833847883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58012205668353085222565255 87018308502529627833847883)
              ·
                refine ⟨130527462753794441750771825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87018308502529627833847883 130527462753794441750771825)
                ·
                  refine ⟨97895597065345831313078869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130527462753794441750771825 97895597065345831313078869)
                  ·
                    refine ⟨1147214028109521460700143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97895597065345831313078869 1147214028109521460700143)
                    ·
                      rfl

theorem cell23_6702574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6702574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702574 prefixEnd_6702574 := by exact prefixLift 6702574
  have htrace : WordTrace (prefixWord ++ tailWord_6702574) baseStart_6702574 baseEnd_6702574 := by
    simpa [prefixWord, tailWord_6702574, baseEnd_6702574] using wordTrace_append hprefix tailTrace_6702574
  have hstable : (prefixWord ++ tailWord_6702574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702574).length < 2 ^ (prefixWord ++ tailWord_6702574).sum := by decide
  have hdescent : baseEnd_6702574 < baseStart_6702574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702601 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_6702601 : Nat := 118140960795 + 6702601 * 2 ^ 59
def prefixEnd_6702601 : Nat := 4983230072969 + 3 ^ 40 * 6702601 * 2
def baseEnd_6702601 : Nat := 3441655948306235776462805

theorem tailTrace_6702601 : CollatzResearch.WordTrace tailWord_6702601 prefixEnd_6702601 3441655948306235776462805 := by
  unfold tailWord_6702601
  simp only [CollatzResearch.WordTrace]
  refine ⟨244463941990628764960643657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162975961327085843307095771 244463941990628764960643657)
  ·
    refine ⟨183347956492971573720482743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244463941990628764960643657 183347956492971573720482743)
    ·
      refine ⟨275021934739457360580724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183347956492971573720482743 275021934739457360580724115)
      ·
        refine ⟨412532902109186040871086173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275021934739457360580724115 412532902109186040871086173)
        ·
          refine ⟨154699838290944765326657315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412532902109186040871086173 154699838290944765326657315)
          ·
            refine ⟨232049757436417147989985973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154699838290944765326657315 232049757436417147989985973)
            ·
              refine ⟨21754664759664107624061185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232049757436417147989985973 21754664759664107624061185)
              ·
                refine ⟨16315998569748080718045889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21754664759664107624061185 16315998569748080718045889)
                ·
                  refine ⟨12236998927311060538534417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16315998569748080718045889 12236998927311060538534417)
                  ·
                    refine ⟨9177749195483295403900813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12236998927311060538534417 9177749195483295403900813)
                    ·
                      refine ⟨3441655948306235776462805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9177749195483295403900813 3441655948306235776462805)
                      ·
                        rfl

theorem cell23_6702601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_6702601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702601 prefixEnd_6702601 := by exact prefixLift 6702601
  have htrace : WordTrace (prefixWord ++ tailWord_6702601) baseStart_6702601 baseEnd_6702601 := by
    simpa [prefixWord, tailWord_6702601, baseEnd_6702601] using wordTrace_append hprefix tailTrace_6702601
  have hstable : (prefixWord ++ tailWord_6702601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702601).length < 2 ^ (prefixWord ++ tailWord_6702601).sum := by decide
  have hdescent : baseEnd_6702601 < baseStart_6702601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702605 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6702605 : Nat := 118140960795 + 6702605 * 2 ^ 59
def prefixEnd_6702605 : Nat := 4983230072969 + 3 ^ 40 * 6702605 * 2
def baseEnd_6702605 : Nat := 3441658002228853760812787

theorem tailTrace_6702605 : CollatzResearch.WordTrace tailWord_6702605 prefixEnd_6702605 3441658002228853760812787 := by
  unfold tailWord_6702605
  simp only [CollatzResearch.WordTrace]
  refine ⟨244464087882614273643789269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162976058588409515762526179 244464087882614273643789269)
  ·
    refine ⟨5729627059748772038526311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 244464087882614273643789269 5729627059748772038526311)
    ·
      refine ⟨8594440589623158057789467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5729627059748772038526311 8594440589623158057789467)
      ·
        refine ⟨12891660884434737086684201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8594440589623158057789467 12891660884434737086684201)
        ·
          refine ⟨9668745663326052815013151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12891660884434737086684201 9668745663326052815013151)
          ·
            refine ⟨14503118494989079222519727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9668745663326052815013151 14503118494989079222519727)
            ·
              refine ⟨21754677742483618833779591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14503118494989079222519727 21754677742483618833779591)
              ·
                refine ⟨32632016613725428250669387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21754677742483618833779591 32632016613725428250669387)
                ·
                  refine ⟨48948024920588142376004081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32632016613725428250669387 48948024920588142376004081)
                  ·
                    refine ⟨36711018690441106782003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48948024920588142376004081 36711018690441106782003061)
                    ·
                      refine ⟨3441658002228853760812787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36711018690441106782003061 3441658002228853760812787)
                      ·
                        rfl

theorem cell23_6702605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6702605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702605 prefixEnd_6702605 := by exact prefixLift 6702605
  have htrace : WordTrace (prefixWord ++ tailWord_6702605) baseStart_6702605 baseEnd_6702605 := by
    simpa [prefixWord, tailWord_6702605, baseEnd_6702605] using wordTrace_append hprefix tailTrace_6702605
  have hstable : (prefixWord ++ tailWord_6702605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702605).length < 2 ^ (prefixWord ++ tailWord_6702605).sum := by decide
  have hdescent : baseEnd_6702605 < baseStart_6702605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702621 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 6]
def baseStart_6702621 : Nat := 118140960795 + 6702621 * 2 ^ 59
def prefixEnd_6702621 : Nat := 4983230072969 + 3 ^ 40 * 6702621 * 2
def baseEnd_6702621 : Nat := 382407357546591744245857

theorem tailTrace_6702621 : CollatzResearch.WordTrace tailWord_6702621 prefixEnd_6702621 382407357546591744245857 := by
  unfold tailWord_6702621
  simp only [CollatzResearch.WordTrace]
  refine ⟨244464671450556308376371717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162976447633704205584247811 244464671450556308376371717)
  ·
    refine ⟨45837125896979307820569697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244464671450556308376371717 45837125896979307820569697)
    ·
      refine ⟨34377844422734480865427273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45837125896979307820569697 34377844422734480865427273)
      ·
        refine ⟨25783383317050860649070455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34377844422734480865427273 25783383317050860649070455)
        ·
          refine ⟨38675074975576290973605683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25783383317050860649070455 38675074975576290973605683)
          ·
            refine ⟨58012612463364436460408525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38675074975576290973605683 58012612463364436460408525)
            ·
              refine ⟨21754729673761663672653197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58012612463364436460408525 21754729673761663672653197)
              ·
                refine ⟨8158023627660623877244949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21754729673761663672653197 8158023627660623877244949)
                ·
                  refine ⟨382407357546591744245857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8158023627660623877244949 382407357546591744245857)
                  ·
                    rfl

theorem cell23_6702621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_6702621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702621 prefixEnd_6702621 := by exact prefixLift 6702621
  have htrace : WordTrace (prefixWord ++ tailWord_6702621) baseStart_6702621 baseEnd_6702621 := by
    simpa [prefixWord, tailWord_6702621, baseEnd_6702621] using wordTrace_append hprefix tailTrace_6702621
  have hstable : (prefixWord ++ tailWord_6702621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702621).length < 2 ^ (prefixWord ++ tailWord_6702621).sum := by decide
  have hdescent : baseEnd_6702621 < baseStart_6702621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702671 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 6, 2]
def baseStart_6702671 : Nat := 118140960795 + 6702671 * 2 ^ 59
def prefixEnd_6702671 : Nat := 4983230072969 + 3 ^ 40 * 6702671 * 2
def baseEnd_6702671 : Nat := 3441691891952050502587483

theorem tailTrace_6702671 : CollatzResearch.WordTrace tailWord_6702671 prefixEnd_6702671 3441691891952050502587483 := by
  unfold tailWord_6702671
  simp only [CollatzResearch.WordTrace]
  refine ⟨244466495100375166915691867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162977663400250111277127911 244466495100375166915691867)
  ·
    refine ⟨366699742650562750373537801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244466495100375166915691867 366699742650562750373537801)
    ·
      refine ⟨275024806987922062780153351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366699742650562750373537801 275024806987922062780153351)
      ·
        refine ⟨412537210481883094170230027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275024806987922062780153351 412537210481883094170230027)
        ·
          refine ⟨618805815722824641255345041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412537210481883094170230027 618805815722824641255345041)
          ·
            refine ⟨464104361792118480941508781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618805815722824641255345041 464104361792118480941508781)
            ·
              refine ⟨174039135672044430353065793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464104361792118480941508781 174039135672044430353065793)
              ·
                refine ⟨130529351754033322764799345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174039135672044430353065793 130529351754033322764799345)
                ·
                  refine ⟨97897013815524992073599509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130529351754033322764799345 97897013815524992073599509)
                  ·
                    refine ⟨4588922522602734003449977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97897013815524992073599509 4588922522602734003449977)
                    ·
                      refine ⟨3441691891952050502587483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4588922522602734003449977 3441691891952050502587483)
                      ·
                        rfl

theorem cell23_6702671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6, 2].length) (baseStart_6702671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702671 prefixEnd_6702671 := by exact prefixLift 6702671
  have htrace : WordTrace (prefixWord ++ tailWord_6702671) baseStart_6702671 baseEnd_6702671 := by
    simpa [prefixWord, tailWord_6702671, baseEnd_6702671] using wordTrace_append hprefix tailTrace_6702671
  have hstable : (prefixWord ++ tailWord_6702671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702671).length < 2 ^ (prefixWord ++ tailWord_6702671).sum := by decide
  have hdescent : baseEnd_6702671 < baseStart_6702671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702702 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_6702702 : Nat := 118140960795 + 6702702 * 2 ^ 59
def prefixEnd_6702702 : Nat := 4983230072969 + 3 ^ 40 * 6702702 * 2
def baseEnd_6702702 : Nat := 1147235936617446627099947

theorem tailTrace_6702702 : CollatzResearch.WordTrace tailWord_6702702 prefixEnd_6702702 1147235936617446627099947 := by
  unfold tailWord_6702702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30558453220407857401258795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162978417175508572806713573 30558453220407857401258795)
  ·
    refine ⟨45837679830611786101888193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30558453220407857401258795 45837679830611786101888193)
    ·
      refine ⟨34378259872958839576416145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45837679830611786101888193 34378259872958839576416145)
      ·
        refine ⟨25783694904719129682312109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34378259872958839576416145 25783694904719129682312109)
        ·
          refine ⟨9668885589269673630867041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25783694904719129682312109 9668885589269673630867041)
          ·
            refine ⟨7251664191952255223150281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9668885589269673630867041 7251664191952255223150281)
            ·
              refine ⟨5438748143964191417362711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7251664191952255223150281 5438748143964191417362711)
              ·
                refine ⟨8158122215946287126044067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438748143964191417362711 8158122215946287126044067)
                ·
                  refine ⟨12237183323919430689066101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8158122215946287126044067 12237183323919430689066101)
                  ·
                    refine ⟨1147235936617446627099947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12237183323919430689066101 1147235936617446627099947)
                    ·
                      rfl

theorem cell23_6702702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_6702702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702702 prefixEnd_6702702 := by exact prefixLift 6702702
  have htrace : WordTrace (prefixWord ++ tailWord_6702702) baseStart_6702702 baseEnd_6702702 := by
    simpa [prefixWord, tailWord_6702702, baseEnd_6702702] using wordTrace_append hprefix tailTrace_6702702
  have hstable : (prefixWord ++ tailWord_6702702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702702).length < 2 ^ (prefixWord ++ tailWord_6702702).sum := by decide
  have hdescent : baseEnd_6702702 < baseStart_6702702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702781 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6702781 : Nat := 118140960795 + 6702781 * 2 ^ 59
def prefixEnd_6702781 : Nat := 4983230072969 + 3 ^ 40 * 6702781 * 2
def baseEnd_6702781 : Nat := 3441748374824045072211977

theorem tailTrace_6702781 : CollatzResearch.WordTrace tailWord_6702781 prefixEnd_6702781 3441748374824045072211977 := by
  unfold tailWord_6702781
  simp only [CollatzResearch.WordTrace]
  refine ⟨244470507129976655702196197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162980338086651103801464131 244470507129976655702196197)
  ·
    refine ⟨45838220086870622944161787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244470507129976655702196197 45838220086870622944161787)
    ·
      refine ⟨68757330130305934416242681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45838220086870622944161787 68757330130305934416242681)
      ·
        refine ⟨51567997597729450812182011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68757330130305934416242681 51567997597729450812182011)
        ·
          refine ⟨77351996396594176218273017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51567997597729450812182011 77351996396594176218273017)
          ·
            refine ⟨58013997297445632163704763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77351996396594176218273017 58013997297445632163704763)
            ·
              refine ⟨87020995946168448245557145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58013997297445632163704763 87020995946168448245557145)
              ·
                refine ⟨65265746959626336184167859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87020995946168448245557145 65265746959626336184167859)
                ·
                  refine ⟨97898620439439504276251789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65265746959626336184167859 97898620439439504276251789)
                  ·
                    refine ⟨36711982664789814103594421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97898620439439504276251789 36711982664789814103594421)
                    ·
                      refine ⟨3441748374824045072211977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36711982664789814103594421 3441748374824045072211977)
                      ·
                        rfl

theorem cell23_6702781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6702781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702781 prefixEnd_6702781 := by exact prefixLift 6702781
  have htrace : WordTrace (prefixWord ++ tailWord_6702781) baseStart_6702781 baseEnd_6702781 := by
    simpa [prefixWord, tailWord_6702781, baseEnd_6702781] using wordTrace_append hprefix tailTrace_6702781
  have hstable : (prefixWord ++ tailWord_6702781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702781).length < 2 ^ (prefixWord ++ tailWord_6702781).sum := by decide
  have hdescent : baseEnd_6702781 < baseStart_6702781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702791 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_6702791 : Nat := 118140960795 + 6702791 * 2 ^ 59
def prefixEnd_6702791 : Nat := 4983230072969 + 3 ^ 40 * 6702791 * 2
def baseEnd_6702791 : Nat := 3441753509630590033086931

theorem tailTrace_6702791 : CollatzResearch.WordTrace tailWord_6702791 prefixEnd_6702791 3441753509630590033086931 := by
  unfold tailWord_6702791
  simp only [CollatzResearch.WordTrace]
  refine ⟨244470871859940427410060227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162980581239960284940040151 244470871859940427410060227)
  ·
    refine ⟨366706307789910641115090341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244470871859940427410060227 366706307789910641115090341)
    ·
      refine ⟨68757432710608245209079439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366706307789910641115090341 68757432710608245209079439)
      ·
        refine ⟨103136149065912367813619159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68757432710608245209079439 103136149065912367813619159)
        ·
          refine ⟨154704223598868551720428739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103136149065912367813619159 154704223598868551720428739)
          ·
            refine ⟨232056335398302827580643109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154704223598868551720428739 232056335398302827580643109)
            ·
              refine ⟨43510562887181780171370583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232056335398302827580643109 43510562887181780171370583)
              ·
                refine ⟨65265844330772670257055875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43510562887181780171370583 65265844330772670257055875)
                ·
                  refine ⟨97898766496159005385583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65265844330772670257055875 97898766496159005385583813)
                  ·
                    refine ⟨18356018718029813509796965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97898766496159005385583813 18356018718029813509796965)
                    ·
                      refine ⟨3441753509630590033086931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18356018718029813509796965 3441753509630590033086931)
                      ·
                        rfl

theorem cell23_6702791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_6702791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702791 prefixEnd_6702791 := by exact prefixLift 6702791
  have htrace : WordTrace (prefixWord ++ tailWord_6702791) baseStart_6702791 baseEnd_6702791 := by
    simpa [prefixWord, tailWord_6702791, baseEnd_6702791] using wordTrace_append hprefix tailTrace_6702791
  have hstable : (prefixWord ++ tailWord_6702791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702791).length < 2 ^ (prefixWord ++ tailWord_6702791).sum := by decide
  have hdescent : baseEnd_6702791 < baseStart_6702791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702829 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6702829 : Nat := 118140960795 + 6702829 * 2 ^ 59
def prefixEnd_6702829 : Nat := 4983230072969 + 3 ^ 40 * 6702829 * 2
def baseEnd_6702829 : Nat := 3441773021895460884411757

theorem tailTrace_6702829 : CollatzResearch.WordTrace tailWord_6702829 prefixEnd_6702829 3441773021895460884411757 := by
  unfold tailWord_6702829
  simp only [CollatzResearch.WordTrace]
  refine ⟨244472257833802759899943541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162981505222535173266629027 244472257833802759899943541)
  ·
    refine ⟨22919274171919008740619707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244472257833802759899943541 22919274171919008740619707)
    ·
      refine ⟨34378911257878513110929561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22919274171919008740619707 34378911257878513110929561)
      ·
        refine ⟨25784183443408884833197171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34378911257878513110929561 25784183443408884833197171)
        ·
          refine ⟨38676275165113327249795757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25784183443408884833197171 38676275165113327249795757)
          ·
            refine ⟨14503603186917497718673409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38676275165113327249795757 14503603186917497718673409)
            ·
              refine ⟨10877702390188123289005057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14503603186917497718673409 10877702390188123289005057)
              ·
                refine ⟨8158276792641092466753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10877702390188123289005057 8158276792641092466753793)
                ·
                  refine ⟨6118707594480819350065345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158276792641092466753793 6118707594480819350065345)
                  ·
                    refine ⟨4589030695860614512549009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6118707594480819350065345 4589030695860614512549009)
                    ·
                      refine ⟨3441773021895460884411757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589030695860614512549009 3441773021895460884411757)
                      ·
                        rfl

theorem cell23_6702829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6702829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702829 prefixEnd_6702829 := by exact prefixLift 6702829
  have htrace : WordTrace (prefixWord ++ tailWord_6702829) baseStart_6702829 baseEnd_6702829 := by
    simpa [prefixWord, tailWord_6702829, baseEnd_6702829] using wordTrace_append hprefix tailTrace_6702829
  have hstable : (prefixWord ++ tailWord_6702829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702829).length < 2 ^ (prefixWord ++ tailWord_6702829).sum := by decide
  have hdescent : baseEnd_6702829 < baseStart_6702829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702835 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 5]
def baseStart_6702835 : Nat := 118140960795 + 6702835 * 2 ^ 59
def prefixEnd_6702835 : Nat := 4983230072969 + 3 ^ 40 * 6702835 * 2
def baseEnd_6702835 : Nat := 382419566975487540104081

theorem tailTrace_6702835 : CollatzResearch.WordTrace tailWord_6702835 prefixEnd_6702835 382419566975487540104081 := by
  unfold tailWord_6702835
  simp only [CollatzResearch.WordTrace]
  refine ⟨244472476671781022924661959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162981651114520681949774639 244472476671781022924661959)
  ·
    refine ⟨366708715007671534386992939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244472476671781022924661959 366708715007671534386992939)
    ·
      refine ⟨550063072511507301580489409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366708715007671534386992939 550063072511507301580489409)
      ·
        refine ⟨412547304383630476185367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550063072511507301580489409 412547304383630476185367057)
        ·
          refine ⟨309410478287722857139025293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412547304383630476185367057 309410478287722857139025293)
          ·
            refine ⟨116028929357896071427134485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309410478287722857139025293 116028929357896071427134485)
            ·
              refine ⟨5438856063651378348146929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116028929357896071427134485 5438856063651378348146929)
              ·
                refine ⟨4079142047738533761110197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438856063651378348146929 4079142047738533761110197)
                ·
                  refine ⟨382419566975487540104081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079142047738533761110197 382419566975487540104081)
                  ·
                    rfl

theorem cell23_6702835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 5].length) (baseStart_6702835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702835 prefixEnd_6702835 := by exact prefixLift 6702835
  have htrace : WordTrace (prefixWord ++ tailWord_6702835) baseStart_6702835 baseEnd_6702835 := by
    simpa [prefixWord, tailWord_6702835, baseEnd_6702835] using wordTrace_append hprefix tailTrace_6702835
  have hstable : (prefixWord ++ tailWord_6702835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702835).length < 2 ^ (prefixWord ++ tailWord_6702835).sum := by decide
  have hdescent : baseEnd_6702835 < baseStart_6702835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702885 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_6702885 : Nat := 118140960795 + 6702885 * 2 ^ 59
def prefixEnd_6702885 : Nat := 4983230072969 + 3 ^ 40 * 6702885 * 2
def baseEnd_6702885 : Nat := 3441801776812112665311499

theorem tailTrace_6702885 : CollatzResearch.WordTrace tailWord_6702885 prefixEnd_6702885 3441801776812112665311499 := by
  unfold tailWord_6702885
  simp only [CollatzResearch.WordTrace]
  refine ⟨244474300321599881463982109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162982866881066587642654739 244474300321599881463982109)
  ·
    refine ⟨91677862620599955548993291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244474300321599881463982109 91677862620599955548993291)
    ·
      refine ⟨137516793930899933323489937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91677862620599955548993291 137516793930899933323489937)
      ·
        refine ⟨103137595448174949992617453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137516793930899933323489937 103137595448174949992617453)
        ·
          refine ⟨38676598293065606247231545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103137595448174949992617453 38676598293065606247231545)
          ·
            refine ⟨29007448719799204685423659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38676598293065606247231545 29007448719799204685423659)
            ·
              refine ⟨43511173079698807028135489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29007448719799204685423659 43511173079698807028135489)
              ·
                refine ⟨32633379809774105271101617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43511173079698807028135489 32633379809774105271101617)
                ·
                  refine ⟨24475034857330578953326213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32633379809774105271101617 24475034857330578953326213)
                  ·
                    refine ⟨4589069035749483553748665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24475034857330578953326213 4589069035749483553748665)
                    ·
                      refine ⟨3441801776812112665311499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589069035749483553748665 3441801776812112665311499)
                      ·
                        rfl

theorem cell23_6702885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_6702885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702885 prefixEnd_6702885 := by exact prefixLift 6702885
  have htrace : WordTrace (prefixWord ++ tailWord_6702885) baseStart_6702885 baseEnd_6702885 := by
    simpa [prefixWord, tailWord_6702885, baseEnd_6702885] using wordTrace_append hprefix tailTrace_6702885
  have hstable : (prefixWord ++ tailWord_6702885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702885).length < 2 ^ (prefixWord ++ tailWord_6702885).sum := by decide
  have hdescent : baseEnd_6702885 < baseStart_6702885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702908 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 6]
def baseStart_6702908 : Nat := 118140960795 + 6702908 * 2 ^ 59
def prefixEnd_6702908 : Nat := 4983230072969 + 3 ^ 40 * 6702908 * 2
def baseEnd_6702908 : Nat := 382423731874129563924877

theorem tailTrace_6702908 : CollatzResearch.WordTrace tailWord_6702908 prefixEnd_6702908 382423731874129563924877 := by
  unfold tailWord_6702908
  simp only [CollatzResearch.WordTrace]
  refine ⟨122237569600258278196034689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162983426133677704261379585 122237569600258278196034689)
  ·
    refine ⟨91678177200193708647026017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122237569600258278196034689 91678177200193708647026017)
    ·
      refine ⟨68758632900145281485269513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91678177200193708647026017 68758632900145281485269513)
      ·
        refine ⟨51568974675108961113952135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68758632900145281485269513 51568974675108961113952135)
        ·
          refine ⟨77353462012663441670928203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51568974675108961113952135 77353462012663441670928203)
          ·
            refine ⟨116030193018995162506392305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77353462012663441670928203 116030193018995162506392305)
            ·
              refine ⟨87022644764246371879794229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116030193018995162506392305 87022644764246371879794229)
              ·
                refine ⟨8158372946648097363730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87022644764246371879794229 8158372946648097363730709)
                ·
                  refine ⟨382423731874129563924877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8158372946648097363730709 382423731874129563924877)
                  ·
                    rfl

theorem cell23_6702908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_6702908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702908 prefixEnd_6702908 := by exact prefixLift 6702908
  have htrace : WordTrace (prefixWord ++ tailWord_6702908) baseStart_6702908 baseEnd_6702908 := by
    simpa [prefixWord, tailWord_6702908, baseEnd_6702908] using wordTrace_append hprefix tailTrace_6702908
  have hstable : (prefixWord ++ tailWord_6702908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702908).length < 2 ^ (prefixWord ++ tailWord_6702908).sum := by decide
  have hdescent : baseEnd_6702908 < baseStart_6702908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702925 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6702925 : Nat := 118140960795 + 6702925 * 2 ^ 59
def prefixEnd_6702925 : Nat := 4983230072969 + 3 ^ 40 * 6702925 * 2
def baseEnd_6702925 : Nat := 382424701782032500979035

theorem tailTrace_6702925 : CollatzResearch.WordTrace tailWord_6702925 prefixEnd_6702925 382424701782032500979035 := by
  unfold tailWord_6702925
  simp only [CollatzResearch.WordTrace]
  refine ⟨244475759241454968295438229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162983839494303312196958819 244475759241454968295438229)
  ·
    refine ⟨11459801214443201638848667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244475759241454968295438229 11459801214443201638848667)
    ·
      refine ⟨17189701821664802458273001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459801214443201638848667 17189701821664802458273001)
      ·
        refine ⟨12892276366248601843704751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17189701821664802458273001 12892276366248601843704751)
        ·
          refine ⟨19338414549372902765557127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892276366248601843704751 19338414549372902765557127)
          ·
            refine ⟨29007621824059354148335691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19338414549372902765557127 29007621824059354148335691)
            ·
              refine ⟨43511432736089031222503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29007621824059354148335691 43511432736089031222503537)
              ·
                refine ⟨32633574552066773416877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43511432736089031222503537 32633574552066773416877653)
                ·
                  refine ⟨382424701782032500979035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32633574552066773416877653 382424701782032500979035)
                  ·
                    rfl

theorem cell23_6702925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6702925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702925 prefixEnd_6702925 := by exact prefixLift 6702925
  have htrace : WordTrace (prefixWord ++ tailWord_6702925) baseStart_6702925 baseEnd_6702925 := by
    simpa [prefixWord, tailWord_6702925, baseEnd_6702925] using wordTrace_append hprefix tailTrace_6702925
  have hstable : (prefixWord ++ tailWord_6702925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702925).length < 2 ^ (prefixWord ++ tailWord_6702925).sum := by decide
  have hdescent : baseEnd_6702925 < baseStart_6702925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702929 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 1, 4]
def baseStart_6702929 : Nat := 118140960795 + 6702929 * 2 ^ 59
def prefixEnd_6702929 : Nat := 4983230072969 + 3 ^ 40 * 6702929 * 2
def baseEnd_6702929 : Nat := 1147274789986970164387099

theorem tailTrace_6702929 : CollatzResearch.WordTrace tailWord_6702929 prefixEnd_6702929 1147274789986970164387099 := by
  unfold tailWord_6702929
  simp only [CollatzResearch.WordTrace]
  refine ⟨244475905133440476978583841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162983936755626984652389227 244475905133440476978583841)
  ·
    refine ⟨183356928850080357733937881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244475905133440476978583841 183356928850080357733937881)
    ·
      refine ⟨137517696637560268300453411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183356928850080357733937881 137517696637560268300453411)
      ·
        refine ⟨206276544956340402450680117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137517696637560268300453411 206276544956340402450680117)
        ·
          refine ⟨19338426089656912729751261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206276544956340402450680117 19338426089656912729751261)
          ·
            refine ⟨7251909783621342273656723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19338426089656912729751261 7251909783621342273656723)
            ·
              refine ⟨10877864675432013410485085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251909783621342273656723 10877864675432013410485085)
              ·
                refine ⟨4079199253287005028931907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10877864675432013410485085 4079199253287005028931907)
                ·
                  refine ⟨6118798879930507543397861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079199253287005028931907 6118798879930507543397861)
                  ·
                    refine ⟨1147274789986970164387099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6118798879930507543397861 1147274789986970164387099)
                    ·
                      rfl

theorem cell23_6702929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_6702929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702929 prefixEnd_6702929 := by exact prefixLift 6702929
  have htrace : WordTrace (prefixWord ++ tailWord_6702929) baseStart_6702929 baseEnd_6702929 := by
    simpa [prefixWord, tailWord_6702929, baseEnd_6702929] using wordTrace_append hprefix tailTrace_6702929
  have hstable : (prefixWord ++ tailWord_6702929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702929).length < 2 ^ (prefixWord ++ tailWord_6702929).sum := by decide
  have hdescent : baseEnd_6702929 < baseStart_6702929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702946 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6702946 : Nat := 118140960795 + 6702946 * 2 ^ 59
def prefixEnd_6702946 : Nat := 4983230072969 + 3 ^ 40 * 6702946 * 2
def baseEnd_6702946 : Nat := 1147277699710678975549573

theorem tailTrace_6702946 : CollatzResearch.WordTrace tailWord_6702946 prefixEnd_6702946 1147277699710678975549573 := by
  unfold tailWord_6702946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61119131293594722220488173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162984350116252592587968461 61119131293594722220488173)
  ·
    refine ⟨22919674235098020832683065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61119131293594722220488173 22919674235098020832683065)
    ·
      refine ⟨17189755676323515624512299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22919674235098020832683065 17189755676323515624512299)
      ·
        refine ⟨25784633514485273436768449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189755676323515624512299 25784633514485273436768449)
        ·
          refine ⟨19338475135863955077576337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25784633514485273436768449 19338475135863955077576337)
          ·
            refine ⟨14503856351897966308182253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19338475135863955077576337 14503856351897966308182253)
            ·
              refine ⟨5438946131961737365568345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14503856351897966308182253 5438946131961737365568345)
              ·
                refine ⟨4079209598971303024176259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438946131961737365568345 4079209598971303024176259)
                ·
                  refine ⟨6118814398456954536264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079209598971303024176259 6118814398456954536264389)
                  ·
                    refine ⟨1147277699710678975549573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6118814398456954536264389 1147277699710678975549573)
                    ·
                      rfl

theorem cell23_6702946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6702946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6702946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6702946 prefixEnd_6702946 := by exact prefixLift 6702946
  have htrace : WordTrace (prefixWord ++ tailWord_6702946) baseStart_6702946 baseEnd_6702946 := by
    simpa [prefixWord, tailWord_6702946, baseEnd_6702946] using wordTrace_append hprefix tailTrace_6702946
  have hstable : (prefixWord ++ tailWord_6702946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702946).length < 2 ^ (prefixWord ++ tailWord_6702946).sum := by decide
  have hdescent : baseEnd_6702946 < baseStart_6702946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703002 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_6703002 : Nat := 118140960795 + 6703002 * 2 ^ 59
def prefixEnd_6703002 : Nat := 4983230072969 + 3 ^ 40 * 6703002 * 2
def baseEnd_6703002 : Nat := 1147287284682896235849487

theorem tailTrace_6703002 : CollatzResearch.WordTrace tailWord_6703002 prefixEnd_6703002 1147287284682896235849487 := by
  unfold tailWord_6703002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61119641915544002611497815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162985711774784006963994173 61119641915544002611497815)
  ·
    refine ⟨91679462873316003917246723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61119641915544002611497815 91679462873316003917246723)
    ·
      refine ⟨137519194309974005875870085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91679462873316003917246723 137519194309974005875870085)
      ·
        refine ⟨25784848933120126101725641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137519194309974005875870085 25784848933120126101725641)
        ·
          refine ⟨19338636699840094576294231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25784848933120126101725641 19338636699840094576294231)
          ·
            refine ⟨29007955049760141864441347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19338636699840094576294231 29007955049760141864441347)
            ·
              refine ⟨43511932574640212796662021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29007955049760141864441347 43511932574640212796662021)
              ·
                refine ⟨8158487357745039899374129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43511932574640212796662021 8158487357745039899374129)
                ·
                  refine ⟨6118865518308779924530597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158487357745039899374129 6118865518308779924530597)
                  ·
                    refine ⟨1147287284682896235849487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6118865518308779924530597 1147287284682896235849487)
                    ·
                      rfl

theorem cell23_6703002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_6703002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703002 prefixEnd_6703002 := by exact prefixLift 6703002
  have htrace : WordTrace (prefixWord ++ tailWord_6703002) baseStart_6703002 baseEnd_6703002 := by
    simpa [prefixWord, tailWord_6703002, baseEnd_6703002] using wordTrace_append hprefix tailTrace_6703002
  have hstable : (prefixWord ++ tailWord_6703002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703002).length < 2 ^ (prefixWord ++ tailWord_6703002).sum := by decide
  have hdescent : baseEnd_6703002 < baseStart_6703002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703015 : List Nat := [1, 1, 6, 1, 2, 1, 3, 8]
def baseStart_6703015 : Nat := 118140960795 + 6703015 * 2 ^ 59
def prefixEnd_6703015 : Nat := 4983230072969 + 3 ^ 40 * 6703015 * 2
def baseEnd_6703015 : Nat := 127476612196192487284663

theorem tailTrace_6703015 : CollatzResearch.WordTrace tailWord_6703015 prefixEnd_6703015 127476612196192487284663 := by
  unfold tailWord_6703015
  simp only [CollatzResearch.WordTrace]
  refine ⟨244479041811128913666214499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162986027874085942444142999 244479041811128913666214499)
  ·
    refine ⟨366718562716693370499321749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244479041811128913666214499 366718562716693370499321749)
    ·
      refine ⟨17189932627345001742155707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366718562716693370499321749 17189932627345001742155707)
      ·
        refine ⟨25784898941017502613233561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189932627345001742155707 25784898941017502613233561)
        ·
          refine ⟨19338674205763126959925171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25784898941017502613233561 19338674205763126959925171)
          ·
            refine ⟨29008011308644690439887757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19338674205763126959925171 29008011308644690439887757)
            ·
              refine ⟨10878004240741758914957909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29008011308644690439887757 10878004240741758914957909)
              ·
                refine ⟨127476612196192487284663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10878004240741758914957909 127476612196192487284663)
                ·
                  rfl

theorem cell23_6703015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 8].length) (baseStart_6703015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703015 prefixEnd_6703015 := by exact prefixLift 6703015
  have htrace : WordTrace (prefixWord ++ tailWord_6703015) baseStart_6703015 baseEnd_6703015 := by
    simpa [prefixWord, tailWord_6703015, baseEnd_6703015] using wordTrace_append hprefix tailTrace_6703015
  have hstable : (prefixWord ++ tailWord_6703015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703015).length < 2 ^ (prefixWord ++ tailWord_6703015).sum := by decide
  have hdescent : baseEnd_6703015 < baseStart_6703015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703075 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 6]
def baseStart_6703075 : Nat := 118140960795 + 6703075 * 2 ^ 59
def prefixEnd_6703075 : Nat := 4983230072969 + 3 ^ 40 * 6703075 * 2
def baseEnd_6703075 : Nat := 1147299779378822307311875

theorem tailTrace_6703075 : CollatzResearch.WordTrace tailWord_6703075 prefixEnd_6703075 1147299779378822307311875 := by
  unfold tailWord_6703075
  simp only [CollatzResearch.WordTrace]
  refine ⟨244481230190911543913398679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162987486793941029275599119 244481230190911543913398679)
  ·
    refine ⟨366721845286367315870098019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244481230190911543913398679 366721845286367315870098019)
    ·
      refine ⟨550082767929550973805147029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366721845286367315870098019 550082767929550973805147029)
      ·
        refine ⟨25785129746697701897116267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 550082767929550973805147029 25785129746697701897116267)
        ·
          refine ⟨38677694620046552845674401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25785129746697701897116267 38677694620046552845674401)
          ·
            refine ⟨29008270965034914634255801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38677694620046552845674401 29008270965034914634255801)
            ·
              refine ⟨21756203223776185975691851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29008270965034914634255801 21756203223776185975691851)
              ·
                refine ⟨32634304835664278963537777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21756203223776185975691851 32634304835664278963537777)
                ·
                  refine ⟨24475728626748209222653333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32634304835664278963537777 24475728626748209222653333)
                  ·
                    refine ⟨1147299779378822307311875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24475728626748209222653333 1147299779378822307311875)
                    ·
                      rfl

theorem cell23_6703075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_6703075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703075 prefixEnd_6703075 := by exact prefixLift 6703075
  have htrace : WordTrace (prefixWord ++ tailWord_6703075) baseStart_6703075 baseEnd_6703075 := by
    simpa [prefixWord, tailWord_6703075, baseEnd_6703075] using wordTrace_append hprefix tailTrace_6703075
  have hstable : (prefixWord ++ tailWord_6703075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703075).length < 2 ^ (prefixWord ++ tailWord_6703075).sum := by decide
  have hdescent : baseEnd_6703075 < baseStart_6703075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703086 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_6703086 : Nat := 118140960795 + 6703086 * 2 ^ 59
def prefixEnd_6703086 : Nat := 4983230072969 + 3 ^ 40 * 6703086 * 2
def baseEnd_6703086 : Nat := 3441904986423666378898075

theorem tailTrace_6703086 : CollatzResearch.WordTrace tailWord_6703086 prefixEnd_6703086 3441904986423666378898075 := by
  unfold tailWord_6703086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560203924233961599006139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162987754262581128528032741 30560203924233961599006139)
  ·
    refine ⟨45840305886350942398509209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30560203924233961599006139 45840305886350942398509209)
    ·
      refine ⟨34380229414763206798881907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45840305886350942398509209 34380229414763206798881907)
      ·
        refine ⟨51570344122144810198322861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34380229414763206798881907 51570344122144810198322861)
        ·
          refine ⟨19338879045804303824371073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51570344122144810198322861 19338879045804303824371073)
          ·
            refine ⟨14504159284353227868278305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19338879045804303824371073 14504159284353227868278305)
            ·
              refine ⟨10878119463264920901208729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504159284353227868278305 10878119463264920901208729)
              ·
                refine ⟨8158589597448690675906547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878119463264920901208729 8158589597448690675906547)
                ·
                  refine ⟨12237884396173036013859821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8158589597448690675906547 12237884396173036013859821)
                  ·
                    refine ⟨4589206648564888505197433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12237884396173036013859821 4589206648564888505197433)
                    ·
                      refine ⟨3441904986423666378898075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589206648564888505197433 3441904986423666378898075)
                      ·
                        rfl

theorem cell23_6703086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_6703086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703086 prefixEnd_6703086 := by exact prefixLift 6703086
  have htrace : WordTrace (prefixWord ++ tailWord_6703086) baseStart_6703086 baseEnd_6703086 := by
    simpa [prefixWord, tailWord_6703086, baseEnd_6703086] using wordTrace_append hprefix tailTrace_6703086
  have hstable : (prefixWord ++ tailWord_6703086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703086).length < 2 ^ (prefixWord ++ tailWord_6703086).sum := by decide
  have hdescent : baseEnd_6703086 < baseStart_6703086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703102 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6703102 : Nat := 118140960795 + 6703102 * 2 ^ 59
def prefixEnd_6703102 : Nat := 4983230072969 + 3 ^ 40 * 6703102 * 2
def baseEnd_6703102 : Nat := 3441913202114138316298001

theorem tailTrace_6703102 : CollatzResearch.WordTrace tailWord_6703102 prefixEnd_6703102 3441913202114138316298001 := by
  unfold tailWord_6703102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560276870226715940578945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162988143307875818349754373 30560276870226715940578945)
  ·
    refine ⟨22920207652670036955434209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30560276870226715940578945 22920207652670036955434209)
    ·
      refine ⟨17190155739502527716575657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22920207652670036955434209 17190155739502527716575657)
      ·
        refine ⟨12892616804626895787431743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17190155739502527716575657 12892616804626895787431743)
        ·
          refine ⟨19338925206940343681147615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892616804626895787431743 19338925206940343681147615)
          ·
            refine ⟨29008387810410515521721423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19338925206940343681147615 29008387810410515521721423)
            ·
              refine ⟨43512581715615773282582135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29008387810410515521721423 43512581715615773282582135)
              ·
                refine ⟨65268872573423659923873203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43512581715615773282582135 65268872573423659923873203)
                ·
                  refine ⟨97903308860135489885809805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65268872573423659923873203 97903308860135489885809805)
                  ·
                    refine ⟨36713740822550808707178677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97903308860135489885809805 36713740822550808707178677)
                    ·
                      refine ⟨3441913202114138316298001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36713740822550808707178677 3441913202114138316298001)
                      ·
                        rfl

theorem cell23_6703102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6703102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703102 prefixEnd_6703102 := by exact prefixLift 6703102
  have htrace : WordTrace (prefixWord ++ tailWord_6703102) baseStart_6703102 baseEnd_6703102 := by
    simpa [prefixWord, tailWord_6703102, baseEnd_6703102] using wordTrace_append hprefix tailTrace_6703102
  have hstable : (prefixWord ++ tailWord_6703102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703102).length < 2 ^ (prefixWord ++ tailWord_6703102).sum := by decide
  have hdescent : baseEnd_6703102 < baseStart_6703102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703133 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_6703133 : Nat := 118140960795 + 6703133 * 2 ^ 59
def prefixEnd_6703133 : Nat := 4983230072969 + 3 ^ 40 * 6703133 * 2
def baseEnd_6703133 : Nat := 3441929120014427695010359

theorem tailTrace_6703133 : CollatzResearch.WordTrace tailWord_6703133 prefixEnd_6703133 3441929120014427695010359 := by
  unfold tailWord_6703133
  simp only [CollatzResearch.WordTrace]
  refine ⟨244483345624701419819010053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162988897083134279879340035 244483345624701419819010053)
  ·
    refine ⟨45840627304631516216064385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244483345624701419819010053 45840627304631516216064385)
    ·
      refine ⟨34380470478473637162048289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45840627304631516216064385 34380470478473637162048289)
      ·
        refine ⟨25785352858855227871536217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34380470478473637162048289 25785352858855227871536217)
        ·
          refine ⟨19339014644141420903652163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25785352858855227871536217 19339014644141420903652163)
          ·
            refine ⟨29008521966212131355478245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19339014644141420903652163 29008521966212131355478245)
            ·
              refine ⟨5439097868664774629152171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29008521966212131355478245 5439097868664774629152171)
              ·
                refine ⟨8158646802997161943728257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439097868664774629152171 8158646802997161943728257)
                ·
                  refine ⟨6118985102247871457796193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158646802997161943728257 6118985102247871457796193)
                  ·
                    refine ⟨4589238826685903593347145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6118985102247871457796193 4589238826685903593347145)
                    ·
                      refine ⟨3441929120014427695010359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589238826685903593347145 3441929120014427695010359)
                      ·
                        rfl

theorem cell23_6703133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_6703133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703133 prefixEnd_6703133 := by exact prefixLift 6703133
  have htrace : WordTrace (prefixWord ++ tailWord_6703133) baseStart_6703133 baseEnd_6703133 := by
    simpa [prefixWord, tailWord_6703133, baseEnd_6703133] using wordTrace_append hprefix tailTrace_6703133
  have hstable : (prefixWord ++ tailWord_6703133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703133).length < 2 ^ (prefixWord ++ tailWord_6703133).sum := by decide
  have hdescent : baseEnd_6703133 < baseStart_6703133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703135 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 4, 5]
def baseStart_6703135 : Nat := 118140960795 + 6703135 * 2 ^ 59
def prefixEnd_6703135 : Nat := 4983230072969 + 3 ^ 40 * 6703135 * 2
def baseEnd_6703135 : Nat := 1147310048991912229061783

theorem tailTrace_6703135 : CollatzResearch.WordTrace tailWord_6703135 prefixEnd_6703135 1147310048991912229061783 := by
  unfold tailWord_6703135
  simp only [CollatzResearch.WordTrace]
  refine ⟨244483418570694174160582859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162988945713796116107055239 244483418570694174160582859)
  ·
    refine ⟨366725127856041261240874289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244483418570694174160582859 366725127856041261240874289)
    ·
      refine ⟨275043845892030945930655717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366725127856041261240874289 275043845892030945930655717)
      ·
        refine ⟨51570721104755802361997947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275043845892030945930655717 51570721104755802361997947)
        ·
          refine ⟨77356081657133703542996921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51570721104755802361997947 77356081657133703542996921)
          ·
            refine ⟨58017061242850277657247691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77356081657133703542996921 58017061242850277657247691)
            ·
              refine ⟨87025591864275416485871537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58017061242850277657247691 87025591864275416485871537)
              ·
                refine ⟨65269193898206562364403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87025591864275416485871537 65269193898206562364403653)
                ·
                  refine ⟨12237973855913730443325685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65269193898206562364403653 12237973855913730443325685)
                  ·
                    refine ⟨1147310048991912229061783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12237973855913730443325685 1147310048991912229061783)
                    ·
                      rfl

theorem cell23_6703135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_6703135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703135 prefixEnd_6703135 := by exact prefixLift 6703135
  have htrace : WordTrace (prefixWord ++ tailWord_6703135) baseStart_6703135 baseEnd_6703135 := by
    simpa [prefixWord, tailWord_6703135, baseEnd_6703135] using wordTrace_append hprefix tailTrace_6703135
  have hstable : (prefixWord ++ tailWord_6703135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703135).length < 2 ^ (prefixWord ++ tailWord_6703135).sum := by decide
  have hdescent : baseEnd_6703135 < baseStart_6703135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703152 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_6703152 : Nat := 118140960795 + 6703152 * 2 ^ 59
def prefixEnd_6703152 : Nat := 4983230072969 + 3 ^ 40 * 6703152 * 2
def baseEnd_6703152 : Nat := 1147312958715621040224257

theorem tailTrace_6703152 : CollatzResearch.WordTrace tailWord_6703152 prefixEnd_6703152 1147312958715621040224257 := by
  unfold tailWord_6703152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122242019305816293031975855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162989359074421724042634473 122242019305816293031975855)
  ·
    refine ⟨183363028958724439547963783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122242019305816293031975855 183363028958724439547963783)
    ·
      refine ⟨275044543438086659321945675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183363028958724439547963783 275044543438086659321945675)
      ·
        refine ⟨412566815157129988982918513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275044543438086659321945675 412566815157129988982918513)
        ·
          refine ⟨309425111367847491737188885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412566815157129988982918513 309425111367847491737188885)
          ·
            refine ⟨14504302095367851175180729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309425111367847491737188885 14504302095367851175180729)
            ·
              refine ⟨10878226571525888381385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504302095367851175180729 10878226571525888381385547)
              ·
                refine ⟨16317339857288832572078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10878226571525888381385547 16317339857288832572078321)
                ·
                  refine ⟨12238004892966624429058741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16317339857288832572078321 12238004892966624429058741)
                  ·
                    refine ⟨1147312958715621040224257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12238004892966624429058741 1147312958715621040224257)
                    ·
                      rfl

theorem cell23_6703152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_6703152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703152 prefixEnd_6703152 := by exact prefixLift 6703152
  have htrace : WordTrace (prefixWord ++ tailWord_6703152) baseStart_6703152 baseEnd_6703152 := by
    simpa [prefixWord, tailWord_6703152, baseEnd_6703152] using wordTrace_append hprefix tailTrace_6703152
  have hstable : (prefixWord ++ tailWord_6703152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703152).length < 2 ^ (prefixWord ++ tailWord_6703152).sum := by decide
  have hdescent : baseEnd_6703152 < baseStart_6703152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703155 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_6703155 : Nat := 118140960795 + 6703155 * 2 ^ 59
def prefixEnd_6703155 : Nat := 4983230072969 + 3 ^ 40 * 6703155 * 2
def baseEnd_6703155 : Nat := 3441940416588826608935257

theorem tailTrace_6703155 : CollatzResearch.WordTrace tailWord_6703155 prefixEnd_6703155 3441940416588826608935257 := by
  unfold tailWord_6703155
  simp only [CollatzResearch.WordTrace]
  refine ⟨244484148030621717576310919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162989432020414478384207279 244484148030621717576310919)
  ·
    refine ⟨366726222045932576364466379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244484148030621717576310919 366726222045932576364466379)
    ·
      refine ⟨550089333068898864546699569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366726222045932576364466379 550089333068898864546699569)
      ·
        refine ⟨412566999801674148410024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550089333068898864546699569 412566999801674148410024677)
        ·
          refine ⟨77356312462813902826879627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412566999801674148410024677 77356312462813902826879627)
          ·
            refine ⟨116034468694220854240319441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77356312462813902826879627 116034468694220854240319441)
            ·
              refine ⟨87025851520665640680239581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116034468694220854240319441 87025851520665640680239581)
              ·
                refine ⟨32634694320249615255089843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87025851520665640680239581 32634694320249615255089843)
                ·
                  refine ⟨48952041480374422882634765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32634694320249615255089843 48952041480374422882634765)
                  ·
                    refine ⟨18357015555140408580988037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48952041480374422882634765 18357015555140408580988037)
                    ·
                      refine ⟨3441940416588826608935257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18357015555140408580988037 3441940416588826608935257)
                      ·
                        rfl

theorem cell23_6703155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_6703155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703155 prefixEnd_6703155 := by exact prefixLift 6703155
  have htrace : WordTrace (prefixWord ++ tailWord_6703155) baseStart_6703155 baseEnd_6703155 := by
    simpa [prefixWord, tailWord_6703155, baseEnd_6703155] using wordTrace_append hprefix tailTrace_6703155
  have hstable : (prefixWord ++ tailWord_6703155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703155).length < 2 ^ (prefixWord ++ tailWord_6703155).sum := by decide
  have hdescent : baseEnd_6703155 < baseStart_6703155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703175 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_6703175 : Nat := 118140960795 + 6703175 * 2 ^ 59
def prefixEnd_6703175 : Nat := 4983230072969 + 3 ^ 40 * 6703175 * 2
def baseEnd_6703175 : Nat := 3441950686201916530685165

theorem tailTrace_6703175 : CollatzResearch.WordTrace tailWord_6703175 prefixEnd_6703175 3441950686201916530685165 := by
  unfold tailWord_6703175
  simp only [CollatzResearch.WordTrace]
  refine ⟨244484877490549260992038979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162989918327032840661359319 244484877490549260992038979)
  ·
    refine ⟨366727316235823891488058469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244484877490549260992038979 366727316235823891488058469)
    ·
      refine ⟨68761371794216979654010963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366727316235823891488058469 68761371794216979654010963)
      ·
        refine ⟨103142057691325469481016445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68761371794216979654010963 103142057691325469481016445)
        ·
          refine ⟨38678271634247051055381167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103142057691325469481016445 38678271634247051055381167)
          ·
            refine ⟨58017407451370576583071751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38678271634247051055381167 58017407451370576583071751)
            ·
              refine ⟨87026111177055864874607627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58017407451370576583071751 87026111177055864874607627)
              ·
                refine ⟨130539166765583797311911441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87026111177055864874607627 130539166765583797311911441)
                ·
                  refine ⟨97904375074187847983933581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130539166765583797311911441 97904375074187847983933581)
                  ·
                    refine ⟨36714140652820442993975093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97904375074187847983933581 36714140652820442993975093)
                    ·
                      refine ⟨3441950686201916530685165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36714140652820442993975093 3441950686201916530685165)
                      ·
                        rfl

theorem cell23_6703175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_6703175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703175 prefixEnd_6703175 := by exact prefixLift 6703175
  have htrace : WordTrace (prefixWord ++ tailWord_6703175) baseStart_6703175 baseEnd_6703175 := by
    simpa [prefixWord, tailWord_6703175, baseEnd_6703175] using wordTrace_append hprefix tailTrace_6703175
  have hstable : (prefixWord ++ tailWord_6703175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703175).length < 2 ^ (prefixWord ++ tailWord_6703175).sum := by decide
  have hdescent : baseEnd_6703175 < baseStart_6703175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703185 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_6703185 : Nat := 118140960795 + 6703185 * 2 ^ 59
def prefixEnd_6703185 : Nat := 4983230072969 + 3 ^ 40 * 6703185 * 2
def baseEnd_6703185 : Nat := 3441955821008461491560119

theorem tailTrace_6703185 : CollatzResearch.WordTrace tailWord_6703185 prefixEnd_6703185 3441955821008461491560119 := by
  unfold tailWord_6703185
  simp only [CollatzResearch.WordTrace]
  refine ⟨244485242220513032699903009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162990161480342021799935339 244485242220513032699903009)
  ·
    refine ⟨183363931665384774524927257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244485242220513032699903009 183363931665384774524927257)
    ·
      refine ⟨137522948749038580893695443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183363931665384774524927257 137522948749038580893695443)
      ·
        refine ⟨206284423123557871340543165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137522948749038580893695443 206284423123557871340543165)
        ·
          refine ⟨77356658671334201752703687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206284423123557871340543165 77356658671334201752703687)
          ·
            refine ⟨116034988007001302629055531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77356658671334201752703687 116034988007001302629055531)
            ·
              refine ⟨174052482010501953943583297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116034988007001302629055531 174052482010501953943583297)
              ·
                refine ⟨130539361507876465457687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174052482010501953943583297 130539361507876465457687473)
                ·
                  refine ⟨97904521130907349093265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130539361507876465457687473 97904521130907349093265605)
                  ·
                    refine ⟨18357097712045127954987301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97904521130907349093265605 18357097712045127954987301)
                    ·
                      refine ⟨3441955821008461491560119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18357097712045127954987301 3441955821008461491560119)
                      ·
                        rfl

theorem cell23_6703185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_6703185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703185 prefixEnd_6703185 := by exact prefixLift 6703185
  have htrace : WordTrace (prefixWord ++ tailWord_6703185) baseStart_6703185 baseEnd_6703185 := by
    simpa [prefixWord, tailWord_6703185, baseEnd_6703185] using wordTrace_append hprefix tailTrace_6703185
  have hstable : (prefixWord ++ tailWord_6703185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703185).length < 2 ^ (prefixWord ++ tailWord_6703185).sum := by decide
  have hdescent : baseEnd_6703185 < baseStart_6703185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703189 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6703189 : Nat := 118140960795 + 6703189 * 2 ^ 59
def prefixEnd_6703189 : Nat := 4983230072969 + 3 ^ 40 * 6703189 * 2
def baseEnd_6703189 : Nat := 3441957874931079475910101

theorem tailTrace_6703189 : CollatzResearch.WordTrace tailWord_6703189 prefixEnd_6703189 3441957874931079475910101 := by
  unfold tailWord_6703189
  simp only [CollatzResearch.WordTrace]
  refine ⟨244485388112498541383048621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162990258741665694255365747 244485388112498541383048621)
  ·
    refine ⟨91682020542186953018643233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244485388112498541383048621 91682020542186953018643233)
    ·
      refine ⟨68761515406640214763982425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91682020542186953018643233 68761515406640214763982425)
      ·
        refine ⟨51571136554980161072986819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68761515406640214763982425 51571136554980161072986819)
        ·
          refine ⟨77356704832470241609480229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51571136554980161072986819 77356704832470241609480229)
          ·
            refine ⟨14504382156088170301777543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77356704832470241609480229 14504382156088170301777543)
            ·
              refine ⟨21756573234132255452666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14504382156088170301777543 21756573234132255452666315)
              ·
                refine ⟨32634859851198383178999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21756573234132255452666315 32634859851198383178999473)
                ·
                  refine ⟨24476144888398787384249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32634859851198383178999473 24476144888398787384249605)
                  ·
                    refine ⟨4589277166574772634546801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24476144888398787384249605 4589277166574772634546801)
                    ·
                      refine ⟨3441957874931079475910101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589277166574772634546801 3441957874931079475910101)
                      ·
                        rfl

theorem cell23_6703189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6703189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703189 prefixEnd_6703189 := by exact prefixLift 6703189
  have htrace : WordTrace (prefixWord ++ tailWord_6703189) baseStart_6703189 baseEnd_6703189 := by
    simpa [prefixWord, tailWord_6703189, baseEnd_6703189] using wordTrace_append hprefix tailTrace_6703189
  have hstable : (prefixWord ++ tailWord_6703189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703189).length < 2 ^ (prefixWord ++ tailWord_6703189).sum := by decide
  have hdescent : baseEnd_6703189 < baseStart_6703189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703216 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 1, 4]
def baseStart_6703216 : Nat := 118140960795 + 6703216 * 2 ^ 59
def prefixEnd_6703216 : Nat := 4983230072969 + 3 ^ 40 * 6703216 * 2
def baseEnd_6703216 : Nat := 1147323912969583623424159

theorem tailTrace_6703216 : CollatzResearch.WordTrace tailWord_6703216 prefixEnd_6703216 1147323912969583623424159 := by
  unfold tailWord_6703216
  simp only [CollatzResearch.WordTrace]
  refine ⟨122243186441700362497140751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162990915255600483329521001 122243186441700362497140751)
  ·
    refine ⟨183364779662550543745711127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122243186441700362497140751 183364779662550543745711127)
    ·
      refine ⟨275047169493825815618566691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183364779662550543745711127 275047169493825815618566691)
      ·
        refine ⟨412570754240738723427850037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275047169493825815618566691 412570754240738723427850037)
        ·
          refine ⟨38678508210069255321360941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412570754240738723427850037 38678508210069255321360941)
          ·
            refine ⟨14504440578775970745510353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38678508210069255321360941 14504440578775970745510353)
            ·
              refine ⟨10878330434081978059132765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504440578775970745510353 10878330434081978059132765)
              ·
                refine ⟨4079373912780741772174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10878330434081978059132765 4079373912780741772174787)
                ·
                  refine ⟨6119060869171112658262181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079373912780741772174787 6119060869171112658262181)
                  ·
                    refine ⟨1147323912969583623424159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119060869171112658262181 1147323912969583623424159)
                    ·
                      rfl

theorem cell23_6703216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_6703216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703216 prefixEnd_6703216 := by exact prefixLift 6703216
  have htrace : WordTrace (prefixWord ++ tailWord_6703216) baseStart_6703216 baseEnd_6703216 := by
    simpa [prefixWord, tailWord_6703216, baseEnd_6703216] using wordTrace_append hprefix tailTrace_6703216
  have hstable : (prefixWord ++ tailWord_6703216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703216).length < 2 ^ (prefixWord ++ tailWord_6703216).sum := by decide
  have hdescent : baseEnd_6703216 < baseStart_6703216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703229 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 6]
def baseStart_6703229 : Nat := 118140960795 + 6703229 * 2 ^ 59
def prefixEnd_6703229 : Nat := 4983230072969 + 3 ^ 40 * 6703229 * 2
def baseEnd_6703229 : Nat := 382442046017473257712213

theorem tailTrace_6703229 : CollatzResearch.WordTrace tailWord_6703229 prefixEnd_6703229 382442046017473257712213 := by
  unfold tailWord_6703229
  simp only [CollatzResearch.WordTrace]
  refine ⟨244486847032353628214504741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162991231354902418809669827 244486847032353628214504741)
  ·
    refine ⟨45841283818566305290219639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244486847032353628214504741 45841283818566305290219639)
    ·
      refine ⟨68761925727849457935329459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45841283818566305290219639 68761925727849457935329459)
      ·
        refine ⟨103142888591774186902994189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68761925727849457935329459 103142888591774186902994189)
        ·
          refine ⟨38678583221915320088622821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103142888591774186902994189 38678583221915320088622821)
          ·
            refine ⟨7252234354109122516616779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38678583221915320088622821 7252234354109122516616779)
            ·
              refine ⟨10878351531163683774925169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252234354109122516616779 10878351531163683774925169)
              ·
                refine ⟨8158763648372762831193877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878351531163683774925169 8158763648372762831193877)
                ·
                  refine ⟨382442046017473257712213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8158763648372762831193877 382442046017473257712213)
                  ·
                    rfl

theorem cell23_6703229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_6703229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703229 prefixEnd_6703229 := by exact prefixLift 6703229
  have htrace : WordTrace (prefixWord ++ tailWord_6703229) baseStart_6703229 baseEnd_6703229 := by
    simpa [prefixWord, tailWord_6703229, baseEnd_6703229] using wordTrace_append hprefix tailTrace_6703229
  have hstable : (prefixWord ++ tailWord_6703229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703229).length < 2 ^ (prefixWord ++ tailWord_6703229).sum := by decide
  have hdescent : baseEnd_6703229 < baseStart_6703229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703239 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_6703239 : Nat := 118140960795 + 6703239 * 2 ^ 59
def prefixEnd_6703239 : Nat := 4983230072969 + 3 ^ 40 * 6703239 * 2
def baseEnd_6703239 : Nat := 3441983548963804280284871

theorem tailTrace_6703239 : CollatzResearch.WordTrace tailWord_6703239 prefixEnd_6703239 3441983548963804280284871 := by
  unfold tailWord_6703239
  simp only [CollatzResearch.WordTrace]
  refine ⟨244487211762317399922368771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162991474508211599948245847 244487211762317399922368771)
  ·
    refine ⟨366730817643476099883553157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244487211762317399922368771 366730817643476099883553157)
    ·
      refine ⟨68762028308151768728166217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366730817643476099883553157 68762028308151768728166217)
      ·
        refine ⟨51571521231113826546124663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68762028308151768728166217 51571521231113826546124663)
        ·
          refine ⟨77357281846670739819186995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51571521231113826546124663 77357281846670739819186995)
          ·
            refine ⟨116035922770006109728780493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77357281846670739819186995 116035922770006109728780493)
            ·
              refine ⟨43513471038752291148292685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116035922770006109728780493 43513471038752291148292685)
              ·
                refine ⟨16317551639532109180609757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43513471038752291148292685 16317551639532109180609757)
                ·
                  refine ⟨6119081864824540942728659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16317551639532109180609757 6119081864824540942728659)
                  ·
                    refine ⟨9178622797236811414092989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6119081864824540942728659 9178622797236811414092989)
                    ·
                      refine ⟨3441983548963804280284871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9178622797236811414092989 3441983548963804280284871)
                      ·
                        rfl

theorem cell23_6703239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_6703239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703239 prefixEnd_6703239 := by exact prefixLift 6703239
  have htrace : WordTrace (prefixWord ++ tailWord_6703239) baseStart_6703239 baseEnd_6703239 := by
    simpa [prefixWord, tailWord_6703239, baseEnd_6703239] using wordTrace_append hprefix tailTrace_6703239
  have hstable : (prefixWord ++ tailWord_6703239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703239).length < 2 ^ (prefixWord ++ tailWord_6703239).sum := by decide
  have hdescent : baseEnd_6703239 < baseStart_6703239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703246 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_6703246 : Nat := 118140960795 + 6703246 * 2 ^ 59
def prefixEnd_6703246 : Nat := 4983230072969 + 3 ^ 40 * 6703246 * 2
def baseEnd_6703246 : Nat := 382443015925376194766371

theorem tailTrace_6703246 : CollatzResearch.WordTrace tailWord_6703246 prefixEnd_6703246 382443015925376194766371 := by
  unfold tailWord_6703246
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560933384161505014734199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162991644715528026745249061 30560933384161505014734199)
  ·
    refine ⟨45841400076242257522101299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30560933384161505014734199 45841400076242257522101299)
    ·
      refine ⟨68762100114363386283151949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45841400076242257522101299 68762100114363386283151949)
      ·
        refine ⟨25785787542886269856181981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68762100114363386283151949 25785787542886269856181981)
        ·
          refine ⟨9669670328582351196068243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25785787542886269856181981 9669670328582351196068243)
          ·
            refine ⟨14504505492873526794102365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669670328582351196068243 14504505492873526794102365)
            ·
              refine ⟨5439189559827572547788387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504505492873526794102365 5439189559827572547788387)
              ·
                refine ⟨8158784339741358821682581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439189559827572547788387 8158784339741358821682581)
                ·
                  refine ⟨382443015925376194766371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8158784339741358821682581 382443015925376194766371)
                  ·
                    rfl

theorem cell23_6703246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_6703246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703246 prefixEnd_6703246 := by exact prefixLift 6703246
  have htrace : WordTrace (prefixWord ++ tailWord_6703246) baseStart_6703246 baseEnd_6703246 := by
    simpa [prefixWord, tailWord_6703246, baseEnd_6703246] using wordTrace_append hprefix tailTrace_6703246
  have hstable : (prefixWord ++ tailWord_6703246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703246).length < 2 ^ (prefixWord ++ tailWord_6703246).sum := by decide
  have hdescent : baseEnd_6703246 < baseStart_6703246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703266 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6703266 : Nat := 118140960795 + 6703266 * 2 ^ 59
def prefixEnd_6703266 : Nat := 4983230072969 + 3 ^ 40 * 6703266 * 2
def baseEnd_6703266 : Nat := 3441997412941475674647247

theorem tailTrace_6703266 : CollatzResearch.WordTrace tailWord_6703266 prefixEnd_6703266 3441997412941475674647247 := by
  unfold tailWord_6703266
  simp only [CollatzResearch.WordTrace]
  refine ⟨61122049133304895883400413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162992131022146389022401101 61122049133304895883400413)
  ·
    refine ⟨22920768424989335956275155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61122049133304895883400413 22920768424989335956275155)
    ·
      refine ⟨34381152637484003934412733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22920768424989335956275155 34381152637484003934412733)
      ·
        refine ⟨12892932239056501475404775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34381152637484003934412733 12892932239056501475404775)
        ·
          refine ⟨19339398358584752213107163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892932239056501475404775 19339398358584752213107163)
          ·
            refine ⟨29009097537877128319660745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19339398358584752213107163 29009097537877128319660745)
            ·
              refine ⟨21756823153407846239745559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29009097537877128319660745 21756823153407846239745559)
              ·
                refine ⟨32635234730111769359618339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21756823153407846239745559 32635234730111769359618339)
                ·
                  refine ⟨48952852095167654039427509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32635234730111769359618339 48952852095167654039427509)
                  ·
                    refine ⟨4589329883921967566196329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48952852095167654039427509 4589329883921967566196329)
                    ·
                      refine ⟨3441997412941475674647247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589329883921967566196329 3441997412941475674647247)
                      ·
                        rfl

theorem cell23_6703266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6703266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703266 prefixEnd_6703266 := by exact prefixLift 6703266
  have htrace : WordTrace (prefixWord ++ tailWord_6703266) baseStart_6703266 baseEnd_6703266 := by
    simpa [prefixWord, tailWord_6703266, baseEnd_6703266] using wordTrace_append hprefix tailTrace_6703266
  have hstable : (prefixWord ++ tailWord_6703266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703266).length < 2 ^ (prefixWord ++ tailWord_6703266).sum := by decide
  have hdescent : baseEnd_6703266 < baseStart_6703266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703284 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6703284 : Nat := 118140960795 + 6703284 * 2 ^ 59
def prefixEnd_6703284 : Nat := 4983230072969 + 3 ^ 40 * 6703284 * 2
def baseEnd_6703284 : Nat := 1147335551864418868074055

theorem tailTrace_6703284 : CollatzResearch.WordTrace tailWord_6703284 prefixEnd_6703284 1147335551864418868074055 := by
  unfold tailWord_6703284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122244426523577186303878453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162992568698102915071837937 122244426523577186303878453)
  ·
    refine ⟨11460414986585361215988605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122244426523577186303878453 11460414986585361215988605)
    ·
      refine ⟨4297655619969510455995727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11460414986585361215988605 4297655619969510455995727)
      ·
        refine ⟨6446483429954265683993591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297655619969510455995727 6446483429954265683993591)
        ·
          refine ⟨9669725144931398525990387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446483429954265683993591 9669725144931398525990387)
          ·
            refine ⟨14504587717397097788985581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669725144931398525990387 14504587717397097788985581)
            ·
              refine ⟨5439220394023911670869593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504587717397097788985581 5439220394023911670869593)
              ·
                refine ⟨4079415295517933753152195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439220394023911670869593 4079415295517933753152195)
                ·
                  refine ⟨6119122943276900629728293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079415295517933753152195 6119122943276900629728293)
                  ·
                    refine ⟨1147335551864418868074055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119122943276900629728293 1147335551864418868074055)
                    ·
                      rfl

theorem cell23_6703284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6703284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703284 prefixEnd_6703284 := by exact prefixLift 6703284
  have htrace : WordTrace (prefixWord ++ tailWord_6703284) baseStart_6703284 baseEnd_6703284 := by
    simpa [prefixWord, tailWord_6703284, baseEnd_6703284] using wordTrace_append hprefix tailTrace_6703284
  have hstable : (prefixWord ++ tailWord_6703284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703284).length < 2 ^ (prefixWord ++ tailWord_6703284).sum := by decide
  have hdescent : baseEnd_6703284 < baseStart_6703284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703289 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_6703289 : Nat := 118140960795 + 6703289 * 2 ^ 59
def prefixEnd_6703289 : Nat := 4983230072969 + 3 ^ 40 * 6703289 * 2
def baseEnd_6703289 : Nat := 1147336407665509694886547

theorem tailTrace_6703289 : CollatzResearch.WordTrace tailWord_6703289 prefixEnd_6703289 1147336407665509694886547 := by
  unfold tailWord_6703289
  simp only [CollatzResearch.WordTrace]
  refine ⟨244489035412136258461688921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162992690274757505641125947 244489035412136258461688921)
  ·
    refine ⟨183366776559102193846266691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244489035412136258461688921 183366776559102193846266691)
    ·
      refine ⟨275050164838653290769400037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183366776559102193846266691 275050164838653290769400037)
      ·
        refine ⟨51571905907247492019262507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275050164838653290769400037 51571905907247492019262507)
        ·
          refine ⟨77357858860871238028893761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51571905907247492019262507 77357858860871238028893761)
          ·
            refine ⟨58018394145653428521670321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77357858860871238028893761 58018394145653428521670321)
            ·
              refine ⟨43513795609240071391252741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58018394145653428521670321 43513795609240071391252741)
              ·
                refine ⟨8158836676732513385859889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43513795609240071391252741 8158836676732513385859889)
                ·
                  refine ⟨6119127507549385039394917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158836676732513385859889 6119127507549385039394917)
                  ·
                    refine ⟨1147336407665509694886547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119127507549385039394917 1147336407665509694886547)
                    ·
                      rfl

theorem cell23_6703289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_6703289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703289 prefixEnd_6703289 := by exact prefixLift 6703289
  have htrace : WordTrace (prefixWord ++ tailWord_6703289) baseStart_6703289 baseEnd_6703289 := by
    simpa [prefixWord, tailWord_6703289, baseEnd_6703289] using wordTrace_append hprefix tailTrace_6703289
  have hstable : (prefixWord ++ tailWord_6703289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703289).length < 2 ^ (prefixWord ++ tailWord_6703289).sum := by decide
  have hdescent : baseEnd_6703289 < baseStart_6703289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703312 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_6703312 : Nat := 118140960795 + 6703312 * 2 ^ 59
def prefixEnd_6703312 : Nat := 4983230072969 + 3 ^ 40 * 6703312 * 2
def baseEnd_6703312 : Nat := 3442021033051582494672035

theorem tailTrace_6703312 : CollatzResearch.WordTrace tailWord_6703312 prefixEnd_6703312 3442021033051582494672035 := by
  unfold tailWord_6703312
  simp only [CollatzResearch.WordTrace]
  refine ⟨122244937145526466694888095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162993249527368622259850793 122244937145526466694888095)
  ·
    refine ⟨183367405718289700042332143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122244937145526466694888095 183367405718289700042332143)
    ·
      refine ⟨275051108577434550063498215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183367405718289700042332143 275051108577434550063498215)
      ·
        refine ⟨412576662866151825095247323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275051108577434550063498215 412576662866151825095247323)
        ·
          refine ⟨618864994299227737642870985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412576662866151825095247323 618864994299227737642870985)
          ·
            refine ⟨464148745724420803232153239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618864994299227737642870985 464148745724420803232153239)
            ·
              refine ⟨696223118586631204848229859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464148745724420803232153239 696223118586631204848229859)
              ·
                refine ⟨1044334677879946807272344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696223118586631204848229859 1044334677879946807272344789)
                ·
                  refine ⟨24476594012811253295445581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1044334677879946807272344789 24476594012811253295445581)
                  ·
                    refine ⟨9178722754804219985792093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24476594012811253295445581 9178722754804219985792093)
                    ·
                      refine ⟨3442021033051582494672035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9178722754804219985792093 3442021033051582494672035)
                      ·
                        rfl

theorem cell23_6703312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_6703312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703312 prefixEnd_6703312 := by exact prefixLift 6703312
  have htrace : WordTrace (prefixWord ++ tailWord_6703312) baseStart_6703312 baseEnd_6703312 := by
    simpa [prefixWord, tailWord_6703312, baseEnd_6703312] using wordTrace_append hprefix tailTrace_6703312
  have hstable : (prefixWord ++ tailWord_6703312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703312).length < 2 ^ (prefixWord ++ tailWord_6703312).sum := by decide
  have hdescent : baseEnd_6703312 < baseStart_6703312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703329 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_6703329 : Nat := 118140960795 + 6703329 * 2 ^ 59
def prefixEnd_6703329 : Nat := 4983230072969 + 3 ^ 40 * 6703329 * 2
def baseEnd_6703329 : Nat := 3442029762222708928159457

theorem tailTrace_6703329 : CollatzResearch.WordTrace tailWord_6703329 prefixEnd_6703329 3442029762222708928159457 := by
  unfold tailWord_6703329
  simp only [CollatzResearch.WordTrace]
  refine ⟨244490494331991345293145041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162993662887994230195430027 244490494331991345293145041)
  ·
    refine ⟨183367870748993508969858781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244490494331991345293145041 183367870748993508969858781)
    ·
      refine ⟨68762951530872565863697043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183367870748993508969858781 68762951530872565863697043)
      ·
        refine ⟨103144427296308848795545565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68762951530872565863697043 103144427296308848795545565)
        ·
          refine ⟨38679160236115818298329587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103144427296308848795545565 38679160236115818298329587)
          ·
            refine ⟨58018740354173727447494381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38679160236115818298329587 58018740354173727447494381)
            ·
              refine ⟨21757027632815147792810393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58018740354173727447494381 21757027632815147792810393)
              ·
                refine ⟨16317770724611360844607795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21757027632815147792810393 16317770724611360844607795)
                ·
                  refine ⟨24476656086917041266911693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16317770724611360844607795 24476656086917041266911693)
                  ·
                    refine ⟨9178746032593890475091885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24476656086917041266911693 9178746032593890475091885)
                    ·
                      refine ⟨3442029762222708928159457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9178746032593890475091885 3442029762222708928159457)
                      ·
                        rfl

theorem cell23_6703329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_6703329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703329 prefixEnd_6703329 := by exact prefixLift 6703329
  have htrace : WordTrace (prefixWord ++ tailWord_6703329) baseStart_6703329 baseEnd_6703329 := by
    simpa [prefixWord, tailWord_6703329, baseEnd_6703329] using wordTrace_append hprefix tailTrace_6703329
  have hstable : (prefixWord ++ tailWord_6703329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703329).length < 2 ^ (prefixWord ++ tailWord_6703329).sum := by decide
  have hdescent : baseEnd_6703329 < baseStart_6703329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703333 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6703333 : Nat := 118140960795 + 6703333 * 2 ^ 59
def prefixEnd_6703333 : Nat := 4983230072969 + 3 ^ 40 * 6703333 * 2
def baseEnd_6703333 : Nat := 3442031816145326912509439

theorem tailTrace_6703333 : CollatzResearch.WordTrace tailWord_6703333 prefixEnd_6703333 3442031816145326912509439 := by
  unfold tailWord_6703333
  simp only [CollatzResearch.WordTrace]
  refine ⟨244490640223976853976290653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162993760149317902650860435 244490640223976853976290653)
  ·
    refine ⟨91683990083991320241108995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244490640223976853976290653 91683990083991320241108995)
    ·
      refine ⟨137525985125986980361663493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91683990083991320241108995 137525985125986980361663493)
      ·
        refine ⟨25786122211122558817811905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137525985125986980361663493 25786122211122558817811905)
        ·
          refine ⟨19339591658341919113358929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25786122211122558817811905 19339591658341919113358929)
          ·
            refine ⟨14504693743756439335019197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339591658341919113358929 14504693743756439335019197)
            ·
              refine ⟨5439260153908664750632199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504693743756439335019197 5439260153908664750632199)
              ·
                refine ⟨8158890230862997125948299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439260153908664750632199 8158890230862997125948299)
                ·
                  refine ⟨12238335346294495688922449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8158890230862997125948299 12238335346294495688922449)
                  ·
                    refine ⟨9178751509720871766691837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12238335346294495688922449 9178751509720871766691837)
                    ·
                      refine ⟨3442031816145326912509439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9178751509720871766691837 3442031816145326912509439)
                      ·
                        rfl

theorem cell23_6703333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6703333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703333 prefixEnd_6703333 := by exact prefixLift 6703333
  have htrace : WordTrace (prefixWord ++ tailWord_6703333) baseStart_6703333 baseEnd_6703333 := by
    simpa [prefixWord, tailWord_6703333, baseEnd_6703333] using wordTrace_append hprefix tailTrace_6703333
  have hstable : (prefixWord ++ tailWord_6703333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703333).length < 2 ^ (prefixWord ++ tailWord_6703333).sum := by decide
  have hdescent : baseEnd_6703333 < baseStart_6703333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703356 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_6703356 : Nat := 118140960795 + 6703356 * 2 ^ 59
def prefixEnd_6703356 : Nat := 4983230072969 + 3 ^ 40 * 6703356 * 2
def baseEnd_6703356 : Nat := 3442043626200380322521833

theorem tailTrace_6703356 : CollatzResearch.WordTrace tailWord_6703356 prefixEnd_6703356 3442043626200380322521833 := by
  unfold tailWord_6703356
  simp only [CollatzResearch.WordTrace]
  refine ⟨122245739551446764452188961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162994319401929019269585281 122245739551446764452188961)
  ·
    refine ⟨91684304663585073339141721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122245739551446764452188961 91684304663585073339141721)
    ·
      refine ⟨68763228497688805004356291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91684304663585073339141721 68763228497688805004356291)
      ·
        refine ⟨103144842746533207506534437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68763228497688805004356291 103144842746533207506534437)
        ·
          refine ⟨19339658014974976407475207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103144842746533207506534437 19339658014974976407475207)
          ·
            refine ⟨29009487022462464611212811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19339658014974976407475207 29009487022462464611212811)
            ·
              refine ⟨43514230533693696916819217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29009487022462464611212811 43514230533693696916819217)
              ·
                refine ⟨32635672900270272687614413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43514230533693696916819217 32635672900270272687614413)
                ·
                  refine ⟨12238377337601352257855405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32635672900270272687614413 12238377337601352257855405)
                  ·
                    refine ⟨4589391501600507096695777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12238377337601352257855405 4589391501600507096695777)
                    ·
                      refine ⟨3442043626200380322521833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589391501600507096695777 3442043626200380322521833)
                      ·
                        rfl

theorem cell23_6703356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_6703356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703356 prefixEnd_6703356 := by exact prefixLift 6703356
  have htrace : WordTrace (prefixWord ++ tailWord_6703356) baseStart_6703356 baseEnd_6703356 := by
    simpa [prefixWord, tailWord_6703356, baseEnd_6703356] using wordTrace_append hprefix tailTrace_6703356
  have hstable : (prefixWord ++ tailWord_6703356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703356).length < 2 ^ (prefixWord ++ tailWord_6703356).sum := by decide
  have hdescent : baseEnd_6703356 < baseStart_6703356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703420 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_6703420 : Nat := 118140960795 + 6703420 * 2 ^ 59
def prefixEnd_6703420 : Nat := 4983230072969 + 3 ^ 40 * 6703420 * 2
def baseEnd_6703420 : Nat := 3442076488962268072121539

theorem tailTrace_6703420 : CollatzResearch.WordTrace tailWord_6703420 prefixEnd_6703420 3442076488962268072121539 := by
  unfold tailWord_6703420
  simp only [CollatzResearch.WordTrace]
  refine ⟨122246906687330833917353857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162995875583107778556471809 122246906687330833917353857)
  ·
    refine ⟨91685180015498125438015393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122246906687330833917353857 91685180015498125438015393)
    ·
      refine ⟨68763885011623594078511545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91685180015498125438015393 68763885011623594078511545)
      ·
        refine ⟨51572913758717695558883659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68763885011623594078511545 51572913758717695558883659)
        ·
          refine ⟨77359370638076543338325489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51572913758717695558883659 77359370638076543338325489)
          ·
            refine ⟨58019527978557407503744117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77359370638076543338325489 58019527978557407503744117)
            ·
              refine ⟨5439330747989756953476011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58019527978557407503744117 5439330747989756953476011)
              ·
                refine ⟨8158996121984635430214017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439330747989756953476011 8158996121984635430214017)
                ·
                  refine ⟨6119247091488476572660513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158996121984635430214017 6119247091488476572660513)
                  ·
                    refine ⟨4589435318616357429495385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119247091488476572660513 4589435318616357429495385)
                    ·
                      refine ⟨3442076488962268072121539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589435318616357429495385 3442076488962268072121539)
                      ·
                        rfl

theorem cell23_6703420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_6703420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703420 prefixEnd_6703420 := by exact prefixLift 6703420
  have htrace : WordTrace (prefixWord ++ tailWord_6703420) baseStart_6703420 baseEnd_6703420 := by
    simpa [prefixWord, tailWord_6703420, baseEnd_6703420] using wordTrace_append hprefix tailTrace_6703420
  have hstable : (prefixWord ++ tailWord_6703420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703420).length < 2 ^ (prefixWord ++ tailWord_6703420).sum := by decide
  have hdescent : baseEnd_6703420 < baseStart_6703420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703456 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_6703456 : Nat := 118140960795 + 6703456 * 2 ^ 59
def prefixEnd_6703456 : Nat := 4983230072969 + 3 ^ 40 * 6703456 * 2
def baseEnd_6703456 : Nat := 1147364991421943310423791

theorem tailTrace_6703456 : CollatzResearch.WordTrace tailWord_6703456 prefixEnd_6703456 1147364991421943310423791 := by
  unfold tailWord_6703456
  simp only [CollatzResearch.WordTrace]
  refine ⟨122247563201265622991509111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162996750935020830655345481 122247563201265622991509111)
  ·
    refine ⟨183371344801898434487263667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122247563201265622991509111 183371344801898434487263667)
    ·
      refine ⟨275057017202847651730895501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183371344801898434487263667 275057017202847651730895501)
      ·
        refine ⟨103146381451067869399085813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275057017202847651730895501 103146381451067869399085813)
        ·
          refine ⟨9669973261037612756164295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103146381451067869399085813 9669973261037612756164295)
          ·
            refine ⟨14504959891556419134246443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669973261037612756164295 14504959891556419134246443)
            ·
              refine ⟨21757439837334628701369665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14504959891556419134246443 21757439837334628701369665)
              ·
                refine ⟨16318079878000971526027249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21757439837334628701369665 16318079878000971526027249)
                ·
                  refine ⟨12238559908500728644520437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16318079878000971526027249 12238559908500728644520437)
                  ·
                    refine ⟨1147364991421943310423791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12238559908500728644520437 1147364991421943310423791)
                    ·
                      rfl

theorem cell23_6703456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_6703456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703456 prefixEnd_6703456 := by exact prefixLift 6703456
  have htrace : WordTrace (prefixWord ++ tailWord_6703456) baseStart_6703456 baseEnd_6703456 := by
    simpa [prefixWord, tailWord_6703456, baseEnd_6703456] using wordTrace_append hprefix tailTrace_6703456
  have hstable : (prefixWord ++ tailWord_6703456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703456).length < 2 ^ (prefixWord ++ tailWord_6703456).sum := by decide
  have hdescent : baseEnd_6703456 < baseStart_6703456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703466 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6703466 : Nat := 118140960795 + 6703466 * 2 ^ 59
def prefixEnd_6703466 : Nat := 4983230072969 + 3 ^ 40 * 6703466 * 2
def baseEnd_6703466 : Nat := 3442100109072374892146327

theorem tailTrace_6703466 : CollatzResearch.WordTrace tailWord_6703466 prefixEnd_6703466 3442100109072374892146327 := by
  unfold tailWord_6703466
  simp only [CollatzResearch.WordTrace]
  refine ⟨61123872783123754422720563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162996994088330011793921501 61123872783123754422720563)
  ·
    refine ⟨91685809174685631634080845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61123872783123754422720563 91685809174685631634080845)
    ·
      refine ⟨34382178440507111862780317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91685809174685631634080845 34382178440507111862780317)
      ·
        refine ⟨12893316915190166948542619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34382178440507111862780317 12893316915190166948542619)
        ·
          refine ⟨19339975372785250422813929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893316915190166948542619 19339975372785250422813929)
          ·
            refine ⟨14504981529588937817110447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339975372785250422813929 14504981529588937817110447)
            ·
              refine ⟨21757472294383406725665671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14504981529588937817110447 21757472294383406725665671)
              ·
                refine ⟨32636208441575110088498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21757472294383406725665671 32636208441575110088498507)
                ·
                  refine ⟨48954312662362665132747761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32636208441575110088498507 48954312662362665132747761)
                  ·
                    refine ⟨36715734496771998849560821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48954312662362665132747761 36715734496771998849560821)
                    ·
                      refine ⟨3442100109072374892146327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36715734496771998849560821 3442100109072374892146327)
                      ·
                        rfl

theorem cell23_6703466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6703466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703466 prefixEnd_6703466 := by exact prefixLift 6703466
  have htrace : WordTrace (prefixWord ++ tailWord_6703466) baseStart_6703466 baseEnd_6703466 := by
    simpa [prefixWord, tailWord_6703466, baseEnd_6703466] using wordTrace_append hprefix tailTrace_6703466
  have hstable : (prefixWord ++ tailWord_6703466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703466).length < 2 ^ (prefixWord ++ tailWord_6703466).sum := by decide
  have hdescent : baseEnd_6703466 < baseStart_6703466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703479 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_6703479 : Nat := 118140960795 + 6703479 * 2 ^ 59
def prefixEnd_6703479 : Nat := 4983230072969 + 3 ^ 40 * 6703479 * 2
def baseEnd_6703479 : Nat := 3442106784320883341283767

theorem tailTrace_6703479 : CollatzResearch.WordTrace tailWord_6703479 prefixEnd_6703479 3442106784320883341283767 := by
  unfold tailWord_6703479
  simp only [CollatzResearch.WordTrace]
  refine ⟨244495965281447920911105491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162997310187631947274070327 244495965281447920911105491)
  ·
    refine ⟨366743947922171881366658237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244495965281447920911105491 366743947922171881366658237)
    ·
      refine ⟨137528980470814455512496839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366743947922171881366658237 137528980470814455512496839)
      ·
        refine ⟨206293470706221683268745259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137528980470814455512496839 206293470706221683268745259)
        ·
          refine ⟨309440206059332524903117889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206293470706221683268745259 309440206059332524903117889)
          ·
            refine ⟨232080154544499393677338417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309440206059332524903117889 232080154544499393677338417)
            ·
              refine ⟨174060115908374545258003813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232080154544499393677338417 174060115908374545258003813)
              ·
                refine ⟨32636271732820227235875715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174060115908374545258003813 32636271732820227235875715)
                ·
                  refine ⟨48954407599230340853813573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32636271732820227235875715 48954407599230340853813573)
                  ·
                    refine ⟨9178951424855688910090045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48954407599230340853813573 9178951424855688910090045)
                    ·
                      refine ⟨3442106784320883341283767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9178951424855688910090045 3442106784320883341283767)
                      ·
                        rfl

theorem cell23_6703479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_6703479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703479 prefixEnd_6703479 := by exact prefixLift 6703479
  have htrace : WordTrace (prefixWord ++ tailWord_6703479) baseStart_6703479 baseEnd_6703479 := by
    simpa [prefixWord, tailWord_6703479, baseEnd_6703479] using wordTrace_append hprefix tailTrace_6703479
  have hstable : (prefixWord ++ tailWord_6703479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703479).length < 2 ^ (prefixWord ++ tailWord_6703479).sum := by decide
  have hdescent : baseEnd_6703479 < baseStart_6703479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703490 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6703490 : Nat := 118140960795 + 6703490 * 2 ^ 59
def prefixEnd_6703490 : Nat := 4983230072969 + 3 ^ 40 * 6703490 * 2
def baseEnd_6703490 : Nat := 1147370810869360932748739

theorem tailTrace_6703490 : CollatzResearch.WordTrace tailWord_6703490 prefixEnd_6703490 1147370810869360932748739 := by
  unfold tailWord_6703490
  simp only [CollatzResearch.WordTrace]
  refine ⟨61124091621102017447438981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162997577656272046526503949 61124091621102017447438981)
  ·
    refine ⟨11460767178956628271394809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61124091621102017447438981 11460767178956628271394809)
    ·
      refine ⟨8595575384217471203546107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11460767178956628271394809 8595575384217471203546107)
      ·
        refine ⟨12893363076326206805319161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595575384217471203546107 12893363076326206805319161)
        ·
          refine ⟨9670022307244655103989371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12893363076326206805319161 9670022307244655103989371)
          ·
            refine ⟨14505033460866982655984057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670022307244655103989371 14505033460866982655984057)
            ·
              refine ⟨10878775095650236991988043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14505033460866982655984057 10878775095650236991988043)
              ·
                refine ⟨16318162643475355487982065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10878775095650236991988043 16318162643475355487982065)
                ·
                  refine ⟨12238621982606516615986549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16318162643475355487982065 12238621982606516615986549)
                  ·
                    refine ⟨1147370810869360932748739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12238621982606516615986549 1147370810869360932748739)
                    ·
                      rfl

theorem cell23_6703490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6703490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703490 prefixEnd_6703490 := by exact prefixLift 6703490
  have htrace : WordTrace (prefixWord ++ tailWord_6703490) baseStart_6703490 baseEnd_6703490 := by
    simpa [prefixWord, tailWord_6703490, baseEnd_6703490] using wordTrace_append hprefix tailTrace_6703490
  have hstable : (prefixWord ++ tailWord_6703490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703490).length < 2 ^ (prefixWord ++ tailWord_6703490).sum := by decide
  have hdescent : baseEnd_6703490 < baseStart_6703490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703519 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6703519 : Nat := 118140960795 + 6703519 * 2 ^ 59
def prefixEnd_6703519 : Nat := 4983230072969 + 3 ^ 40 * 6703519 * 2
def baseEnd_6703519 : Nat := 3442127323547063184783583

theorem tailTrace_6703519 : CollatzResearch.WordTrace tailWord_6703519 prefixEnd_6703519 3442127323547063184783583 := by
  unfold tailWord_6703519
  simp only [CollatzResearch.WordTrace]
  refine ⟨244497424201303007742561611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162998282800868671828374407 244497424201303007742561611)
  ·
    refine ⟨366746136301954511613842417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244497424201303007742561611 366746136301954511613842417)
    ·
      refine ⟨275059602226465883710381813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366746136301954511613842417 275059602226465883710381813)
      ·
        refine ⟨25786837708731176597848295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275059602226465883710381813 25786837708731176597848295)
        ·
          refine ⟨38680256563096764896772443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25786837708731176597848295 38680256563096764896772443)
          ·
            refine ⟨58020384844645147345158665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38680256563096764896772443 58020384844645147345158665)
            ·
              refine ⟨43515288633483860508868999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58020384844645147345158665 43515288633483860508868999)
              ·
                refine ⟨65272932950225790763303499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43515288633483860508868999 65272932950225790763303499)
                ·
                  refine ⟨97909399425338686144955249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65272932950225790763303499 97909399425338686144955249)
                  ·
                    refine ⟨73432049569004014608716437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97909399425338686144955249 73432049569004014608716437)
                    ·
                      refine ⟨3442127323547063184783583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73432049569004014608716437 3442127323547063184783583)
                      ·
                        rfl

theorem cell23_6703519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6703519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703519 prefixEnd_6703519 := by exact prefixLift 6703519
  have htrace : WordTrace (prefixWord ++ tailWord_6703519) baseStart_6703519 baseEnd_6703519 := by
    simpa [prefixWord, tailWord_6703519, baseEnd_6703519] using wordTrace_append hprefix tailTrace_6703519
  have hstable : (prefixWord ++ tailWord_6703519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703519).length < 2 ^ (prefixWord ++ tailWord_6703519).sum := by decide
  have hdescent : baseEnd_6703519 < baseStart_6703519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703520 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 1, 4]
def baseStart_6703520 : Nat := 118140960795 + 6703520 * 2 ^ 59
def prefixEnd_6703520 : Nat := 4983230072969 + 3 ^ 40 * 6703520 * 2
def baseEnd_6703520 : Nat := 1147375945675905893623693

theorem tailTrace_6703520 : CollatzResearch.WordTrace tailWord_6703520 prefixEnd_6703520 1147375945675905893623693 := by
  unfold tailWord_6703520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122248730337149692456674007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162998307116199589942232009 122248730337149692456674007)
  ·
    refine ⟨183373095505724538685011011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122248730337149692456674007 183373095505724538685011011)
    ·
      refine ⟨275059643258586808027516517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183373095505724538685011011 275059643258586808027516517)
      ·
        refine ⟨51573683110985026505159347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275059643258586808027516517 51573683110985026505159347)
        ·
          refine ⟨77360524666477539757739021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51573683110985026505159347 77360524666477539757739021)
          ·
            refine ⟨29010196749929077409152133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77360524666477539757739021 29010196749929077409152133)
            ·
              refine ⟨5439411890611702014216025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29010196749929077409152133 5439411890611702014216025)
              ·
                refine ⟨4079558917958776510662019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439411890611702014216025 4079558917958776510662019)
                ·
                  refine ⟨6119338376938164765993029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079558917958776510662019 6119338376938164765993029)
                  ·
                    refine ⟨1147375945675905893623693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119338376938164765993029 1147375945675905893623693)
                    ·
                      rfl

theorem cell23_6703520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_6703520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703520 prefixEnd_6703520 := by exact prefixLift 6703520
  have htrace : WordTrace (prefixWord ++ tailWord_6703520) baseStart_6703520 baseEnd_6703520 := by
    simpa [prefixWord, tailWord_6703520, baseEnd_6703520] using wordTrace_append hprefix tailTrace_6703520
  have hstable : (prefixWord ++ tailWord_6703520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703520).length < 2 ^ (prefixWord ++ tailWord_6703520).sum := by decide
  have hdescent : baseEnd_6703520 < baseStart_6703520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703543 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_6703543 : Nat := 118140960795 + 6703543 * 2 ^ 59
def prefixEnd_6703543 : Nat := 4983230072969 + 3 ^ 40 * 6703543 * 2
def baseEnd_6703543 : Nat := 3442139647082771090883473

theorem tailTrace_6703543 : CollatzResearch.WordTrace tailWord_6703543 prefixEnd_6703543 3442139647082771090883473 := by
  unfold tailWord_6703543
  simp only [CollatzResearch.WordTrace]
  refine ⟨244498299553216059841435283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162998866368810706560956855 244498299553216059841435283)
  ·
    refine ⟨366747449329824089762152925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244498299553216059841435283 366747449329824089762152925)
    ·
      refine ⟨137530293498684033660807347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366747449329824089762152925 137530293498684033660807347)
      ·
        refine ⟨206295440248026050491211021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137530293498684033660807347 206295440248026050491211021)
        ·
          refine ⟨77360790093009768934204133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206295440248026050491211021 77360790093009768934204133)
          ·
            refine ⟨14505148142439331675163275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77360790093009768934204133 14505148142439331675163275)
            ·
              refine ⟨21757722213658997512744913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14505148142439331675163275 21757722213658997512744913)
              ·
                refine ⟨16318291660244248134558685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21757722213658997512744913 16318291660244248134558685)
                ·
                  refine ⟨6119359372591593050459507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16318291660244248134558685 6119359372591593050459507)
                  ·
                    refine ⟨9179039058887389575689261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6119359372591593050459507 9179039058887389575689261)
                    ·
                      refine ⟨3442139647082771090883473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179039058887389575689261 3442139647082771090883473)
                      ·
                        rfl

theorem cell23_6703543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_6703543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703543 prefixEnd_6703543 := by exact prefixLift 6703543
  have htrace : WordTrace (prefixWord ++ tailWord_6703543) baseStart_6703543 baseEnd_6703543 := by
    simpa [prefixWord, tailWord_6703543, baseEnd_6703543] using wordTrace_append hprefix tailTrace_6703543
  have hstable : (prefixWord ++ tailWord_6703543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703543).length < 2 ^ (prefixWord ++ tailWord_6703543).sum := by decide
  have hdescent : baseEnd_6703543 < baseStart_6703543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703560 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_6703560 : Nat := 118140960795 + 6703560 * 2 ^ 59
def prefixEnd_6703560 : Nat := 4983230072969 + 3 ^ 40 * 6703560 * 2
def baseEnd_6703560 : Nat := 3442148376253897524370895

theorem tailTrace_6703560 : CollatzResearch.WordTrace tailWord_6703560 prefixEnd_6703560 3442148376253897524370895 := by
  unfold tailWord_6703560
  simp only [CollatzResearch.WordTrace]
  refine ⟨122249459797077235872402067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162999279729436314496536089 122249459797077235872402067)
  ·
    refine ⟨183374189695615853808603101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122249459797077235872402067 183374189695615853808603101)
    ·
      refine ⟨68765321135855945178226163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183374189695615853808603101 68765321135855945178226163)
      ·
        refine ⟨103147981703783917767339245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68765321135855945178226163 103147981703783917767339245)
        ·
          refine ⟨38680493138918969162752217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103147981703783917767339245 38680493138918969162752217)
          ·
            refine ⟨29010369854189226872064163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38680493138918969162752217 29010369854189226872064163)
            ·
              refine ⟨43515554781283840308096245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29010369854189226872064163 43515554781283840308096245)
              ·
                refine ⟨4079583260745360028884023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43515554781283840308096245 4079583260745360028884023)
                ·
                  refine ⟨6119374891118040043326035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079583260745360028884023 6119374891118040043326035)
                  ·
                    refine ⟨9179062336677060064989053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6119374891118040043326035 9179062336677060064989053)
                    ·
                      refine ⟨3442148376253897524370895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179062336677060064989053 3442148376253897524370895)
                      ·
                        rfl

theorem cell23_6703560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_6703560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703560 prefixEnd_6703560 := by exact prefixLift 6703560
  have htrace : WordTrace (prefixWord ++ tailWord_6703560) baseStart_6703560 baseEnd_6703560 := by
    simpa [prefixWord, tailWord_6703560, baseEnd_6703560] using wordTrace_append hprefix tailTrace_6703560
  have hstable : (prefixWord ++ tailWord_6703560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703560).length < 2 ^ (prefixWord ++ tailWord_6703560).sum := by decide
  have hdescent : baseEnd_6703560 < baseStart_6703560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_6703569 : Nat := 118140960795 + 6703569 * 2 ^ 59
def prefixEnd_6703569 : Nat := 4983230072969 + 3 ^ 40 * 6703569 * 2
def baseEnd_6703569 : Nat := 3442152997579787989158353

theorem tailTrace_6703569 : CollatzResearch.WordTrace tailWord_6703569 prefixEnd_6703569 3442152997579787989158353 := by
  unfold tailWord_6703569
  simp only [CollatzResearch.WordTrace]
  refine ⟨244499247851121866281881761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162999498567414577521254507 244499247851121866281881761)
  ·
    refine ⟨183374435888341399711411321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244499247851121866281881761 183374435888341399711411321)
    ·
      refine ⟨137530826916256049783558491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183374435888341399711411321 137530826916256049783558491)
      ·
        refine ⟨206296240374384074675337737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137530826916256049783558491 206296240374384074675337737)
        ·
          refine ⟨154722180280788056006503303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206296240374384074675337737 154722180280788056006503303)
          ·
            refine ⟨232083270421182084009754955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154722180280788056006503303 232083270421182084009754955)
            ·
              refine ⟨348124905631773126014632433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232083270421182084009754955 348124905631773126014632433)
              ·
                refine ⟨261093679223829844510974325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348124905631773126014632433 261093679223829844510974325)
                ·
                  refine ⟨24477532427234047922903843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261093679223829844510974325 24477532427234047922903843)
                  ·
                    refine ⟨36716298640851071884355765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24477532427234047922903843 36716298640851071884355765)
                    ·
                      refine ⟨3442152997579787989158353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36716298640851071884355765 3442152997579787989158353)
                      ·
                        rfl

theorem cell23_6703569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_6703569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703569 prefixEnd_6703569 := by exact prefixLift 6703569
  have htrace : WordTrace (prefixWord ++ tailWord_6703569) baseStart_6703569 baseEnd_6703569 := by
    simpa [prefixWord, tailWord_6703569, baseEnd_6703569] using wordTrace_append hprefix tailTrace_6703569
  have hstable : (prefixWord ++ tailWord_6703569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703569).length < 2 ^ (prefixWord ++ tailWord_6703569).sum := by decide
  have hdescent : baseEnd_6703569 < baseStart_6703569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703603 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 3]
def baseStart_6703603 : Nat := 118140960795 + 6703603 * 2 ^ 59
def prefixEnd_6703603 : Nat := 4983230072969 + 3 ^ 40 * 6703603 * 2
def baseEnd_6703603 : Nat := 3442170455922040856133197

theorem tailTrace_6703603 : CollatzResearch.WordTrace tailWord_6703603 prefixEnd_6703603 3442170455922040856133197 := by
  unfold tailWord_6703603
  simp only [CollatzResearch.WordTrace]
  refine ⟨244500487932998690088619463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163000325288665793392412975 244500487932998690088619463)
  ·
    refine ⟨366750731899498035132929195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244500487932998690088619463 366750731899498035132929195)
    ·
      refine ⟨550126097849247052699393793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366750731899498035132929195 550126097849247052699393793)
      ·
        refine ⟨412594573386935289524545345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550126097849247052699393793 412594573386935289524545345)
        ·
          refine ⟨309445930040201467143409009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412594573386935289524545345 309445930040201467143409009)
          ·
            refine ⟨232084447530151100357556757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309445930040201467143409009 232084447530151100357556757)
            ·
              refine ⟨10878958477975832829260473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232084447530151100357556757 10878958477975832829260473)
              ·
                refine ⟨8159218858481874621945355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878958477975832829260473 8159218858481874621945355)
                ·
                  refine ⟨12238828287722811932918033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159218858481874621945355 12238828287722811932918033)
                  ·
                    refine ⟨9179121215792108949688525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12238828287722811932918033 9179121215792108949688525)
                    ·
                      refine ⟨3442170455922040856133197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179121215792108949688525 3442170455922040856133197)
                      ·
                        rfl

theorem cell23_6703603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_6703603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703603 prefixEnd_6703603 := by exact prefixLift 6703603
  have htrace : WordTrace (prefixWord ++ tailWord_6703603) baseStart_6703603 baseEnd_6703603 := by
    simpa [prefixWord, tailWord_6703603, baseEnd_6703603] using wordTrace_append hprefix tailTrace_6703603
  have hstable : (prefixWord ++ tailWord_6703603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703603).length < 2 ^ (prefixWord ++ tailWord_6703603).sum := by decide
  have hdescent : baseEnd_6703603 < baseStart_6703603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703606 : List Nat := [5, 1, 1, 1, 2, 1, 3, 9]
def baseStart_6703606 : Nat := 118140960795 + 6703606 * 2 ^ 59
def prefixEnd_6703606 : Nat := 4983230072969 + 3 ^ 40 * 6703606 * 2
def baseEnd_6703606 : Nat := 127487851717185346088729

theorem tailTrace_6703606 : CollatzResearch.WordTrace tailWord_6703606 prefixEnd_6703606 127487851717185346088729 := by
  unfold tailWord_6703606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281287334499238850061167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163000398234658547733985781 15281287334499238850061167)
  ·
    refine ⟨22921931001748858275091751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15281287334499238850061167 22921931001748858275091751)
    ·
      refine ⟨34382896502623287412637627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22921931001748858275091751 34382896502623287412637627)
      ·
        refine ⟨51574344753934931118956441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34382896502623287412637627 51574344753934931118956441)
        ·
          refine ⟨38680758565451198339217331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51574344753934931118956441 38680758565451198339217331)
          ·
            refine ⟨58021137848176797508825997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38680758565451198339217331 58021137848176797508825997)
            ·
              refine ⟨21757926693066299065809749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58021137848176797508825997 21757926693066299065809749)
              ·
                refine ⟨127487851717185346088729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21757926693066299065809749 127487851717185346088729)
                ·
                  rfl

theorem cell23_6703606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_6703606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703606 prefixEnd_6703606 := by exact prefixLift 6703606
  have htrace : WordTrace (prefixWord ++ tailWord_6703606) baseStart_6703606 baseEnd_6703606 := by
    simpa [prefixWord, tailWord_6703606, baseEnd_6703606] using wordTrace_append hprefix tailTrace_6703606
  have hstable : (prefixWord ++ tailWord_6703606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703606).length < 2 ^ (prefixWord ++ tailWord_6703606).sum := by decide
  have hdescent : baseEnd_6703606 < baseStart_6703606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703620 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6703620 : Nat := 118140960795 + 6703620 * 2 ^ 59
def prefixEnd_6703620 : Nat := 4983230072969 + 3 ^ 40 * 6703620 * 2
def baseEnd_6703620 : Nat := 3442179185093167289620619

theorem tailTrace_6703620 : CollatzResearch.WordTrace tailWord_6703620 prefixEnd_6703620 3442179185093167289620619 := by
  unfold tailWord_6703620
  simp only [CollatzResearch.WordTrace]
  refine ⟨122250553986968550995994157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163000738649291401327992209 122250553986968550995994157)
  ·
    refine ⟨45843957745113206623497809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122250553986968550995994157 45843957745113206623497809)
    ·
      refine ⟨34382968308834904967623357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45843957745113206623497809 34382968308834904967623357)
      ·
        refine ⟨12893613115813089362858759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34382968308834904967623357 12893613115813089362858759)
        ·
          refine ⟨19340419673719634044288139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893613115813089362858759 19340419673719634044288139)
          ·
            refine ⟨29010629510579451066432209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19340419673719634044288139 29010629510579451066432209)
            ·
              refine ⟨21757972132934588299824157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29010629510579451066432209 21757972132934588299824157)
              ·
                refine ⟨8159239549850470612434059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21757972132934588299824157 8159239549850470612434059)
                ·
                  refine ⟨12238859324775705918651089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159239549850470612434059 12238859324775705918651089)
                  ·
                    refine ⟨9179144493581779438988317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12238859324775705918651089 9179144493581779438988317)
                    ·
                      refine ⟨3442179185093167289620619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179144493581779438988317 3442179185093167289620619)
                      ·
                        rfl

theorem cell23_6703620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6703620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703620 prefixEnd_6703620 := by exact prefixLift 6703620
  have htrace : WordTrace (prefixWord ++ tailWord_6703620) baseStart_6703620 baseEnd_6703620 := by
    simpa [prefixWord, tailWord_6703620, baseEnd_6703620] using wordTrace_append hprefix tailTrace_6703620
  have hstable : (prefixWord ++ tailWord_6703620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703620).length < 2 ^ (prefixWord ++ tailWord_6703620).sum := by decide
  have hdescent : baseEnd_6703620 < baseStart_6703620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703623 : List Nat := [1, 1, 4, 3, 4, 1, 9]
def baseStart_6703623 : Nat := 118140960795 + 6703623 * 2 ^ 59
def prefixEnd_6703623 : Nat := 4983230072969 + 3 ^ 40 * 6703623 * 2
def baseEnd_6703623 : Nat := 42496058339939886146705

theorem tailTrace_6703623 : CollatzResearch.WordTrace tailWord_6703623 prefixEnd_6703623 42496058339939886146705 := by
  unfold tailWord_6703623
  simp only [CollatzResearch.WordTrace]
  refine ⟨244501217392926233504347523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163000811595284155669565015 244501217392926233504347523)
  ·
    refine ⟨366751826089389350256521285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244501217392926233504347523 366751826089389350256521285)
    ·
      refine ⟨68765967391760503173097741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366751826089389350256521285 68765967391760503173097741)
      ·
        refine ⟨25787237771910188689911653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68765967391760503173097741 25787237771910188689911653)
        ·
          refine ⟨4835107082233160379358435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25787237771910188689911653 4835107082233160379358435)
          ·
            refine ⟨7252660623349740569037653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835107082233160379358435 7252660623349740569037653)
            ·
              refine ⟨42496058339939886146705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7252660623349740569037653 42496058339939886146705)
              ·
                rfl

theorem cell23_6703623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 9].length) (baseStart_6703623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703623 prefixEnd_6703623 := by exact prefixLift 6703623
  have htrace : WordTrace (prefixWord ++ tailWord_6703623) baseStart_6703623 baseEnd_6703623 := by
    simpa [prefixWord, tailWord_6703623, baseEnd_6703623] using wordTrace_append hprefix tailTrace_6703623
  have hstable : (prefixWord ++ tailWord_6703623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703623).length < 2 ^ (prefixWord ++ tailWord_6703623).sum := by decide
  have hdescent : baseEnd_6703623 < baseStart_6703623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703741 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_6703741 : Nat := 118140960795 + 6703741 * 2 ^ 59
def prefixEnd_6703741 : Nat := 4983230072969 + 3 ^ 40 * 6703741 * 2
def baseEnd_6703741 : Nat := 3442241316252361316207563

theorem tailTrace_6703741 : CollatzResearch.WordTrace tailWord_6703741 prefixEnd_6703741 3442241316252361316207563 := by
  unfold tailWord_6703741
  simp only [CollatzResearch.WordTrace]
  refine ⟨244505521206498739657143077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163003680804332493104762051 244505521206498739657143077)
  ·
    refine ⟨45844785226218513685714327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244505521206498739657143077 45844785226218513685714327)
    ·
      refine ⟨68767177839327770528571491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45844785226218513685714327 68767177839327770528571491)
      ·
        refine ⟨103150766758991655792857237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68767177839327770528571491 103150766758991655792857237)
        ·
          refine ⟨4835192191827733865290183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103150766758991655792857237 4835192191827733865290183)
          ·
            refine ⟨7252788287741600797935275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835192191827733865290183 7252788287741600797935275)
            ·
              refine ⟨10879182431612401196902913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252788287741600797935275 10879182431612401196902913)
              ·
                refine ⟨8159386823709300897677185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10879182431612401196902913 8159386823709300897677185)
                ·
                  refine ⟨6119540117781975673257889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159386823709300897677185 6119540117781975673257889)
                  ·
                    refine ⟨4589655088336481754943417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119540117781975673257889 4589655088336481754943417)
                    ·
                      refine ⟨3442241316252361316207563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589655088336481754943417 3442241316252361316207563)
                      ·
                        rfl

theorem cell23_6703741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_6703741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703741 prefixEnd_6703741 := by exact prefixLift 6703741
  have htrace : WordTrace (prefixWord ++ tailWord_6703741) baseStart_6703741 baseEnd_6703741 := by
    simpa [prefixWord, tailWord_6703741, baseEnd_6703741] using wordTrace_append hprefix tailTrace_6703741
  have hstable : (prefixWord ++ tailWord_6703741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703741).length < 2 ^ (prefixWord ++ tailWord_6703741).sum := by decide
  have hdescent : baseEnd_6703741 < baseStart_6703741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703820 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 6]
def baseStart_6703820 : Nat := 118140960795 + 6703820 * 2 ^ 59
def prefixEnd_6703820 : Nat := 4983230072969 + 3 ^ 40 * 6703820 * 2
def baseEnd_6703820 : Nat := 382475764580451834124411

theorem tailTrace_6703820 : CollatzResearch.WordTrace tailWord_6703820 prefixEnd_6703820 382475764580451834124411 := by
  unfold tailWord_6703820
  simp only [CollatzResearch.WordTrace]
  refine ⟨122254201286606268074634457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163005601715475024099512609 122254201286606268074634457)
  ·
    refine ⟨91690650964954701055975843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122254201286606268074634457 91690650964954701055975843)
    ·
      refine ⟨137535976447432051583963765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91690650964954701055975843 137535976447432051583963765)
      ·
        refine ⟨12893997791946754835996603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137535976447432051583963765 12893997791946754835996603)
        ·
          refine ⟨19340996687920132253994905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893997791946754835996603 19340996687920132253994905)
          ·
            refine ⟨14505747515940099190496179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19340996687920132253994905 14505747515940099190496179)
            ·
              refine ⟨21758621273910148785744269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14505747515940099190496179 21758621273910148785744269)
              ·
                refine ⟨8159482977716305794654101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21758621273910148785744269 8159482977716305794654101)
                ·
                  refine ⟨382475764580451834124411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8159482977716305794654101 382475764580451834124411)
                  ·
                    rfl

theorem cell23_6703820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_6703820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703820 prefixEnd_6703820 := by exact prefixLift 6703820
  have htrace : WordTrace (prefixWord ++ tailWord_6703820) baseStart_6703820 baseEnd_6703820 := by
    simpa [prefixWord, tailWord_6703820, baseEnd_6703820] using wordTrace_append hprefix tailTrace_6703820
  have hstable : (prefixWord ++ tailWord_6703820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703820).length < 2 ^ (prefixWord ++ tailWord_6703820).sum := by decide
  have hdescent : baseEnd_6703820 < baseStart_6703820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703833 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_6703833 : Nat := 118140960795 + 6703833 * 2 ^ 59
def prefixEnd_6703833 : Nat := 4983230072969 + 3 ^ 40 * 6703833 * 2
def baseEnd_6703833 : Nat := 1147429518824191652085713

theorem tailTrace_6703833 : CollatzResearch.WordTrace tailWord_6703833 prefixEnd_6703833 1147429518824191652085713 := by
  unfold tailWord_6703833
  simp only [CollatzResearch.WordTrace]
  refine ⟨244508876722165439369492153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163005917814776959579661435 244508876722165439369492153)
  ·
    refine ⟨183381657541624079527119115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244508876722165439369492153 183381657541624079527119115)
    ·
      refine ⟨275072486312436119290678673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183381657541624079527119115 275072486312436119290678673)
      ·
        refine ⟨206304364734327089468009005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275072486312436119290678673 206304364734327089468009005)
        ·
          refine ⟨77364136775372658550503377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206304364734327089468009005 77364136775372658550503377)
          ·
            refine ⟨58023102581529493912877533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77364136775372658550503377 58023102581529493912877533)
            ·
              refine ⟨21758663468073560217329075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58023102581529493912877533 21758663468073560217329075)
              ·
                refine ⟨32637995202110340325993613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21758663468073560217329075 32637995202110340325993613)
                ·
                  refine ⟨12239248200791377622247605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32637995202110340325993613 12239248200791377622247605)
                  ·
                    refine ⟨1147429518824191652085713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12239248200791377622247605 1147429518824191652085713)
                    ·
                      rfl

theorem cell23_6703833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_6703833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703833 prefixEnd_6703833 := by exact prefixLift 6703833
  have htrace : WordTrace (prefixWord ++ tailWord_6703833) baseStart_6703833 baseEnd_6703833 := by
    simpa [prefixWord, tailWord_6703833, baseEnd_6703833] using wordTrace_append hprefix tailTrace_6703833
  have hstable : (prefixWord ++ tailWord_6703833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703833).length < 2 ^ (prefixWord ++ tailWord_6703833).sum := by decide
  have hdescent : baseEnd_6703833 < baseStart_6703833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703873 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6703873 : Nat := 118140960795 + 6703873 * 2 ^ 59
def prefixEnd_6703873 : Nat := 4983230072969 + 3 ^ 40 * 6703873 * 2
def baseEnd_6703873 : Nat := 3442309095698754799756955

theorem tailTrace_6703873 : CollatzResearch.WordTrace tailWord_6703873 prefixEnd_6703873 3442309095698754799756955 := by
  unfold tailWord_6703873
  simp only [CollatzResearch.WordTrace]
  refine ⟨244510335642020526200948273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163006890428013684133965515 244510335642020526200948273)
  ·
    refine ⟨183382751731515394650711205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244510335642020526200948273 183382751731515394650711205)
    ·
      refine ⟨34384265949659136497008351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183382751731515394650711205 34384265949659136497008351)
      ·
        refine ⟨51576398924488704745512527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34384265949659136497008351 51576398924488704745512527)
        ·
          refine ⟨77364598386733057118268791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51576398924488704745512527 77364598386733057118268791)
          ·
            refine ⟨116046897580099585677403187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77364598386733057118268791 116046897580099585677403187)
            ·
              refine ⟨174070346370149378516104781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116046897580099585677403187 174070346370149378516104781)
              ·
                refine ⟨65276379888806016943539293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174070346370149378516104781 65276379888806016943539293)
                ·
                  refine ⟨24478642458302256353827235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65276379888806016943539293 24478642458302256353827235)
                  ·
                    refine ⟨36717963687453384530740853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24478642458302256353827235 36717963687453384530740853)
                    ·
                      refine ⟨3442309095698754799756955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36717963687453384530740853 3442309095698754799756955)
                      ·
                        rfl

theorem cell23_6703873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6703873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703873 prefixEnd_6703873 := by exact prefixLift 6703873
  have htrace : WordTrace (prefixWord ++ tailWord_6703873) baseStart_6703873 baseEnd_6703873 := by
    simpa [prefixWord, tailWord_6703873, baseEnd_6703873] using wordTrace_append hprefix tailTrace_6703873
  have hstable : (prefixWord ++ tailWord_6703873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703873).length < 2 ^ (prefixWord ++ tailWord_6703873).sum := by decide
  have hdescent : baseEnd_6703873 < baseStart_6703873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703880 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_6703880 : Nat := 118140960795 + 6703880 * 2 ^ 59
def prefixEnd_6703880 : Nat := 4983230072969 + 3 ^ 40 * 6703880 * 2
def baseEnd_6703880 : Nat := 1147437563354445424123141

theorem tailTrace_6703880 : CollatzResearch.WordTrace tailWord_6703880 prefixEnd_6703880 1147437563354445424123141 := by
  unfold tailWord_6703880
  simp only [CollatzResearch.WordTrace]
  refine ⟨122255295476497583198226547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163007060635330110930968729 122255295476497583198226547)
  ·
    refine ⟨183382943214746374797339821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122255295476497583198226547 183382943214746374797339821)
    ·
      refine ⟨68768603705529890549002433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183382943214746374797339821 68768603705529890549002433)
      ·
        refine ⟨51576452779147417911751825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68768603705529890549002433 51576452779147417911751825)
        ·
          refine ⟨38682339584360563433813869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51576452779147417911751825 38682339584360563433813869)
          ·
            refine ⟨14505877344135211287680201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38682339584360563433813869 14505877344135211287680201)
            ·
              refine ⟨10879408008101408465760151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14505877344135211287680201 10879408008101408465760151)
              ·
                refine ⟨16319112012152112698640227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879408008101408465760151 16319112012152112698640227)
                ·
                  refine ⟨24478668018228169047960341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16319112012152112698640227 24478668018228169047960341)
                  ·
                    refine ⟨1147437563354445424123141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24478668018228169047960341 1147437563354445424123141)
                    ·
                      rfl

theorem cell23_6703880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_6703880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703880 prefixEnd_6703880 := by exact prefixLift 6703880
  have htrace : WordTrace (prefixWord ++ tailWord_6703880) baseStart_6703880 baseEnd_6703880 := by
    simpa [prefixWord, tailWord_6703880, baseEnd_6703880] using wordTrace_append hprefix tailTrace_6703880
  have hstable : (prefixWord ++ tailWord_6703880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703880).length < 2 ^ (prefixWord ++ tailWord_6703880).sum := by decide
  have hdescent : baseEnd_6703880 < baseStart_6703880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703887 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 3, 2, 2]
def baseStart_6703887 : Nat := 118140960795 + 6703887 * 2 ^ 59
def prefixEnd_6703887 : Nat := 4983230072969 + 3 ^ 40 * 6703887 * 2
def baseEnd_6703887 : Nat := 3442316284427917744981891

theorem tailTrace_6703887 : CollatzResearch.WordTrace tailWord_6703887 prefixEnd_6703887 3442316284427917744981891 := by
  unfold tailWord_6703887
  simp only [CollatzResearch.WordTrace]
  refine ⟨244510846263969806591957915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163007230842646537727971943 244510846263969806591957915)
  ·
    refine ⟨366766269395954709887936873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244510846263969806591957915 366766269395954709887936873)
    ·
      refine ⟨275074702046966032415952655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366766269395954709887936873 275074702046966032415952655)
      ·
        refine ⟨412612053070449048623928983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275074702046966032415952655 412612053070449048623928983)
        ·
          refine ⟨618918079605673572935893475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412612053070449048623928983 618918079605673572935893475)
          ·
            refine ⟨928377119408510359403840213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618918079605673572935893475 928377119408510359403840213)
            ·
              refine ⟨21758838736136961548527505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 928377119408510359403840213 21758838736136961548527505)
              ·
                refine ⟨16319129052102721161395629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21758838736136961548527505 16319129052102721161395629)
                ·
                  refine ⟨6119673394538520435523361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16319129052102721161395629 6119673394538520435523361)
                  ·
                    refine ⟨4589755045903890326642521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119673394538520435523361 4589755045903890326642521)
                    ·
                      refine ⟨3442316284427917744981891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589755045903890326642521 3442316284427917744981891)
                      ·
                        rfl

theorem cell23_6703887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2, 2].length) (baseStart_6703887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703887 prefixEnd_6703887 := by exact prefixLift 6703887
  have htrace : WordTrace (prefixWord ++ tailWord_6703887) baseStart_6703887 baseEnd_6703887 := by
    simpa [prefixWord, tailWord_6703887, baseEnd_6703887] using wordTrace_append hprefix tailTrace_6703887
  have hstable : (prefixWord ++ tailWord_6703887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703887).length < 2 ^ (prefixWord ++ tailWord_6703887).sum := by decide
  have hdescent : baseEnd_6703887 < baseStart_6703887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703900 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6703900 : Nat := 118140960795 + 6703900 * 2 ^ 59
def prefixEnd_6703900 : Nat := 4983230072969 + 3 ^ 40 * 6703900 * 2
def baseEnd_6703900 : Nat := 3442322959676426194119331

theorem tailTrace_6703900 : CollatzResearch.WordTrace tailWord_6703900 prefixEnd_6703900 3442322959676426194119331 := by
  unfold tailWord_6703900
  simp only [CollatzResearch.WordTrace]
  refine ⟨122255660206461354906090577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163007546941948473208120769 122255660206461354906090577)
  ·
    refine ⟨91691745154846016179567933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122255660206461354906090577 91691745154846016179567933)
    ·
      refine ⟨34384404433067256067337975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91691745154846016179567933 34384404433067256067337975)
      ·
        refine ⟨51576606649600884101006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34384404433067256067337975 51576606649600884101006963)
        ·
          refine ⟨77364909974401326151510445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51576606649600884101006963 77364909974401326151510445)
          ·
            refine ⟨29011841240400497306816417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77364909974401326151510445 29011841240400497306816417)
            ·
              refine ⟨21758880930300372980112313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29011841240400497306816417 21758880930300372980112313)
              ·
                refine ⟨16319160697725279735084235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21758880930300372980112313 16319160697725279735084235)
                ·
                  refine ⟨24478741046587919602626353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16319160697725279735084235 24478741046587919602626353)
                  ·
                    refine ⟨18359055784940939701969765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24478741046587919602626353 18359055784940939701969765)
                    ·
                      refine ⟨3442322959676426194119331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18359055784940939701969765 3442322959676426194119331)
                      ·
                        rfl

theorem cell23_6703900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6703900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703900 prefixEnd_6703900 := by exact prefixLift 6703900
  have htrace : WordTrace (prefixWord ++ tailWord_6703900) baseStart_6703900 baseEnd_6703900 := by
    simpa [prefixWord, tailWord_6703900, baseEnd_6703900] using wordTrace_append hprefix tailTrace_6703900
  have hstable : (prefixWord ++ tailWord_6703900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703900).length < 2 ^ (prefixWord ++ tailWord_6703900).sum := by decide
  have hdescent : baseEnd_6703900 < baseStart_6703900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703901 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6703901 : Nat := 118140960795 + 6703901 * 2 ^ 59
def prefixEnd_6703901 : Nat := 4983230072969 + 3 ^ 40 * 6703901 * 2
def baseEnd_6703901 : Nat := 1147441157719026896735609

theorem tailTrace_6703901 : CollatzResearch.WordTrace tailWord_6703901 prefixEnd_6703901 1147441157719026896735609 := by
  unfold tailWord_6703901
  simp only [CollatzResearch.WordTrace]
  refine ⟨244511356885919086982967557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163007571257279391321978371 244511356885919086982967557)
  ·
    refine ⟨45845879416109828809306417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244511356885919086982967557 45845879416109828809306417)
    ·
      refine ⟨34384409562082371606979813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45845879416109828809306417 34384409562082371606979813)
      ·
        refine ⟨6447076792890444676308715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34384409562082371606979813 6447076792890444676308715)
        ·
          refine ⟨9670615189335667014463073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447076792890444676308715 9670615189335667014463073)
          ·
            refine ⟨7252961392001750260847305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670615189335667014463073 7252961392001750260847305)
            ·
              refine ⟨5439721044001312695635479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252961392001750260847305 5439721044001312695635479)
              ·
                refine ⟨8159581566001969043453219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439721044001312695635479 8159581566001969043453219)
                ·
                  refine ⟨12239372349002953565179829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159581566001969043453219 12239372349002953565179829)
                  ·
                    refine ⟨1147441157719026896735609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12239372349002953565179829 1147441157719026896735609)
                    ·
                      rfl

theorem cell23_6703901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6703901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703901 prefixEnd_6703901 := by exact prefixLift 6703901
  have htrace : WordTrace (prefixWord ++ tailWord_6703901) baseStart_6703901 baseEnd_6703901 := by
    simpa [prefixWord, tailWord_6703901, baseEnd_6703901] using wordTrace_append hprefix tailTrace_6703901
  have hstable : (prefixWord ++ tailWord_6703901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703901).length < 2 ^ (prefixWord ++ tailWord_6703901).sum := by decide
  have hdescent : baseEnd_6703901 < baseStart_6703901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703904 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6703904 : Nat := 118140960795 + 6703904 * 2 ^ 59
def prefixEnd_6703904 : Nat := 4983230072969 + 3 ^ 40 * 6703904 * 2
def baseEnd_6703904 : Nat := 3442325013599044178469313

theorem tailTrace_6703904 : CollatzResearch.WordTrace tailWord_6703904 prefixEnd_6703904 3442325013599044178469313 := by
  unfold tailWord_6703904
  simp only [CollatzResearch.WordTrace]
  refine ⟨122255733152454109247663383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163007644203272145663551177 122255733152454109247663383)
  ·
    refine ⟨183383599728681163871495075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122255733152454109247663383 183383599728681163871495075)
    ·
      refine ⟨275075399593021745807242613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183383599728681163871495075 275075399593021745807242613)
      ·
        refine ⟨25788318711845788669428995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275075399593021745807242613 25788318711845788669428995)
        ·
          refine ⟨38682478067768683004143493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25788318711845788669428995 38682478067768683004143493)
          ·
            refine ⟨7252964637706628063276905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38682478067768683004143493 7252964637706628063276905)
            ·
              refine ⟨5439723478279971047457679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252964637706628063276905 5439723478279971047457679)
              ·
                refine ⟨8159585217419956571186519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439723478279971047457679 8159585217419956571186519)
                ·
                  refine ⟨12239377826129934856779779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159585217419956571186519 12239377826129934856779779)
                  ·
                    refine ⟨18359066739194902285169669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12239377826129934856779779 18359066739194902285169669)
                    ·
                      refine ⟨3442325013599044178469313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18359066739194902285169669 3442325013599044178469313)
                      ·
                        rfl

theorem cell23_6703904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6703904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703904 prefixEnd_6703904 := by exact prefixLift 6703904
  have htrace : WordTrace (prefixWord ++ tailWord_6703904) baseStart_6703904 baseEnd_6703904 := by
    simpa [prefixWord, tailWord_6703904, baseEnd_6703904] using wordTrace_append hprefix tailTrace_6703904
  have hstable : (prefixWord ++ tailWord_6703904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703904).length < 2 ^ (prefixWord ++ tailWord_6703904).sum := by decide
  have hdescent : baseEnd_6703904 < baseStart_6703904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703914 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_6703914 : Nat := 118140960795 + 6703914 * 2 ^ 59
def prefixEnd_6703914 : Nat := 4983230072969 + 3 ^ 40 * 6703914 * 2
def baseEnd_6703914 : Nat := 1147443382801863046448089

theorem tailTrace_6703914 : CollatzResearch.WordTrace tailWord_6703914 prefixEnd_6703914 1147443382801863046448089 := by
  unfold tailWord_6703914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127957758717997550797699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163007887356581326802127197 61127957758717997550797699)
  ·
    refine ⟨91691936638076996326196549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61127957758717997550797699 91691936638076996326196549)
    ·
      refine ⟨17192238119639436811161853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91691936638076996326196549 17192238119639436811161853)
      ·
        refine ⟨6447089294864788804185695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17192238119639436811161853 6447089294864788804185695)
        ·
          refine ⟨9670633942297183206278543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447089294864788804185695 9670633942297183206278543)
          ·
            refine ⟨14505950913445774809417815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670633942297183206278543 14505950913445774809417815)
            ·
              refine ⟨21758926370168662214126723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14505950913445774809417815 21758926370168662214126723)
              ·
                refine ⟨32638389555252993321190085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21758926370168662214126723 32638389555252993321190085)
                ·
                  refine ⟨6119698041609936247723141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32638389555252993321190085 6119698041609936247723141)
                  ·
                    refine ⟨1147443382801863046448089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119698041609936247723141 1147443382801863046448089)
                    ·
                      rfl

theorem cell23_6703914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_6703914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703914 prefixEnd_6703914 := by exact prefixLift 6703914
  have htrace : WordTrace (prefixWord ++ tailWord_6703914) baseStart_6703914 baseEnd_6703914 := by
    simpa [prefixWord, tailWord_6703914, baseEnd_6703914] using wordTrace_append hprefix tailTrace_6703914
  have hstable : (prefixWord ++ tailWord_6703914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703914).length < 2 ^ (prefixWord ++ tailWord_6703914).sum := by decide
  have hdescent : baseEnd_6703914 < baseStart_6703914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703934 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6703934 : Nat := 118140960795 + 6703934 * 2 ^ 59
def prefixEnd_6703934 : Nat := 4983230072969 + 3 ^ 40 * 6703934 * 2
def baseEnd_6703934 : Nat := 3442340418018679061094175

theorem tailTrace_6703934 : CollatzResearch.WordTrace tailWord_6703934 prefixEnd_6703934 3442340418018679061094175 := by
  unfold tailWord_6703934
  simp only [CollatzResearch.WordTrace]
  refine ⟨30564070061849941702364857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163008373663199689079279237 30564070061849941702364857)
  ·
    refine ⟨22923052546387456276773643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30564070061849941702364857 22923052546387456276773643)
    ·
      refine ⟨34384578819581184415160465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923052546387456276773643 34384578819581184415160465)
      ·
        refine ⟨25788434114685888311370349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34384578819581184415160465 25788434114685888311370349)
        ·
          refine ⟨9670662793007208116763881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25788434114685888311370349 9670662793007208116763881)
          ·
            refine ⟨7252997094755406087572911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670662793007208116763881 7252997094755406087572911)
            ·
              refine ⟨10879495642133109131359367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252997094755406087572911 10879495642133109131359367)
              ·
                refine ⟨16319243463199663697039051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879495642133109131359367 16319243463199663697039051)
                ·
                  refine ⟨24478865194799495545558577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16319243463199663697039051 24478865194799495545558577)
                  ·
                    refine ⟨18359148896099621659168933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24478865194799495545558577 18359148896099621659168933)
                    ·
                      refine ⟨3442340418018679061094175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18359148896099621659168933 3442340418018679061094175)
                      ·
                        rfl

theorem cell23_6703934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6703934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703934 prefixEnd_6703934 := by exact prefixLift 6703934
  have htrace : WordTrace (prefixWord ++ tailWord_6703934) baseStart_6703934 baseEnd_6703934 := by
    simpa [prefixWord, tailWord_6703934, baseEnd_6703934] using wordTrace_append hprefix tailTrace_6703934
  have hstable : (prefixWord ++ tailWord_6703934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703934).length < 2 ^ (prefixWord ++ tailWord_6703934).sum := by decide
  have hdescent : baseEnd_6703934 < baseStart_6703934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6703980 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_6703980 : Nat := 118140960795 + 6703980 * 2 ^ 59
def prefixEnd_6703980 : Nat := 4983230072969 + 3 ^ 40 * 6703980 * 2
def baseEnd_6703980 : Nat := 3442364038128785881118963

theorem tailTrace_6703980 : CollatzResearch.WordTrace tailWord_6703980 prefixEnd_6703980 3442364038128785881118963 := by
  unfold tailWord_6703980
  simp only [CollatzResearch.WordTrace]
  refine ⟨122257119126316441737546697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163009492168421922316728929 122257119126316441737546697)
  ·
    refine ⟨91692839344737331303160023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122257119126316441737546697 91692839344737331303160023)
    ·
      refine ⟨137539259017105996954740035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91692839344737331303160023 137539259017105996954740035)
      ·
        refine ⟨206308888525658995432110053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137539259017105996954740035 206308888525658995432110053)
        ·
          refine ⟨38682916598561061643520635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206308888525658995432110053 38682916598561061643520635)
          ·
            refine ⟨58024374897841592465280953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38682916598561061643520635 58024374897841592465280953)
            ·
              refine ⟨43518281173381194348960715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58024374897841592465280953 43518281173381194348960715)
              ·
                refine ⟨65277421760071791523441073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43518281173381194348960715 65277421760071791523441073)
                ·
                  refine ⟨48958066320053843642580805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65277421760071791523441073 48958066320053843642580805)
                  ·
                    refine ⟨9179637435010095682983901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48958066320053843642580805 9179637435010095682983901)
                    ·
                      refine ⟨3442364038128785881118963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179637435010095682983901 3442364038128785881118963)
                      ·
                        rfl

theorem cell23_6703980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_6703980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6703980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6703980 prefixEnd_6703980 := by exact prefixLift 6703980
  have htrace : WordTrace (prefixWord ++ tailWord_6703980) baseStart_6703980 baseEnd_6703980 := by
    simpa [prefixWord, tailWord_6703980, baseEnd_6703980] using wordTrace_append hprefix tailTrace_6703980
  have hstable : (prefixWord ++ tailWord_6703980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6703980).length < 2 ^ (prefixWord ++ tailWord_6703980).sum := by decide
  have hdescent : baseEnd_6703980 < baseStart_6703980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6703980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704028 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6704028 : Nat := 118140960795 + 6704028 * 2 ^ 59
def prefixEnd_6704028 : Nat := 4983230072969 + 3 ^ 40 * 6704028 * 2
def baseEnd_6704028 : Nat := 3442388685200201693318743

theorem tailTrace_6704028 : CollatzResearch.WordTrace tailWord_6704028 prefixEnd_6704028 3442388685200201693318743 := by
  unfold tailWord_6704028
  simp only [CollatzResearch.WordTrace]
  refine ⟨122257994478229493836420369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163010659304305991781893825 122257994478229493836420369)
  ·
    refine ⟨91693495858672120377315277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122257994478229493836420369 91693495858672120377315277)
    ·
      refine ⟨34385060947002045141493229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91693495858672120377315277 34385060947002045141493229)
      ·
        refine ⟨12894397855125766928059961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34385060947002045141493229 12894397855125766928059961)
        ·
          refine ⟨9670798391344325196044971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12894397855125766928059961 9670798391344325196044971)
          ·
            refine ⟨14506197587016487794067457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670798391344325196044971 14506197587016487794067457)
            ·
              refine ⟨10879648190262365845550593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14506197587016487794067457 10879648190262365845550593)
              ·
                refine ⟨8159736142696774384162945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10879648190262365845550593 8159736142696774384162945)
                ·
                  refine ⟨6119802107022580788122209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159736142696774384162945 6119802107022580788122209)
                  ·
                    refine ⟨4589851580266935591091657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119802107022580788122209 4589851580266935591091657)
                    ·
                      refine ⟨3442388685200201693318743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589851580266935591091657 3442388685200201693318743)
                      ·
                        rfl

theorem cell23_6704028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6704028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704028 prefixEnd_6704028 := by exact prefixLift 6704028
  have htrace : WordTrace (prefixWord ++ tailWord_6704028) baseStart_6704028 baseEnd_6704028 := by
    simpa [prefixWord, tailWord_6704028, baseEnd_6704028] using wordTrace_append hprefix tailTrace_6704028
  have hstable : (prefixWord ++ tailWord_6704028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704028).length < 2 ^ (prefixWord ++ tailWord_6704028).sum := by decide
  have hdescent : baseEnd_6704028 < baseStart_6704028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704034 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_6704034 : Nat := 118140960795 + 6704034 * 2 ^ 59
def prefixEnd_6704034 : Nat := 4983230072969 + 3 ^ 40 * 6704034 * 2
def baseEnd_6704034 : Nat := 382487974009347629982635

theorem tailTrace_6704034 : CollatzResearch.WordTrace tailWord_6704034 prefixEnd_6704034 382487974009347629982635 := by
  unfold tailWord_6704034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61129051948609312674389789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163010805196291500465039437 61129051948609312674389789)
  ·
    refine ⟨22923394480728492252896171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61129051948609312674389789 22923394480728492252896171)
    ·
      refine ⟨34385091721092738379344257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923394480728492252896171 34385091721092738379344257)
      ·
        refine ⟨25788818790819553784508193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34385091721092738379344257 25788818790819553784508193)
        ·
          refine ⟨19341614093114665338381145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25788818790819553784508193 19341614093114665338381145)
          ·
            refine ⟨14506210569835999003785859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19341614093114665338381145 14506210569835999003785859)
            ·
              refine ⟨21759315854753998505678789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14506210569835999003785859 21759315854753998505678789)
              ·
                refine ⟨4079871722766374719814773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21759315854753998505678789 4079871722766374719814773)
                ·
                  refine ⟨382487974009347629982635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079871722766374719814773 382487974009347629982635)
                  ·
                    rfl

theorem cell23_6704034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_6704034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704034 prefixEnd_6704034 := by exact prefixLift 6704034
  have htrace : WordTrace (prefixWord ++ tailWord_6704034) baseStart_6704034 baseEnd_6704034 := by
    simpa [prefixWord, tailWord_6704034, baseEnd_6704034] using wordTrace_append hprefix tailTrace_6704034
  have hstable : (prefixWord ++ tailWord_6704034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704034).length < 2 ^ (prefixWord ++ tailWord_6704034).sum := by decide
  have hdescent : baseEnd_6704034 < baseStart_6704034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704084 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6704084 : Nat := 118140960795 + 6704084 * 2 ^ 59
def prefixEnd_6704084 : Nat := 4983230072969 + 3 ^ 40 * 6704084 * 2
def baseEnd_6704084 : Nat := 3442417440116853474218485

theorem tailTrace_6704084 : CollatzResearch.WordTrace tailWord_6704084 prefixEnd_6704084 3442417440116853474218485 := by
  unfold tailWord_6704084
  simp only [CollatzResearch.WordTrace]
  refine ⟨122259015722128054618439653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163012020962837406157919537 122259015722128054618439653)
  ·
    refine ⟨22923565447899010240957435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122259015722128054618439653 22923565447899010240957435)
    ·
      refine ⟨34385348171848515361436153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923565447899010240957435 34385348171848515361436153)
      ·
        refine ⟨25789011128886386521077115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34385348171848515361436153 25789011128886386521077115)
        ·
          refine ⟨38683516693329579781615673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789011128886386521077115 38683516693329579781615673)
          ·
            refine ⟨29012637519997184836211755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38683516693329579781615673 29012637519997184836211755)
            ·
              refine ⟨43518956279995777254317633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29012637519997184836211755 43518956279995777254317633)
              ·
                refine ⟨32639217209996832940738225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43518956279995777254317633 32639217209996832940738225)
                ·
                  refine ⟨24479412907497624705553669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32639217209996832940738225 24479412907497624705553669)
                  ·
                    refine ⟨4589889920155804632291313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24479412907497624705553669 4589889920155804632291313)
                    ·
                      refine ⟨3442417440116853474218485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4589889920155804632291313 3442417440116853474218485)
                      ·
                        rfl

theorem cell23_6704084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6704084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704084 prefixEnd_6704084 := by exact prefixLift 6704084
  have htrace : WordTrace (prefixWord ++ tailWord_6704084) baseStart_6704084 baseEnd_6704084 := by
    simpa [prefixWord, tailWord_6704084, baseEnd_6704084] using wordTrace_append hprefix tailTrace_6704084
  have hstable : (prefixWord ++ tailWord_6704084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704084).length < 2 ^ (prefixWord ++ tailWord_6704084).sum := by decide
  have hdescent : baseEnd_6704084 < baseStart_6704084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704151 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6704151 : Nat := 118140960795 + 6704151 * 2 ^ 59
def prefixEnd_6704151 : Nat := 4983230072969 + 3 ^ 40 * 6704151 * 2
def baseEnd_6704151 : Nat := 3442451843320704712080677

theorem tailTrace_6704151 : CollatzResearch.WordTrace tailWord_6704151 prefixEnd_6704151 3442451843320704712080677 := by
  unfold tailWord_6704151
  simp only [CollatzResearch.WordTrace]
  refine ⟨244520475135013379679568307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163013650090008919786378871 244520475135013379679568307)
  ·
    refine ⟨366780712702520069519352461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244520475135013379679568307 366780712702520069519352461)
    ·
      refine ⟨137542767263445026069757173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366780712702520069519352461 137542767263445026069757173)
      ·
        refine ⟨12894634430947971194039735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137542767263445026069757173 12894634430947971194039735)
        ·
          refine ⟨19341951646421956791059603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894634430947971194039735 19341951646421956791059603)
          ·
            refine ⟨29012927469632935186589405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19341951646421956791059603 29012927469632935186589405)
            ·
              refine ⟨10879847801112350694971027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29012927469632935186589405 10879847801112350694971027)
              ·
                refine ⟨16319771701668526042456541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879847801112350694971027 16319771701668526042456541)
                ·
                  refine ⟨6119914388125697265921203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16319771701668526042456541 6119914388125697265921203)
                  ·
                    refine ⟨9179871582188545898881805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6119914388125697265921203 9179871582188545898881805)
                    ·
                      refine ⟨3442451843320704712080677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179871582188545898881805 3442451843320704712080677)
                      ·
                        rfl

theorem cell23_6704151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6704151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704151 prefixEnd_6704151 := by exact prefixLift 6704151
  have htrace : WordTrace (prefixWord ++ tailWord_6704151) baseStart_6704151 baseEnd_6704151 := by
    simpa [prefixWord, tailWord_6704151, baseEnd_6704151] using wordTrace_append hprefix tailTrace_6704151
  have hstable : (prefixWord ++ tailWord_6704151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704151).length < 2 ^ (prefixWord ++ tailWord_6704151).sum := by decide
  have hdescent : baseEnd_6704151 < baseStart_6704151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704174 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6704174 : Nat := 118140960795 + 6704174 * 2 ^ 59
def prefixEnd_6704174 : Nat := 4983230072969 + 3 ^ 40 * 6704174 * 2
def baseEnd_6704174 : Nat := 3442463653375758122093071

theorem tailTrace_6704174 : CollatzResearch.WordTrace tailWord_6704174 prefixEnd_6704174 3442463653375758122093071 := by
  unfold tailWord_6704174
  simp only [CollatzResearch.WordTrace]
  refine ⟨30565164251741256825956947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163014209342620036405103717 30565164251741256825956947)
  ·
    refine ⟨45847746377611885238935421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30565164251741256825956947 45847746377611885238935421)
    ·
      refine ⟨17192904891604456964600783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45847746377611885238935421 17192904891604456964600783)
      ·
        refine ⟨25789357337406685446901175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17192904891604456964600783 25789357337406685446901175)
        ·
          refine ⟨38684036006110028170351763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789357337406685446901175 38684036006110028170351763)
          ·
            refine ⟨58026054009165042255527645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38684036006110028170351763 58026054009165042255527645)
            ·
              refine ⟨21759770253436890845822867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58026054009165042255527645 21759770253436890845822867)
              ·
                refine ⟨32639655380155336268734301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21759770253436890845822867 32639655380155336268734301)
                ·
                  refine ⟨12239870767558251100775363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32639655380155336268734301 12239870767558251100775363)
                  ·
                    refine ⟨18359806151337376651163045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12239870767558251100775363 18359806151337376651163045)
                    ·
                      refine ⟨3442463653375758122093071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18359806151337376651163045 3442463653375758122093071)
                      ·
                        rfl

theorem cell23_6704174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6704174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704174 prefixEnd_6704174 := by exact prefixLift 6704174
  have htrace : WordTrace (prefixWord ++ tailWord_6704174) baseStart_6704174 baseEnd_6704174 := by
    simpa [prefixWord, tailWord_6704174, baseEnd_6704174] using wordTrace_append hprefix tailTrace_6704174
  have hstable : (prefixWord ++ tailWord_6704174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704174).length < 2 ^ (prefixWord ++ tailWord_6704174).sum := by decide
  have hdescent : baseEnd_6704174 < baseStart_6704174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704224 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_6704224 : Nat := 118140960795 + 6704224 * 2 ^ 59
def prefixEnd_6704224 : Nat := 4983230072969 + 3 ^ 40 * 6704224 * 2
def baseEnd_6704224 : Nat := 3442489327408482926467841

theorem tailTrace_6704224 : CollatzResearch.WordTrace tailWord_6704224 prefixEnd_6704224 3442489327408482926467841 := by
  unfold tailWord_6704224
  simp only [CollatzResearch.WordTrace]
  refine ⟨122261568831874456573487863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163015425109165942097983817 122261568831874456573487863)
  ·
    refine ⟨183392353247811684860231795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122261568831874456573487863 183392353247811684860231795)
    ·
      refine ⟨275088529871717527290347693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183392353247811684860231795 275088529871717527290347693)
      ·
        refine ⟨103158198701894072733880385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275088529871717527290347693 103158198701894072733880385)
        ·
          refine ⟨77368649026420554550410289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103158198701894072733880385 77368649026420554550410289)
          ·
            refine ⟨58026486769815415912807717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77368649026420554550410289 58026486769815415912807717)
            ·
              refine ⟨10879966269340390483651447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58026486769815415912807717 10879966269340390483651447)
              ·
                refine ⟨16319949404010585725477171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879966269340390483651447 16319949404010585725477171)
                ·
                  refine ⟨24479924106015878588215757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16319949404010585725477171 24479924106015878588215757)
                  ·
                    refine ⟨9179971539755954470580909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24479924106015878588215757 9179971539755954470580909)
                    ·
                      refine ⟨3442489327408482926467841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9179971539755954470580909 3442489327408482926467841)
                      ·
                        rfl

theorem cell23_6704224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_6704224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704224 prefixEnd_6704224 := by exact prefixLift 6704224
  have htrace : WordTrace (prefixWord ++ tailWord_6704224) baseStart_6704224 baseEnd_6704224 := by
    simpa [prefixWord, tailWord_6704224, baseEnd_6704224] using wordTrace_append hprefix tailTrace_6704224
  have hstable : (prefixWord ++ tailWord_6704224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704224).length < 2 ^ (prefixWord ++ tailWord_6704224).sum := by decide
  have hdescent : baseEnd_6704224 < baseStart_6704224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3]
def baseStart_6704267 : Nat := 118140960795 + 6704267 * 2 ^ 59
def prefixEnd_6704267 : Nat := 4983230072969 + 3 ^ 40 * 6704267 * 2
def baseEnd_6704267 : Nat := 3442511407076626258230143

theorem tailTrace_6704267 : CollatzResearch.WordTrace tailWord_6704267 prefixEnd_6704267 3442511407076626258230143 := by
  unfold tailWord_6704267
  simp only [CollatzResearch.WordTrace]
  refine ⟨244524706002593131490791055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163016470668395420993860703 244524706002593131490791055)
  ·
    refine ⟨366787059003889697236186583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244524706002593131490791055 366787059003889697236186583)
    ·
      refine ⟨550180588505834545854279875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366787059003889697236186583 550180588505834545854279875)
      ·
        refine ⟨825270882758751818781419813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550180588505834545854279875 825270882758751818781419813)
        ·
          refine ⟨154738290517265966021516215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 825270882758751818781419813 154738290517265966021516215)
          ·
            refine ⟨232107435775898949032274323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154738290517265966021516215 232107435775898949032274323)
            ·
              refine ⟨348161153663848423548411485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232107435775898949032274323 348161153663848423548411485)
              ·
                refine ⟨130560432623943158830654307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348161153663848423548411485 130560432623943158830654307)
                ·
                  refine ⟨195840648935914738245981461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130560432623943158830654307 195840648935914738245981461)
                  ·
                    refine ⟨9180030418871003355280381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195840648935914738245981461 9180030418871003355280381)
                    ·
                      refine ⟨3442511407076626258230143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180030418871003355280381 3442511407076626258230143)
                      ·
                        rfl

theorem cell23_6704267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].length) (baseStart_6704267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704267 prefixEnd_6704267 := by exact prefixLift 6704267
  have htrace : WordTrace (prefixWord ++ tailWord_6704267) baseStart_6704267 baseEnd_6704267 := by
    simpa [prefixWord, tailWord_6704267, baseEnd_6704267] using wordTrace_append hprefix tailTrace_6704267
  have hstable : (prefixWord ++ tailWord_6704267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704267).length < 2 ^ (prefixWord ++ tailWord_6704267).sum := by decide
  have hdescent : baseEnd_6704267 < baseStart_6704267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704274 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6704274 : Nat := 118140960795 + 6704274 * 2 ^ 59
def prefixEnd_6704274 : Nat := 4983230072969 + 3 ^ 40 * 6704274 * 2
def baseEnd_6704274 : Nat := 1147505000480402576947537

theorem tailTrace_6704274 : CollatzResearch.WordTrace tailWord_6704274 prefixEnd_6704274 1147505000480402576947537 := by
  unfold tailWord_6704274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61131240328391942921573969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163016640875711847790863917 61131240328391942921573969)
  ·
    refine ⟨45848430246293957191180477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61131240328391942921573969 45848430246293957191180477)
    ·
      refine ⟨17193161342360233946692679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45848430246293957191180477 17193161342360233946692679)
      ·
        refine ⟨25789742013540350920039019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193161342360233946692679 25789742013540350920039019)
        ·
          refine ⟨38684613020310526380058529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789742013540350920039019 38684613020310526380058529)
          ·
            refine ⟨29013459765232894785043897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38684613020310526380058529 29013459765232894785043897)
            ·
              refine ⟨21760094823924671088782923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29013459765232894785043897 21760094823924671088782923)
              ·
                refine ⟨32640142235887006633174385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760094823924671088782923 32640142235887006633174385)
                ·
                  refine ⟨24480106676915254974880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32640142235887006633174385 24480106676915254974880789)
                  ·
                    refine ⟨1147505000480402576947537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24480106676915254974880789 1147505000480402576947537)
                    ·
                      rfl

theorem cell23_6704274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6704274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704274 prefixEnd_6704274 := by exact prefixLift 6704274
  have htrace : WordTrace (prefixWord ++ tailWord_6704274) baseStart_6704274 baseEnd_6704274 := by
    simpa [prefixWord, tailWord_6704274, baseEnd_6704274] using wordTrace_append hprefix tailTrace_6704274
  have hstable : (prefixWord ++ tailWord_6704274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704274).length < 2 ^ (prefixWord ++ tailWord_6704274).sum := by decide
  have hdescent : baseEnd_6704274 < baseStart_6704274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704277 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6704277 : Nat := 118140960795 + 6704277 * 2 ^ 59
def prefixEnd_6704277 : Nat := 4983230072969 + 3 ^ 40 * 6704277 * 2
def baseEnd_6704277 : Nat := 3442516541883171219105097

theorem tailTrace_6704277 : CollatzResearch.WordTrace tailWord_6704277 prefixEnd_6704277 3442516541883171219105097 := by
  unfold tailWord_6704277
  simp only [CollatzResearch.WordTrace]
  refine ⟨244525070732556903198655085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163016713821704602132436723 244525070732556903198655085)
  ·
    refine ⟨91696901524708838699495657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244525070732556903198655085 91696901524708838699495657)
    ·
      refine ⟨68772676143531629024621743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91696901524708838699495657 68772676143531629024621743)
      ·
        refine ⟨103159014215297443536932615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68772676143531629024621743 103159014215297443536932615)
        ·
          refine ⟨154738521322946165305398923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103159014215297443536932615 154738521322946165305398923)
          ·
            refine ⟨232107781984419247958098385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154738521322946165305398923 232107781984419247958098385)
            ·
              refine ⟨174080836488314435968573789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232107781984419247958098385 174080836488314435968573789)
              ·
                refine ⟨65280313683117913488215171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174080836488314435968573789 65280313683117913488215171)
                ·
                  refine ⟨97920470524676870232322757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65280313683117913488215171 97920470524676870232322757)
                  ·
                    refine ⟨18360088223376913168560517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97920470524676870232322757 18360088223376913168560517)
                    ·
                      refine ⟨3442516541883171219105097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18360088223376913168560517 3442516541883171219105097)
                      ·
                        rfl

theorem cell23_6704277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6704277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704277 prefixEnd_6704277 := by exact prefixLift 6704277
  have htrace : WordTrace (prefixWord ++ tailWord_6704277) baseStart_6704277 baseEnd_6704277 := by
    simpa [prefixWord, tailWord_6704277, baseEnd_6704277] using wordTrace_append hprefix tailTrace_6704277
  have hstable : (prefixWord ++ tailWord_6704277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704277).length < 2 ^ (prefixWord ++ tailWord_6704277).sum := by decide
  have hdescent : baseEnd_6704277 < baseStart_6704277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704301 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_6704301 : Nat := 118140960795 + 6704301 * 2 ^ 59
def prefixEnd_6704301 : Nat := 4983230072969 + 3 ^ 40 * 6704301 * 2
def baseEnd_6704301 : Nat := 3442528865418879125204987

theorem tailTrace_6704301 : CollatzResearch.WordTrace tailWord_6704301 prefixEnd_6704301 3442528865418879125204987 := by
  unfold tailWord_6704301
  simp only [CollatzResearch.WordTrace]
  refine ⟨244525946084469955297528757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163017297389646636865019171 244525946084469955297528757)
  ·
    refine ⟨22924307445419058309143321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244525946084469955297528757 22924307445419058309143321)
    ·
      refine ⟨17193230584064293731857491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22924307445419058309143321 17193230584064293731857491)
      ·
        refine ⟨25789845876096440597786237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193230584064293731857491 25789845876096440597786237)
        ·
          refine ⟨9671192203536165224169839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25789845876096440597786237 9671192203536165224169839)
          ·
            refine ⟨14506788305304247836254759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671192203536165224169839 14506788305304247836254759)
            ·
              refine ⟨21760182457956371754382139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14506788305304247836254759 21760182457956371754382139)
              ·
                refine ⟨32640273686934557631573209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760182457956371754382139 32640273686934557631573209)
                ·
                  refine ⟨24480205265200918223679907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32640273686934557631573209 24480205265200918223679907)
                  ·
                    refine ⟨36720307897801377335519861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24480205265200918223679907 36720307897801377335519861)
                    ·
                      refine ⟨3442528865418879125204987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36720307897801377335519861 3442528865418879125204987)
                      ·
                        rfl

theorem cell23_6704301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_6704301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704301 prefixEnd_6704301 := by exact prefixLift 6704301
  have htrace : WordTrace (prefixWord ++ tailWord_6704301) baseStart_6704301 baseEnd_6704301 := by
    simpa [prefixWord, tailWord_6704301, baseEnd_6704301] using wordTrace_append hprefix tailTrace_6704301
  have hstable : (prefixWord ++ tailWord_6704301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704301).length < 2 ^ (prefixWord ++ tailWord_6704301).sum := by decide
  have hdescent : baseEnd_6704301 < baseStart_6704301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704321 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 7]
def baseStart_6704321 : Nat := 118140960795 + 6704321 * 2 ^ 59
def prefixEnd_6704321 : Nat := 4983230072969 + 3 ^ 40 * 6704321 * 2
def baseEnd_6704321 : Nat := 382504348336885449661655

theorem tailTrace_6704321 : CollatzResearch.WordTrace tailWord_6704321 prefixEnd_6704321 382504348336885449661655 := by
  unfold tailWord_6704321
  simp only [CollatzResearch.WordTrace]
  refine ⟨244526675544397498713256817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163017783696264999142171211 244526675544397498713256817)
  ·
    refine ⟨183395006658298124034942613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244526675544397498713256817 183395006658298124034942613)
    ·
      refine ⟨8596640937107724564137935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183395006658298124034942613 8596640937107724564137935)
      ·
        refine ⟨12894961405661586846206903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8596640937107724564137935 12894961405661586846206903)
        ·
          refine ⟨19342442108492380269310355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894961405661586846206903 19342442108492380269310355)
          ·
            refine ⟨29013663162738570403965533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19342442108492380269310355 29013663162738570403965533)
            ·
              refine ⟨10880123686026963901487075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29013663162738570403965533 10880123686026963901487075)
              ·
                refine ⟨16320185529040445852230613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880123686026963901487075 16320185529040445852230613)
                ·
                  refine ⟨382504348336885449661655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16320185529040445852230613 382504348336885449661655)
                  ·
                    rfl

theorem cell23_6704321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_6704321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704321 prefixEnd_6704321 := by exact prefixLift 6704321
  have htrace : WordTrace (prefixWord ++ tailWord_6704321) baseStart_6704321 baseEnd_6704321 := by
    simpa [prefixWord, tailWord_6704321, baseEnd_6704321] using wordTrace_append hprefix tailTrace_6704321
  have hstable : (prefixWord ++ tailWord_6704321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704321).length < 2 ^ (prefixWord ++ tailWord_6704321).sum := by decide
  have hdescent : baseEnd_6704321 < baseStart_6704321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704326 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6704326 : Nat := 118140960795 + 6704326 * 2 ^ 59
def prefixEnd_6704326 : Nat := 4983230072969 + 3 ^ 40 * 6704326 * 2
def baseEnd_6704326 : Nat := 3442541702435241527392373

theorem tailTrace_6704326 : CollatzResearch.WordTrace tailWord_6704326 prefixEnd_6704326 3442541702435241527392373 := by
  unfold tailWord_6704326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641464309668105767724651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163017905272919589711459221 7641464309668105767724651)
  ·
    refine ⟨11462196464502158651586977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641464309668105767724651 11462196464502158651586977)
    ·
      refine ⟨8596647348376618988690233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11462196464502158651586977 8596647348376618988690233)
      ·
        refine ⟨6447485511282464241517675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596647348376618988690233 6447485511282464241517675)
        ·
          refine ⟨9671228266923696362276513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447485511282464241517675 9671228266923696362276513)
          ·
            refine ⟨7253421200192772271707385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9671228266923696362276513 7253421200192772271707385)
            ·
              refine ⟨5440065900144579203780539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7253421200192772271707385 5440065900144579203780539)
              ·
                refine ⟨8160098850216868805670809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440065900144579203780539 8160098850216868805670809)
                ·
                  refine ⟨6120074137662651604253107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160098850216868805670809 6120074137662651604253107)
                  ·
                    refine ⟨9180111206493977406379661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120074137662651604253107 9180111206493977406379661)
                    ·
                      refine ⟨3442541702435241527392373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180111206493977406379661 3442541702435241527392373)
                      ·
                        rfl

theorem cell23_6704326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6704326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704326 prefixEnd_6704326 := by exact prefixLift 6704326
  have htrace : WordTrace (prefixWord ++ tailWord_6704326) baseStart_6704326 baseEnd_6704326 := by
    simpa [prefixWord, tailWord_6704326, baseEnd_6704326] using wordTrace_append hprefix tailTrace_6704326
  have hstable : (prefixWord ++ tailWord_6704326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704326).length < 2 ^ (prefixWord ++ tailWord_6704326).sum := by decide
  have hdescent : baseEnd_6704326 < baseStart_6704326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704372 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6704372 : Nat := 118140960795 + 6704372 * 2 ^ 59
def prefixEnd_6704372 : Nat := 4983230072969 + 3 ^ 40 * 6704372 * 2
def baseEnd_6704372 : Nat := 382507258060594260824129

theorem tailTrace_6704372 : CollatzResearch.WordTrace tailWord_6704372 prefixEnd_6704372 382507258060594260824129 := by
  unfold tailWord_6704372
  simp only [CollatzResearch.WordTrace]
  refine ⟨122264267833606367211681685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163019023778141822948908913 122264267833606367211681685)
  ·
    refine ⟨5731137554700298463047579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122264267833606367211681685 5731137554700298463047579)
    ·
      refine ⟨8596706332050447694571369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731137554700298463047579 8596706332050447694571369)
      ·
        refine ⟨6447529749037835770928527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596706332050447694571369 6447529749037835770928527)
        ·
          refine ⟨9671294623556753656392791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447529749037835770928527 9671294623556753656392791)
          ·
            refine ⟨14506941935335130484589187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671294623556753656392791 14506941935335130484589187)
            ·
              refine ⟨21760412903002695726883781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14506941935335130484589187 21760412903002695726883781)
              ·
                refine ⟨4080077419313005448790709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21760412903002695726883781 4080077419313005448790709)
                ·
                  refine ⟨382507258060594260824129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080077419313005448790709 382507258060594260824129)
                  ·
                    rfl

theorem cell23_6704372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6704372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704372 prefixEnd_6704372 := by exact prefixLift 6704372
  have htrace : WordTrace (prefixWord ++ tailWord_6704372) baseStart_6704372 baseEnd_6704372 := by
    simpa [prefixWord, tailWord_6704372, baseEnd_6704372] using wordTrace_append hprefix tailTrace_6704372
  have hstable : (prefixWord ++ tailWord_6704372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704372).length < 2 ^ (prefixWord ++ tailWord_6704372).sum := by decide
  have hdescent : baseEnd_6704372 < baseStart_6704372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704374 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6704374 : Nat := 118140960795 + 6704374 * 2 ^ 59
def prefixEnd_6704374 : Nat := 4983230072969 + 3 ^ 40 * 6704374 * 2
def baseEnd_6704374 : Nat := 3442566349506657339592151

theorem tailTrace_6704374 : CollatzResearch.WordTrace tailWord_6704374 prefixEnd_6704374 3442566349506657339592151 := by
  unfold tailWord_6704374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283038038325343047808511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163019072408803659176624117 15283038038325343047808511)
  ·
    refine ⟨22924557057488014571712767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283038038325343047808511 22924557057488014571712767)
    ·
      refine ⟨34386835586232021857569151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22924557057488014571712767 34386835586232021857569151)
      ·
        refine ⟨51580253379348032786353727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34386835586232021857569151 51580253379348032786353727)
        ·
          refine ⟨77370380069022049179530591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51580253379348032786353727 77370380069022049179530591)
          ·
            refine ⟨116055570103533073769295887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77370380069022049179530591 116055570103533073769295887)
            ·
              refine ⟨174083355155299610653943831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116055570103533073769295887 174083355155299610653943831)
              ·
                refine ⟨261125032732949415980915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174083355155299610653943831 261125032732949415980915747)
                ·
                  refine ⟨391687549099424123971373621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261125032732949415980915747 391687549099424123971373621)
                  ·
                    refine ⟨36720707728071011622316277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 391687549099424123971373621 36720707728071011622316277)
                    ·
                      refine ⟨3442566349506657339592151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36720707728071011622316277 3442566349506657339592151)
                      ·
                        rfl

theorem cell23_6704374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6704374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704374 prefixEnd_6704374 := by exact prefixLift 6704374
  have htrace : WordTrace (prefixWord ++ tailWord_6704374) baseStart_6704374 baseEnd_6704374 := by
    simpa [prefixWord, tailWord_6704374, baseEnd_6704374] using wordTrace_append hprefix tailTrace_6704374
  have hstable : (prefixWord ++ tailWord_6704374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704374).length < 2 ^ (prefixWord ++ tailWord_6704374).sum := by decide
  have hdescent : baseEnd_6704374 < baseStart_6704374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704388 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6704388 : Nat := 118140960795 + 6704388 * 2 ^ 59
def prefixEnd_6704388 : Nat := 4983230072969 + 3 ^ 40 * 6704388 * 2
def baseEnd_6704388 : Nat := 3442573538235820284817087

theorem tailTrace_6704388 : CollatzResearch.WordTrace tailWord_6704388 prefixEnd_6704388 3442573538235820284817087 := by
  unfold tailWord_6704388
  simp only [CollatzResearch.WordTrace]
  refine ⟨122264559617577384577972909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163019412823436512770630545 122264559617577384577972909)
  ·
    refine ⟨45849209856591519216739841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122264559617577384577972909 45849209856591519216739841)
    ·
      refine ⟨34386907392443639412554881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45849209856591519216739841 34386907392443639412554881)
      ·
        refine ⟨25790180544332729559416161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34386907392443639412554881 25790180544332729559416161)
        ·
          refine ⟨19342635408249547169562121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25790180544332729559416161 19342635408249547169562121)
          ·
            refine ⟨14506976556187160377171591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19342635408249547169562121 14506976556187160377171591)
            ·
              refine ⟨21760464834280740565757387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14506976556187160377171591 21760464834280740565757387)
              ·
                refine ⟨32640697251421110848636081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760464834280740565757387 32640697251421110848636081)
                ·
                  refine ⟨24480522938565833136477061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32640697251421110848636081 24480522938565833136477061)
                  ·
                    refine ⟨4590098050981093713089449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24480522938565833136477061 4590098050981093713089449)
                    ·
                      refine ⟨3442573538235820284817087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590098050981093713089449 3442573538235820284817087)
                      ·
                        rfl

theorem cell23_6704388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6704388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704388 prefixEnd_6704388 := by exact prefixLift 6704388
  have htrace : WordTrace (prefixWord ++ tailWord_6704388) baseStart_6704388 baseEnd_6704388 := by
    simpa [prefixWord, tailWord_6704388, baseEnd_6704388] using wordTrace_append hprefix tailTrace_6704388
  have hstable : (prefixWord ++ tailWord_6704388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704388).length < 2 ^ (prefixWord ++ tailWord_6704388).sum := by decide
  have hdescent : baseEnd_6704388 < baseStart_6704388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704402 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6704402 : Nat := 118140960795 + 6704402 * 2 ^ 59
def prefixEnd_6704402 : Nat := 4983230072969 + 3 ^ 40 * 6704402 * 2
def baseEnd_6704402 : Nat := 1147526908988327743347341

theorem tailTrace_6704402 : CollatzResearch.WordTrace tailWord_6704402 prefixEnd_6704402 1147526908988327743347341 := by
  unfold tailWord_6704402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61132407464276012386738865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163019753238069366364636973 61132407464276012386738865)
  ·
    refine ⟨45849305598207009290054149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61132407464276012386738865 45849305598207009290054149)
    ·
      refine ⟨8596744799663814241885153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45849305598207009290054149 8596744799663814241885153)
      ·
        refine ⟨6447558599747860681413865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596744799663814241885153 6447558599747860681413865)
        ·
          refine ⟨4835668949810895511060399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6447558599747860681413865 4835668949810895511060399)
          ·
            refine ⟨7253503424716343266590599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835668949810895511060399 7253503424716343266590599)
            ·
              refine ⟨10880255137074514899885899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253503424716343266590599 10880255137074514899885899)
              ·
                refine ⟨16320382705611772349828849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880255137074514899885899 16320382705611772349828849)
                ·
                  refine ⟨12240287029208829262371637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16320382705611772349828849 12240287029208829262371637)
                  ·
                    refine ⟨1147526908988327743347341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12240287029208829262371637 1147526908988327743347341)
                    ·
                      rfl

theorem cell23_6704402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6704402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704402 prefixEnd_6704402 := by exact prefixLift 6704402
  have htrace : WordTrace (prefixWord ++ tailWord_6704402) baseStart_6704402 baseEnd_6704402 := by
    simpa [prefixWord, tailWord_6704402, baseEnd_6704402] using wordTrace_append hprefix tailTrace_6704402
  have hstable : (prefixWord ++ tailWord_6704402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704402).length < 2 ^ (prefixWord ++ tailWord_6704402).sum := by decide
  have hdescent : baseEnd_6704402 < baseStart_6704402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704408 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_6704408 : Nat := 118140960795 + 6704408 * 2 ^ 59
def prefixEnd_6704408 : Nat := 4983230072969 + 3 ^ 40 * 6704408 * 2
def baseEnd_6704408 : Nat := 3442583807848910206566995

theorem tailTrace_6704408 : CollatzResearch.WordTrace tailWord_6704408 prefixEnd_6704408 3442583807848910206566995 := by
  unfold tailWord_6704408
  simp only [CollatzResearch.WordTrace]
  refine ⟨122264924347541156285836939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163019899130054875047782585 122264924347541156285836939)
  ·
    refine ⟨183397386521311734428755409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122264924347541156285836939 183397386521311734428755409)
    ·
      refine ⟨137548039890983800821566557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183397386521311734428755409 137548039890983800821566557)
      ·
        refine ⟨51580514959118925308087459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137548039890983800821566557 51580514959118925308087459)
        ·
          refine ⟨77370772438678387962131189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51580514959118925308087459 77370772438678387962131189)
          ·
            refine ⟨7253509916126098871449799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77370772438678387962131189 7253509916126098871449799)
            ·
              refine ⟨10880264874189148307174699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253509916126098871449799 10880264874189148307174699)
              ·
                refine ⟨16320397311283722460762049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880264874189148307174699 16320397311283722460762049)
                ·
                  refine ⟨12240297983462791845571537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16320397311283722460762049 12240297983462791845571537)
                  ·
                    refine ⟨9180223487597093884178653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12240297983462791845571537 9180223487597093884178653)
                    ·
                      refine ⟨3442583807848910206566995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180223487597093884178653 3442583807848910206566995)
                      ·
                        rfl

theorem cell23_6704408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_6704408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704408 prefixEnd_6704408 := by exact prefixLift 6704408
  have htrace : WordTrace (prefixWord ++ tailWord_6704408) baseStart_6704408 baseEnd_6704408 := by
    simpa [prefixWord, tailWord_6704408, baseEnd_6704408] using wordTrace_append hprefix tailTrace_6704408
  have hstable : (prefixWord ++ tailWord_6704408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704408).length < 2 ^ (prefixWord ++ tailWord_6704408).sum := by decide
  have hdescent : baseEnd_6704408 < baseStart_6704408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704415 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 1, 4]
def baseStart_6704415 : Nat := 118140960795 + 6704415 * 2 ^ 59
def prefixEnd_6704415 : Nat := 4983230072969 + 3 ^ 40 * 6704415 * 2
def baseEnd_6704415 : Nat := 1147529134071163893059821

theorem tailTrace_6704415 : CollatzResearch.WordTrace tailWord_6704415 prefixEnd_6704415 1147529134071163893059821 := by
  unfold tailWord_6704415
  simp only [CollatzResearch.WordTrace]
  refine ⟨244530104006056952767178699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163020069337371301844785799 244530104006056952767178699)
  ·
    refine ⟨366795156009085429150768049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244530104006056952767178699 366795156009085429150768049)
    ·
      refine ⟨275096367006814071863076037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366795156009085429150768049 275096367006814071863076037)
      ·
        refine ⟨51580568813777638474326757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275096367006814071863076037 51580568813777638474326757)
        ·
          refine ⟨9671356652583307213936267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51580568813777638474326757 9671356652583307213936267)
          ·
            refine ⟨14507034978874960820904401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671356652583307213936267 14507034978874960820904401)
            ·
              refine ⟨10880276234156220615678301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14507034978874960820904401 10880276234156220615678301)
              ·
                refine ⟨4080103587808582730879363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10880276234156220615678301 4080103587808582730879363)
                ·
                  refine ⟨6120155381712874096319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080103587808582730879363 6120155381712874096319045)
                  ·
                    refine ⟨1147529134071163893059821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120155381712874096319045 1147529134071163893059821)
                    ·
                      rfl

theorem cell23_6704415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_6704415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704415 prefixEnd_6704415 := by exact prefixLift 6704415
  have htrace : WordTrace (prefixWord ++ tailWord_6704415) baseStart_6704415 baseEnd_6704415 := by
    simpa [prefixWord, tailWord_6704415, baseEnd_6704415] using wordTrace_append hprefix tailTrace_6704415
  have hstable : (prefixWord ++ tailWord_6704415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704415).length < 2 ^ (prefixWord ++ tailWord_6704415).sum := by decide
  have hdescent : baseEnd_6704415 < baseStart_6704415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704431 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 4, 3, 2]
def baseStart_6704431 : Nat := 118140960795 + 6704431 * 2 ^ 59
def prefixEnd_6704431 : Nat := 4983230072969 + 3 ^ 40 * 6704431 * 2
def baseEnd_6704431 : Nat := 3442595617903963616579389

theorem tailTrace_6704431 : CollatzResearch.WordTrace tailWord_6704431 prefixEnd_6704431 3442595617903963616579389 := by
  unfold tailWord_6704431
  simp only [CollatzResearch.WordTrace]
  refine ⟨244530687573998987499761147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163020458382665991666507431 244530687573998987499761147)
  ·
    refine ⟨366796031360998481249641721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244530687573998987499761147 366796031360998481249641721)
    ·
      refine ⟨275097023520748860937231291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366796031360998481249641721 275097023520748860937231291)
      ·
        refine ⟨412645535281123291405846937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275097023520748860937231291 412645535281123291405846937)
        ·
          refine ⟨309484151460842468554385203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412645535281123291405846937 309484151460842468554385203)
          ·
            refine ⟨464226227191263702831577805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309484151460842468554385203 464226227191263702831577805)
            ·
              refine ⟨174084835196723888561841677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464226227191263702831577805 174084835196723888561841677)
              ·
                refine ⟨65281813198771458210690629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174084835196723888561841677 65281813198771458210690629)
                ·
                  refine ⟨12240339974769648414504493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65281813198771458210690629 12240339974769648414504493)
                  ·
                    refine ⟨4590127490538618155439185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12240339974769648414504493 4590127490538618155439185)
                    ·
                      refine ⟨3442595617903963616579389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590127490538618155439185 3442595617903963616579389)
                      ·
                        rfl

theorem cell23_6704431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3, 2].length) (baseStart_6704431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704431 prefixEnd_6704431 := by exact prefixLift 6704431
  have htrace : WordTrace (prefixWord ++ tailWord_6704431) baseStart_6704431 baseEnd_6704431 := by
    simpa [prefixWord, tailWord_6704431, baseEnd_6704431] using wordTrace_append hprefix tailTrace_6704431
  have hstable : (prefixWord ++ tailWord_6704431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704431).length < 2 ^ (prefixWord ++ tailWord_6704431).sum := by decide
  have hdescent : baseEnd_6704431 < baseStart_6704431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704445 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 6]
def baseStart_6704445 : Nat := 118140960795 + 6704445 * 2 ^ 59
def prefixEnd_6704445 : Nat := 4983230072969 + 3 ^ 40 * 6704445 * 2
def baseEnd_6704445 : Nat := 382511422959236284644925

theorem tailTrace_6704445 : CollatzResearch.WordTrace tailWord_6704445 prefixEnd_6704445 382511422959236284644925 := by
  unfold tailWord_6704445
  simp only [CollatzResearch.WordTrace]
  refine ⟨244531198195948267890770789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163020798797298845260513859 244531198195948267890770789)
  ·
    refine ⟨45849599661740300229519523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244531198195948267890770789 45849599661740300229519523)
    ·
      refine ⟨68774399492610450344279285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45849599661740300229519523 68774399492610450344279285)
      ·
        refine ⟨6447599952432229719776183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68774399492610450344279285 6447599952432229719776183)
        ·
          refine ⟨9671399928648344579664275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447599952432229719776183 9671399928648344579664275)
          ·
            refine ⟨14507099892972516869496413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671399928648344579664275 14507099892972516869496413)
            ·
              refine ⟨5440162459864693826061155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14507099892972516869496413 5440162459864693826061155)
              ·
                refine ⟨8160243689797040739091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440162459864693826061155 8160243689797040739091733)
                ·
                  refine ⟨382511422959236284644925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8160243689797040739091733 382511422959236284644925)
                  ·
                    rfl

theorem cell23_6704445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_6704445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704445 prefixEnd_6704445 := by exact prefixLift 6704445
  have htrace : WordTrace (prefixWord ++ tailWord_6704445) baseStart_6704445 baseEnd_6704445 := by
    simpa [prefixWord, tailWord_6704445, baseEnd_6704445] using wordTrace_append hprefix tailTrace_6704445
  have hstable : (prefixWord ++ tailWord_6704445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704445).length < 2 ^ (prefixWord ++ tailWord_6704445).sum := by decide
  have hdescent : baseEnd_6704445 < baseStart_6704445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704464 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_6704464 : Nat := 118140960795 + 6704464 * 2 ^ 59
def prefixEnd_6704464 : Nat := 4983230072969 + 3 ^ 40 * 6704464 * 2
def baseEnd_6704464 : Nat := 3442612562765561987466737

theorem tailTrace_6704464 : CollatzResearch.WordTrace tailWord_6704464 prefixEnd_6704464 3442612562765561987466737 := by
  unfold tailWord_6704464
  simp only [CollatzResearch.WordTrace]
  refine ⟨122265945591439717067856223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163021260788586289423808297 122265945591439717067856223)
  ·
    refine ⟨183398918387159575601784335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122265945591439717067856223 183398918387159575601784335)
    ·
      refine ⟨275098377580739363402676503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183398918387159575601784335 275098377580739363402676503)
      ·
        refine ⟨412647566371109045104014755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275098377580739363402676503 412647566371109045104014755)
        ·
          refine ⟨618971349556663567656022133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412647566371109045104014755 618971349556663567656022133)
          ·
            refine ⟨58028564020937209467752075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 618971349556663567656022133 58028564020937209467752075)
            ·
              refine ⟨87042846031405814201628113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58028564020937209467752075 87042846031405814201628113)
              ·
                refine ⟨65282134523554360651221085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87042846031405814201628113 65282134523554360651221085)
                ·
                  refine ⟨24480800446332885244207907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65282134523554360651221085 24480800446332885244207907)
                  ·
                    refine ⟨36721200669499327866311861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24480800446332885244207907 36721200669499327866311861)
                    ·
                      refine ⟨3442612562765561987466737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36721200669499327866311861 3442612562765561987466737)
                      ·
                        rfl

theorem cell23_6704464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_6704464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704464 prefixEnd_6704464 := by exact prefixLift 6704464
  have htrace : WordTrace (prefixWord ++ tailWord_6704464) baseStart_6704464 baseEnd_6704464 := by
    simpa [prefixWord, tailWord_6704464, baseEnd_6704464] using wordTrace_append hprefix tailTrace_6704464
  have hstable : (prefixWord ++ tailWord_6704464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704464).length < 2 ^ (prefixWord ++ tailWord_6704464).sum := by decide
  have hdescent : baseEnd_6704464 < baseStart_6704464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704471 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 4, 4]
def baseStart_6704471 : Nat := 118140960795 + 6704471 * 2 ^ 59
def prefixEnd_6704471 : Nat := 4983230072969 + 3 ^ 40 * 6704471 * 2
def baseEnd_6704471 : Nat := 1147538719043381153359735

theorem tailTrace_6704471 : CollatzResearch.WordTrace tailWord_6704471 prefixEnd_6704471 1147538719043381153359735 := by
  unfold tailWord_6704471
  simp only [CollatzResearch.WordTrace]
  refine ⟨244532146493854074331217267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163021430995902716220811511 244532146493854074331217267)
  ·
    refine ⟨366798219740781111496825901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244532146493854074331217267 366798219740781111496825901)
    ·
      refine ⟨137549332402792916811309713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366798219740781111496825901 137549332402792916811309713)
      ·
        refine ⟨103161999302094687608482285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137549332402792916811309713 103161999302094687608482285)
        ·
          refine ⟨38685749738285507853180857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103161999302094687608482285 38685749738285507853180857)
          ·
            refine ⟨29014312303714130889885643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38685749738285507853180857 29014312303714130889885643)
            ·
              refine ⟨43521468455571196334828465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29014312303714130889885643 43521468455571196334828465)
              ·
                refine ⟨32641101341678397251121349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43521468455571196334828465 32641101341678397251121349)
                ·
                  refine ⟨6120206501564699484585253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32641101341678397251121349 6120206501564699484585253)
                  ·
                    refine ⟨1147538719043381153359735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120206501564699484585253 1147538719043381153359735)
                    ·
                      rfl

theorem cell23_6704471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_6704471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704471 prefixEnd_6704471 := by exact prefixLift 6704471
  have htrace : WordTrace (prefixWord ++ tailWord_6704471) baseStart_6704471 baseEnd_6704471 := by
    simpa [prefixWord, tailWord_6704471, baseEnd_6704471] using wordTrace_append hprefix tailTrace_6704471
  have hstable : (prefixWord ++ tailWord_6704471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704471).length < 2 ^ (prefixWord ++ tailWord_6704471).sum := by decide
  have hdescent : baseEnd_6704471 < baseStart_6704471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704484 : List Nat := [2, 3, 1, 1, 3, 2, 11]
def baseStart_6704484 : Nat := 118140960795 + 6704484 * 2 ^ 59
def prefixEnd_6704484 : Nat := 4983230072969 + 3 ^ 40 * 6704484 * 2
def baseEnd_6704484 : Nat := 42501516449119159373045

theorem tailTrace_6704484 : CollatzResearch.WordTrace tailWord_6704484 prefixEnd_6704484 42501516449119159373045 := by
  unfold tailWord_6704484
  simp only [CollatzResearch.WordTrace]
  refine ⟨122266310321403488775720253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163021747095204651700960337 122266310321403488775720253)
  ·
    refine ⟨45849866370526308290895095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122266310321403488775720253 45849866370526308290895095)
    ·
      refine ⟨68774799555789462436342643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45849866370526308290895095 68774799555789462436342643)
      ·
        refine ⟨103162199333684193654513965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68774799555789462436342643 103162199333684193654513965)
        ·
          refine ⟨38685824750131572620442737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103162199333684193654513965 38685824750131572620442737)
          ·
            refine ⟨29014368562598679465332053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38685824750131572620442737 29014368562598679465332053)
            ·
              refine ⟨42501516449119159373045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29014368562598679465332053 42501516449119159373045)
              ·
                rfl

theorem cell23_6704484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 11].length) (baseStart_6704484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704484 prefixEnd_6704484 := by exact prefixLift 6704484
  have htrace : WordTrace (prefixWord ++ tailWord_6704484) baseStart_6704484 baseEnd_6704484 := by
    simpa [prefixWord, tailWord_6704484, baseEnd_6704484] using wordTrace_append hprefix tailTrace_6704484
  have hstable : (prefixWord ++ tailWord_6704484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704484).length < 2 ^ (prefixWord ++ tailWord_6704484).sum := by decide
  have hdescent : baseEnd_6704484 < baseStart_6704484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704515 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 3]
def baseStart_6704515 : Nat := 118140960795 + 6704515 * 2 ^ 59
def prefixEnd_6704515 : Nat := 4983230072969 + 3 ^ 40 * 6704515 * 2
def baseEnd_6704515 : Nat := 3442638750278941287929003

theorem tailTrace_6704515 : CollatzResearch.WordTrace tailWord_6704515 prefixEnd_6704515 3442638750278941287929003 := by
  unfold tailWord_6704515
  simp only [CollatzResearch.WordTrace]
  refine ⟨244533751305694669845818999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163022500870463113230545999 244533751305694669845818999)
  ·
    refine ⟨366800626958542004768728499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244533751305694669845818999 366800626958542004768728499)
    ·
      refine ⟨550200940437813007153092749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366800626958542004768728499 550200940437813007153092749)
      ·
        refine ⟨206325352664179877682409781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550200940437813007153092749 206325352664179877682409781)
        ·
          refine ⟨19343001812266863532725917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206325352664179877682409781 19343001812266863532725917)
          ·
            refine ⟨7253625679600073824772219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19343001812266863532725917 7253625679600073824772219)
            ·
              refine ⟨10880438519400110737158329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253625679600073824772219 10880438519400110737158329)
              ·
                refine ⟨8160328889550083052868747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10880438519400110737158329 8160328889550083052868747)
                ·
                  refine ⟨12240493334325124579303121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8160328889550083052868747 12240493334325124579303121)
                  ·
                    refine ⟨9180370000743843434477341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12240493334325124579303121 9180370000743843434477341)
                    ·
                      refine ⟨3442638750278941287929003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180370000743843434477341 3442638750278941287929003)
                      ·
                        rfl

theorem cell23_6704515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_6704515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704515 prefixEnd_6704515 := by exact prefixLift 6704515
  have htrace : WordTrace (prefixWord ++ tailWord_6704515) baseStart_6704515 baseEnd_6704515 := by
    simpa [prefixWord, tailWord_6704515, baseEnd_6704515] using wordTrace_append hprefix tailTrace_6704515
  have hstable : (prefixWord ++ tailWord_6704515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704515).length < 2 ^ (prefixWord ++ tailWord_6704515).sum := by decide
  have hdescent : baseEnd_6704515 < baseStart_6704515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704532 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6704532 : Nat := 118140960795 + 6704532 * 2 ^ 59
def prefixEnd_6704532 : Nat := 4983230072969 + 3 ^ 40 * 6704532 * 2
def baseEnd_6704532 : Nat := 3442647479450067721416425

theorem tailTrace_6704532 : CollatzResearch.WordTrace tailWord_6704532 prefixEnd_6704532 3442647479450067721416425 := by
  unfold tailWord_6704532
  simp only [CollatzResearch.WordTrace]
  refine ⟨122267185673316540874593925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163022914231088721166125233 122267185673316540874593925)
  ·
    refine ⟨22925097313746851413986361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122267185673316540874593925 22925097313746851413986361)
    ·
      refine ⟨17193822985310138560489771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22925097313746851413986361 17193822985310138560489771)
      ·
        refine ⟨25790734477965207840734657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193822985310138560489771 25790734477965207840734657)
        ·
          refine ⟨19343050858473905880550993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25790734477965207840734657 19343050858473905880550993)
          ·
            refine ⟨14507288143855429410413245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19343050858473905880550993 14507288143855429410413245)
            ·
              refine ⟨5440233053945786028904967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14507288143855429410413245 5440233053945786028904967)
              ·
                refine ⟨8160349580918679043357451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440233053945786028904967 8160349580918679043357451)
                ·
                  refine ⟨12240524371378018565036177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8160349580918679043357451 12240524371378018565036177)
                  ·
                    refine ⟨9180393278533513923777133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12240524371378018565036177 9180393278533513923777133)
                    ·
                      refine ⟨3442647479450067721416425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180393278533513923777133 3442647479450067721416425)
                      ·
                        rfl

theorem cell23_6704532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6704532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704532 prefixEnd_6704532 := by exact prefixLift 6704532
  have htrace : WordTrace (prefixWord ++ tailWord_6704532) baseStart_6704532 baseEnd_6704532 := by
    simpa [prefixWord, tailWord_6704532, baseEnd_6704532] using wordTrace_append hprefix tailTrace_6704532
  have hstable : (prefixWord ++ tailWord_6704532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704532).length < 2 ^ (prefixWord ++ tailWord_6704532).sum := by decide
  have hdescent : baseEnd_6704532 < baseStart_6704532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704546 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6704546 : Nat := 118140960795 + 6704546 * 2 ^ 59
def prefixEnd_6704546 : Nat := 4983230072969 + 3 ^ 40 * 6704546 * 2
def baseEnd_6704546 : Nat := 3442654668179230666641361

theorem tailTrace_6704546 : CollatzResearch.WordTrace tailWord_6704546 prefixEnd_6704546 3442654668179230666641361 := by
  unfold tailWord_6704546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61133720492145590535049373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163023254645721574760131661 61133720492145590535049373)
  ·
    refine ⟨22925145184554596450643515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61133720492145590535049373 22925145184554596450643515)
    ·
      refine ⟨34387717776831894675965273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22925145184554596450643515 34387717776831894675965273)
      ·
        refine ⟨25790788332623921006973955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34387717776831894675965273 25790788332623921006973955)
        ·
          refine ⟨38686182498935881510460933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25790788332623921006973955 38686182498935881510460933)
          ·
            refine ⟨7253659218550477783211425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38686182498935881510460933 7253659218550477783211425)
            ·
              refine ⟨5440244413912858337408569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7253659218550477783211425 5440244413912858337408569)
              ·
                refine ⟨4080183310434643753056427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5440244413912858337408569 4080183310434643753056427)
                ·
                  refine ⟨6120274965651965629584641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080183310434643753056427 6120274965651965629584641)
                  ·
                    refine ⟨4590206224238974222188481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120274965651965629584641 4590206224238974222188481)
                    ·
                      refine ⟨3442654668179230666641361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590206224238974222188481 3442654668179230666641361)
                      ·
                        rfl

theorem cell23_6704546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6704546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704546 prefixEnd_6704546 := by exact prefixLift 6704546
  have htrace : WordTrace (prefixWord ++ tailWord_6704546) baseStart_6704546 baseEnd_6704546 := by
    simpa [prefixWord, tailWord_6704546, baseEnd_6704546] using wordTrace_append hprefix tailTrace_6704546
  have hstable : (prefixWord ++ tailWord_6704546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704546).length < 2 ^ (prefixWord ++ tailWord_6704546).sum := by decide
  have hdescent : baseEnd_6704546 < baseStart_6704546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704551 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6704551 : Nat := 118140960795 + 6704551 * 2 ^ 59
def prefixEnd_6704551 : Nat := 4983230072969 + 3 ^ 40 * 6704551 * 2
def baseEnd_6704551 : Nat := 3442657235582503147078837

theorem tailTrace_6704551 : CollatzResearch.WordTrace tailWord_6704551 prefixEnd_6704551 3442657235582503147078837 := by
  unfold tailWord_6704551
  simp only [CollatzResearch.WordTrace]
  refine ⟨244535064333564247994129507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163023376222376165329419671 244535064333564247994129507)
  ·
    refine ⟨366802596500346371991194261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244535064333564247994129507 366802596500346371991194261)
    ·
      refine ⟨17193871710953736187087231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366802596500346371991194261 17193871710953736187087231)
      ·
        refine ⟨25790807566430604280630847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193871710953736187087231 25790807566430604280630847)
        ·
          refine ⟨38686211349645906420946271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25790807566430604280630847 38686211349645906420946271)
          ·
            refine ⟨58029317024468859631419407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38686211349645906420946271 58029317024468859631419407)
            ·
              refine ⟨87043975536703289447129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58029317024468859631419407 87043975536703289447129111)
              ·
                refine ⟨130565963305054934170693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87043975536703289447129111 130565963305054934170693667)
                ·
                  refine ⟨195848944957582401256040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130565963305054934170693667 195848944957582401256040501)
                  ·
                    refine ⟨18360838589773350117753797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195848944957582401256040501 18360838589773350117753797)
                    ·
                      refine ⟨3442657235582503147078837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18360838589773350117753797 3442657235582503147078837)
                      ·
                        rfl

theorem cell23_6704551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6704551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704551 prefixEnd_6704551 := by exact prefixLift 6704551
  have htrace : WordTrace (prefixWord ++ tailWord_6704551) baseStart_6704551 baseEnd_6704551 := by
    simpa [prefixWord, tailWord_6704551, baseEnd_6704551] using wordTrace_append hprefix tailTrace_6704551
  have hstable : (prefixWord ++ tailWord_6704551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704551).length < 2 ^ (prefixWord ++ tailWord_6704551).sum := by decide
  have hdescent : baseEnd_6704551 < baseStart_6704551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704561 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_6704561 : Nat := 118140960795 + 6704561 * 2 ^ 59
def prefixEnd_6704561 : Nat := 4983230072969 + 3 ^ 40 * 6704561 * 2
def baseEnd_6704561 : Nat := 1147554123463016035984597

theorem tailTrace_6704561 : CollatzResearch.WordTrace tailWord_6704561 prefixEnd_6704561 1147554123463016035984597 := by
  unfold tailWord_6704561
  simp only [CollatzResearch.WordTrace]
  refine ⟨244535429063528019701993537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163023619375685346467995691 244535429063528019701993537)
  ·
    refine ⟨183401571797646014776495153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244535429063528019701993537 183401571797646014776495153)
    ·
      refine ⟨137551178848234511082371365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183401571797646014776495153 137551178848234511082371365)
      ·
        refine ⟨25790846034043970827944631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137551178848234511082371365 25790846034043970827944631)
        ·
          refine ⟨38686269051065956241916947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25790846034043970827944631 38686269051065956241916947)
          ·
            refine ⟨58029403576598934362875421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38686269051065956241916947 58029403576598934362875421)
            ·
              refine ⟨21761026341224600386078283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58029403576598934362875421 21761026341224600386078283)
              ·
                refine ⟨32641539511836900579117425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21761026341224600386078283 32641539511836900579117425)
                ·
                  refine ⟨24481154633877675434338069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32641539511836900579117425 24481154633877675434338069)
                  ·
                    refine ⟨1147554123463016035984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24481154633877675434338069 1147554123463016035984597)
                    ·
                      rfl

theorem cell23_6704561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_6704561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704561 prefixEnd_6704561 := by exact prefixLift 6704561
  have htrace : WordTrace (prefixWord ++ tailWord_6704561) baseStart_6704561 baseEnd_6704561 := by
    simpa [prefixWord, tailWord_6704561, baseEnd_6704561] using wordTrace_append hprefix tailTrace_6704561
  have hstable : (prefixWord ++ tailWord_6704561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704561).length < 2 ^ (prefixWord ++ tailWord_6704561).sum := by decide
  have hdescent : baseEnd_6704561 < baseStart_6704561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704568 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_6704568 : Nat := 118140960795 + 6704568 * 2 ^ 59
def prefixEnd_6704568 : Nat := 4983230072969 + 3 ^ 40 * 6704568 * 2
def baseEnd_6704568 : Nat := 3442665964753629580566259

theorem tailTrace_6704568 : CollatzResearch.WordTrace tailWord_6704568 prefixEnd_6704568 3442665964753629580566259 := by
  unfold tailWord_6704568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122267842187251329948749179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163023789583001773264998905 122267842187251329948749179)
  ·
    refine ⟨183401763280876994923123769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122267842187251329948749179 183401763280876994923123769)
    ·
      refine ⟨137551322460657746192342827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183401763280876994923123769 137551322460657746192342827)
      ·
        refine ⟨206326983690986619288514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137551322460657746192342827 206326983690986619288514241)
        ·
          refine ⟨154745237768239964466385681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206326983690986619288514241 154745237768239964466385681)
          ·
            refine ⟨116058928326179973349789261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154745237768239964466385681 116058928326179973349789261)
            ·
              refine ⟨43522098122317490006170973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116058928326179973349789261 43522098122317490006170973)
              ·
                refine ⟨16320786795869058752314115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43522098122317490006170973 16320786795869058752314115)
                ·
                  refine ⟨24481180193803588128471173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16320786795869058752314115 24481180193803588128471173)
                  ·
                    refine ⟨4590221286338172774088345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24481180193803588128471173 4590221286338172774088345)
                    ·
                      refine ⟨3442665964753629580566259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590221286338172774088345 3442665964753629580566259)
                      ·
                        rfl

theorem cell23_6704568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_6704568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704568 prefixEnd_6704568 := by exact prefixLift 6704568
  have htrace : WordTrace (prefixWord ++ tailWord_6704568) baseStart_6704568 baseEnd_6704568 := by
    simpa [prefixWord, tailWord_6704568, baseEnd_6704568] using wordTrace_append hprefix tailTrace_6704568
  have hstable : (prefixWord ++ tailWord_6704568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704568).length < 2 ^ (prefixWord ++ tailWord_6704568).sum := by decide
  have hdescent : baseEnd_6704568 < baseStart_6704568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704602 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_6704602 : Nat := 118140960795 + 6704602 * 2 ^ 59
def prefixEnd_6704602 : Nat := 4983230072969 + 3 ^ 40 * 6704602 * 2
def baseEnd_6704602 : Nat := 3442683423095882447541103

theorem tailTrace_6704602 : CollatzResearch.WordTrace tailWord_6704602 prefixEnd_6704602 3442683423095882447541103 := by
  unfold tailWord_6704602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61134231114094870926059015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163024616304252989136157373 61134231114094870926059015)
  ·
    refine ⟨91701346671142306389088523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61134231114094870926059015 91701346671142306389088523)
    ·
      refine ⟨137552020006713459583632785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91701346671142306389088523 137552020006713459583632785)
      ·
        refine ⟨103164015005035094687724589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137552020006713459583632785 103164015005035094687724589)
        ·
          refine ⟨38686505626888160507896721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103164015005035094687724589 38686505626888160507896721)
          ·
            refine ⟨29014879220166120380922541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38686505626888160507896721 29014879220166120380922541)
            ·
              refine ⟨10880579707562295142845953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29014879220166120380922541 10880579707562295142845953)
              ·
                refine ⟨8160434780671721357134465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10880579707562295142845953 8160434780671721357134465)
                ·
                  refine ⟨6120326085503791017850849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160434780671721357134465 6120326085503791017850849)
                  ·
                    refine ⟨4590244564127843263388137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120326085503791017850849 4590244564127843263388137)
                    ·
                      refine ⟨3442683423095882447541103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4590244564127843263388137 3442683423095882447541103)
                      ·
                        rfl

theorem cell23_6704602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_6704602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704602 prefixEnd_6704602 := by exact prefixLift 6704602
  have htrace : WordTrace (prefixWord ++ tailWord_6704602) baseStart_6704602 baseEnd_6704602 := by
    simpa [prefixWord, tailWord_6704602, baseEnd_6704602] using wordTrace_append hprefix tailTrace_6704602
  have hstable : (prefixWord ++ tailWord_6704602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704602).length < 2 ^ (prefixWord ++ tailWord_6704602).sum := by decide
  have hdescent : baseEnd_6704602 < baseStart_6704602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704642 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_6704642 : Nat := 118140960795 + 6704642 * 2 ^ 59
def prefixEnd_6704642 : Nat := 4983230072969 + 3 ^ 40 * 6704642 * 2
def baseEnd_6704642 : Nat := 382522662480229143448991

theorem tailTrace_6704642 : CollatzResearch.WordTrace tailWord_6704642 prefixEnd_6704642 382522662480229143448991 := by
  unfold tailWord_6704642
  simp only [CollatzResearch.WordTrace]
  refine ⟨61134595844058642633923045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163025588917489713690461453 61134595844058642633923045)
  ·
    refine ⟨11462736720760995493860571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61134595844058642633923045 11462736720760995493860571)
    ·
      refine ⟨17194105081141493240790857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462736720760995493860571 17194105081141493240790857)
      ·
        refine ⟨12895578810856119930593143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17194105081141493240790857 12895578810856119930593143)
        ·
          refine ⟨19343368216284179895889715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12895578810856119930593143 19343368216284179895889715)
          ·
            refine ⟨29015052324426269843834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19343368216284179895889715 29015052324426269843834573)
            ·
              refine ⟨10880644621659851191437965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29015052324426269843834573 10880644621659851191437965)
              ·
                refine ⟨4080241733122444196789237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10880644621659851191437965 4080241733122444196789237)
                ·
                  refine ⟨382522662480229143448991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080241733122444196789237 382522662480229143448991)
                  ·
                    rfl

theorem cell23_6704642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_6704642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704642 prefixEnd_6704642 := by exact prefixLift 6704642
  have htrace : WordTrace (prefixWord ++ tailWord_6704642) baseStart_6704642 baseEnd_6704642 := by
    simpa [prefixWord, tailWord_6704642, baseEnd_6704642] using wordTrace_append hprefix tailTrace_6704642
  have hstable : (prefixWord ++ tailWord_6704642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704642).length < 2 ^ (prefixWord ++ tailWord_6704642).sum := by decide
  have hdescent : baseEnd_6704642 < baseStart_6704642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704671 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_6704671 : Nat := 118140960795 + 6704671 * 2 ^ 59
def prefixEnd_6704671 : Nat := 4983230072969 + 3 ^ 40 * 6704671 * 2
def baseEnd_6704671 : Nat := 3442718853261042677578285

theorem tailTrace_6704671 : CollatzResearch.WordTrace tailWord_6704671 prefixEnd_6704671 3442718853261042677578285 := by
  unfold tailWord_6704671
  simp only [CollatzResearch.WordTrace]
  refine ⟨244539441093129508488497867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163026294062086338992331911 244539441093129508488497867)
  ·
    refine ⟨366809161639694262732746801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244539441093129508488497867 366809161639694262732746801)
    ·
      refine ⟨275106871229770697049560101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366809161639694262732746801 275106871229770697049560101)
      ·
        refine ⟨51582538355582005696792519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275106871229770697049560101 51582538355582005696792519)
        ·
          refine ⟨77373807533373008545188779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51582538355582005696792519 77373807533373008545188779)
          ·
            refine ⟨116060711300059512817783169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77373807533373008545188779 116060711300059512817783169)
            ·
              refine ⟨87045533475044634613337377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116060711300059512817783169 87045533475044634613337377)
              ·
                refine ⟨65284150106283475960003033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87045533475044634613337377 65284150106283475960003033)
                ·
                  refine ⟨48963112579712606970002275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65284150106283475960003033 48963112579712606970002275)
                  ·
                    refine ⟨73444668869568910455003413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48963112579712606970002275 73444668869568910455003413)
                    ·
                      refine ⟨3442718853261042677578285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73444668869568910455003413 3442718853261042677578285)
                      ·
                        rfl

theorem cell23_6704671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_6704671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704671 prefixEnd_6704671 := by exact prefixLift 6704671
  have htrace : WordTrace (prefixWord ++ tailWord_6704671) baseStart_6704671 baseEnd_6704671 := by
    simpa [prefixWord, tailWord_6704671, baseEnd_6704671] using wordTrace_append hprefix tailTrace_6704671
  have hstable : (prefixWord ++ tailWord_6704671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704671).length < 2 ^ (prefixWord ++ tailWord_6704671).sum := by decide
  have hdescent : baseEnd_6704671 < baseStart_6704671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704695 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_6704695 : Nat := 118140960795 + 6704695 * 2 ^ 59
def prefixEnd_6704695 : Nat := 4983230072969 + 3 ^ 40 * 6704695 * 2
def baseEnd_6704695 : Nat := 3442731176796750583678175

theorem tailTrace_6704695 : CollatzResearch.WordTrace tailWord_6704695 prefixEnd_6704695 3442731176796750583678175 := by
  unfold tailWord_6704695
  simp only [CollatzResearch.WordTrace]
  refine ⟨244540316445042560587371539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163026877630028373724914359 244540316445042560587371539)
  ·
    refine ⟨366810474667563840881057309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244540316445042560587371539 366810474667563840881057309)
    ·
      refine ⟨137553928000336440330396491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366810474667563840881057309 137553928000336440330396491)
      ·
        refine ⟨206330892000504660495594737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137553928000336440330396491 206330892000504660495594737)
        ·
          refine ⟨154748169000378495371696053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206330892000504660495594737 154748169000378495371696053)
          ·
            refine ⟨14507640843785483941096505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154748169000378495371696053 14507640843785483941096505)
            ·
              refine ⟨10880730632839112955822379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14507640843785483941096505 10880730632839112955822379)
              ·
                refine ⟨16321095949258669433733569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880730632839112955822379 16321095949258669433733569)
                ·
                  refine ⟨12240821961944002075300177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16321095949258669433733569 12240821961944002075300177)
                  ·
                    refine ⟨9180616471458001556475133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12240821961944002075300177 9180616471458001556475133)
                    ·
                      refine ⟨3442731176796750583678175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180616471458001556475133 3442731176796750583678175)
                      ·
                        rfl

theorem cell23_6704695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_6704695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704695 prefixEnd_6704695 := by exact prefixLift 6704695
  have htrace : WordTrace (prefixWord ++ tailWord_6704695) baseStart_6704695 baseEnd_6704695 := by
    simpa [prefixWord, tailWord_6704695, baseEnd_6704695] using wordTrace_append hprefix tailTrace_6704695
  have hstable : (prefixWord ++ tailWord_6704695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704695).length < 2 ^ (prefixWord ++ tailWord_6704695).sum := by decide
  have hdescent : baseEnd_6704695 < baseStart_6704695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6704725 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6704725 : Nat := 118140960795 + 6704725 * 2 ^ 59
def prefixEnd_6704725 : Nat := 4983230072969 + 3 ^ 40 * 6704725 * 2
def baseEnd_6704725 : Nat := 3442746581216385466303037

theorem tailTrace_6704725 : CollatzResearch.WordTrace tailWord_6704725 prefixEnd_6704725 3442746581216385466303037 := by
  unfold tailWord_6704725
  simp only [CollatzResearch.WordTrace]
  refine ⟨244541410634933875710963629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163027607089955917140642419 244541410634933875710963629)
  ·
    refine ⟨91703028988100203391611361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244541410634933875710963629 91703028988100203391611361)
    ·
      refine ⟨68777271741075152543708521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91703028988100203391611361 68777271741075152543708521)
      ·
        refine ⟨51582953805806364407781391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68777271741075152543708521 51582953805806364407781391)
        ·
          refine ⟨77374430708709546611672087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51582953805806364407781391 77374430708709546611672087)
          ·
            refine ⟨116061646063064319917508131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77374430708709546611672087 116061646063064319917508131)
            ·
              refine ⟨174092469094596479876262197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116061646063064319917508131 174092469094596479876262197)
              ·
                refine ⟨16321168977618419988399581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174092469094596479876262197 16321168977618419988399581)
                ·
                  refine ⟨6120438366606907495649843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16321168977618419988399581 6120438366606907495649843)
                  ·
                    refine ⟨9180657549910361243474765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120438366606907495649843 9180657549910361243474765)
                    ·
                      refine ⟨3442746581216385466303037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9180657549910361243474765 3442746581216385466303037)
                      ·
                        rfl

theorem cell23_6704725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6704725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6704725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6704725 prefixEnd_6704725 := by exact prefixLift 6704725
  have htrace : WordTrace (prefixWord ++ tailWord_6704725) baseStart_6704725 baseEnd_6704725 := by
    simpa [prefixWord, tailWord_6704725, baseEnd_6704725] using wordTrace_append hprefix tailTrace_6704725
  have hstable : (prefixWord ++ tailWord_6704725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6704725).length < 2 ^ (prefixWord ++ tailWord_6704725).sum := by decide
  have hdescent : baseEnd_6704725 < baseStart_6704725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6704725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
