import V185TrunkScan23Chunk1065

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6311020 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_6311020 : Nat := 118140960795 + 6311020 * 2 ^ 59
def prefixEnd_6311020 : Nat := 4983230072969 + 3 ^ 40 * 6311020 * 2
def baseEnd_6311020 : Nat := 3240586680138003338926153

theorem tailTrace_6311020 : CollatzResearch.WordTrace tailWord_6311020 prefixEnd_6311020 3240586680138003338926153 := by
  unfold tailWord_6311020
  simp only [CollatzResearch.WordTrace]
  refine ⟨115090904798129925625085257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153454539730839900833447009 115090904798129925625085257)
  ·
    refine ⟨86318178598597444218813943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115090904798129925625085257 86318178598597444218813943)
    ·
      refine ⟨129477267897896166328220915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86318178598597444218813943 129477267897896166328220915)
      ·
        refine ⟨194215901846844249492331373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129477267897896166328220915 194215901846844249492331373)
        ·
          refine ⟨72830963192566593559624265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194215901846844249492331373 72830963192566593559624265)
          ·
            refine ⟨54623222394424945169718199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72830963192566593559624265 54623222394424945169718199)
            ·
              refine ⟨81934833591637417754577299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54623222394424945169718199 81934833591637417754577299)
              ·
                refine ⟨122902250387456126631865949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81934833591637417754577299 122902250387456126631865949)
                ·
                  refine ⟨46088343895296047486949731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122902250387456126631865949 46088343895296047486949731)
                  ·
                    refine ⟨69132515842944071230424597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46088343895296047486949731 69132515842944071230424597)
                    ·
                      refine ⟨3240586680138003338926153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69132515842944071230424597 3240586680138003338926153)
                      ·
                        rfl

theorem cell23_6311020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_6311020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311020 prefixEnd_6311020 := by exact prefixLift 6311020
  have htrace : WordTrace (prefixWord ++ tailWord_6311020) baseStart_6311020 baseEnd_6311020 := by
    simpa [prefixWord, tailWord_6311020, baseEnd_6311020] using wordTrace_append hprefix tailTrace_6311020
  have hstable : (prefixWord ++ tailWord_6311020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311020).length < 2 ^ (prefixWord ++ tailWord_6311020).sum := by decide
  have hdescent : baseEnd_6311020 < baseStart_6311020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311037 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_6311037 : Nat := 118140960795 + 6311037 * 2 ^ 59
def prefixEnd_6311037 : Nat := 4983230072969 + 3 ^ 40 * 6311037 * 2
def baseEnd_6311037 : Nat := 3240595409309129772413575

theorem tailTrace_6311037 : CollatzResearch.WordTrace tailWord_6311037 prefixEnd_6311037 3240595409309129772413575 := by
  unfold tailWord_6311037
  simp only [CollatzResearch.WordTrace]
  refine ⟨230182429637198263153539365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153454953091465508769026243 230182429637198263153539365)
  ·
    refine ⟨43159205556974674341288631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230182429637198263153539365 43159205556974674341288631)
    ·
      refine ⟨64738808335462011511932947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43159205556974674341288631 64738808335462011511932947)
      ·
        refine ⟨97108212503193017267899421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64738808335462011511932947 97108212503193017267899421)
        ·
          refine ⟨36415579688697381475462283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97108212503193017267899421 36415579688697381475462283)
          ·
            refine ⟨54623369533046072213193425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36415579688697381475462283 54623369533046072213193425)
            ·
              refine ⟨40967527149784554159895069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54623369533046072213193425 40967527149784554159895069)
              ·
                refine ⟨15362822681169207809960651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40967527149784554159895069 15362822681169207809960651)
                ·
                  refine ⟨23044234021753811714940977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15362822681169207809960651 23044234021753811714940977)
                  ·
                    refine ⟨17283175516315358786205733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23044234021753811714940977 17283175516315358786205733)
                    ·
                      refine ⟨3240595409309129772413575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283175516315358786205733 3240595409309129772413575)
                      ·
                        rfl

theorem cell23_6311037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_6311037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311037 prefixEnd_6311037 := by exact prefixLift 6311037
  have htrace : WordTrace (prefixWord ++ tailWord_6311037) baseStart_6311037 baseEnd_6311037 := by
    simpa [prefixWord, tailWord_6311037, baseEnd_6311037] using wordTrace_append hprefix tailTrace_6311037
  have hstable : (prefixWord ++ tailWord_6311037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311037).length < 2 ^ (prefixWord ++ tailWord_6311037).sum := by decide
  have hdescent : baseEnd_6311037 < baseStart_6311037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311038 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6311038 : Nat := 118140960795 + 6311038 * 2 ^ 59
def prefixEnd_6311038 : Nat := 4983230072969 + 3 ^ 40 * 6311038 * 2
def baseEnd_6311038 : Nat := 1080198640929928089500357

theorem tailTrace_6311038 : CollatzResearch.WordTrace tailWord_6311038 prefixEnd_6311038 1080198640929928089500357 := by
  unfold tailWord_6311038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28772808263774330040540721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153454977406796426882883845 28772808263774330040540721)
  ·
    refine ⟨21579606197830747530405541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28772808263774330040540721 21579606197830747530405541)
    ·
      refine ⟨4046176162093265161951039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21579606197830747530405541 4046176162093265161951039)
      ·
        refine ⟨6069264243139897742926559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046176162093265161951039 6069264243139897742926559)
        ·
          refine ⟨9103896364709846614389839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069264243139897742926559 9103896364709846614389839)
          ·
            refine ⟨13655844547064769921584759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103896364709846614389839 13655844547064769921584759)
            ·
              refine ⟨20483766820597154882377139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655844547064769921584759 20483766820597154882377139)
              ·
                refine ⟨30725650230895732323565709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483766820597154882377139 30725650230895732323565709)
                ·
                  refine ⟨11522118836585899621337141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30725650230895732323565709 11522118836585899621337141)
                  ·
                    refine ⟨1080198640929928089500357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11522118836585899621337141 1080198640929928089500357)
                    ·
                      rfl

theorem cell23_6311038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6311038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311038 prefixEnd_6311038 := by exact prefixLift 6311038
  have htrace : WordTrace (prefixWord ++ tailWord_6311038) baseStart_6311038 baseEnd_6311038 := by
    simpa [prefixWord, tailWord_6311038, baseEnd_6311038] using wordTrace_append hprefix tailTrace_6311038
  have hstable : (prefixWord ++ tailWord_6311038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311038).length < 2 ^ (prefixWord ++ tailWord_6311038).sum := by decide
  have hdescent : baseEnd_6311038 < baseStart_6311038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311041 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6311041 : Nat := 118140960795 + 6311041 * 2 ^ 59
def prefixEnd_6311041 : Nat := 4983230072969 + 3 ^ 40 * 6311041 * 2
def baseEnd_6311041 : Nat := 3240597463231747756763557

theorem tailTrace_6311041 : CollatzResearch.WordTrace tailWord_6311041 prefixEnd_6311041 3240597463231747756763557 := by
  unfold tailWord_6311041
  simp only [CollatzResearch.WordTrace]
  refine ⟨230182575529183771836684977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153455050352789181224456651 230182575529183771836684977)
  ·
    refine ⟨172636931646887828877513733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230182575529183771836684977 172636931646887828877513733)
    ·
      refine ⟨32369424683791467914533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172636931646887828877513733 32369424683791467914533825)
      ·
        refine ⟨24277068512843600935900369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32369424683791467914533825 24277068512843600935900369)
        ·
          refine ⟨18207801384632700701925277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24277068512843600935900369 18207801384632700701925277)
          ·
            refine ⟨6827925519237262763221979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18207801384632700701925277 6827925519237262763221979)
            ·
              refine ⟨10241888278855894144832969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827925519237262763221979 10241888278855894144832969)
              ·
                refine ⟨7681416209141920608624727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10241888278855894144832969 7681416209141920608624727)
                ·
                  refine ⟨11522124313712880912937091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681416209141920608624727 11522124313712880912937091)
                  ·
                    refine ⟨17283186470569321369405637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11522124313712880912937091 17283186470569321369405637)
                    ·
                      refine ⟨3240597463231747756763557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283186470569321369405637 3240597463231747756763557)
                      ·
                        rfl

theorem cell23_6311041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6311041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311041 prefixEnd_6311041 := by exact prefixLift 6311041
  have htrace : WordTrace (prefixWord ++ tailWord_6311041) baseStart_6311041 baseEnd_6311041 := by
    simpa [prefixWord, tailWord_6311041, baseEnd_6311041] using wordTrace_append hprefix tailTrace_6311041
  have hstable : (prefixWord ++ tailWord_6311041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311041).length < 2 ^ (prefixWord ++ tailWord_6311041).sum := by decide
  have hdescent : baseEnd_6311041 < baseStart_6311041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311044 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_6311044 : Nat := 118140960795 + 6311044 * 2 ^ 59
def prefixEnd_6311044 : Nat := 4983230072969 + 3 ^ 40 * 6311044 * 2
def baseEnd_6311044 : Nat := 3240599003673711245026043

theorem tailTrace_6311044 : CollatzResearch.WordTrace tailWord_6311044 prefixEnd_6311044 3240599003673711245026043 := by
  unfold tailWord_6311044
  simp only [CollatzResearch.WordTrace]
  refine ⟨115091342474086451674522093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153455123298781935566029457 115091342474086451674522093)
  ·
    refine ⟨43159253427782419377945785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115091342474086451674522093 43159253427782419377945785)
    ·
      refine ⟨32369440070836814533459339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43159253427782419377945785 32369440070836814533459339)
      ·
        refine ⟨48554160106255221800189009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32369440070836814533459339 48554160106255221800189009)
        ·
          refine ⟨36415620079691416350141757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48554160106255221800189009 36415620079691416350141757)
          ·
            refine ⟨13655857529884281131303159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36415620079691416350141757 13655857529884281131303159)
            ·
              refine ⟨20483786294826421696954739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655857529884281131303159 20483786294826421696954739)
              ·
                refine ⟨30725679442239632545432109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483786294826421696954739 30725679442239632545432109)
                ·
                  refine ⟨11522129790839862204537041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30725679442239632545432109 11522129790839862204537041)
                  ·
                    refine ⟨8641597343129896653402781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11522129790839862204537041 8641597343129896653402781)
                    ·
                      refine ⟨3240599003673711245026043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8641597343129896653402781 3240599003673711245026043)
                      ·
                        rfl

theorem cell23_6311044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_6311044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311044 prefixEnd_6311044 := by exact prefixLift 6311044
  have htrace : WordTrace (prefixWord ++ tailWord_6311044) baseStart_6311044 baseEnd_6311044 := by
    simpa [prefixWord, tailWord_6311044, baseEnd_6311044] using wordTrace_append hprefix tailTrace_6311044
  have hstable : (prefixWord ++ tailWord_6311044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311044).length < 2 ^ (prefixWord ++ tailWord_6311044).sum := by decide
  have hdescent : baseEnd_6311044 < baseStart_6311044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311054 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6311054 : Nat := 118140960795 + 6311054 * 2 ^ 59
def prefixEnd_6311054 : Nat := 4983230072969 + 3 ^ 40 * 6311054 * 2
def baseEnd_6311054 : Nat := 3240604138480256205900997

theorem tailTrace_6311054 : CollatzResearch.WordTrace tailWord_6311054 prefixEnd_6311054 3240604138480256205900997 := by
  unfold tailWord_6311054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28772881209767084382113527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153455366452091116704605477 28772881209767084382113527)
  ·
    refine ⟨43159321814650626573170291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28772881209767084382113527 43159321814650626573170291)
    ·
      refine ⟨64738982721975939859755437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43159321814650626573170291 64738982721975939859755437)
      ·
        refine ⟨24277118520740977447408289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64738982721975939859755437 24277118520740977447408289)
        ·
          refine ⟨18207838890555733085556217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24277118520740977447408289 18207838890555733085556217)
          ·
            refine ⟨13655879167916799814167163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18207838890555733085556217 13655879167916799814167163)
            ·
              refine ⟨20483818751875199721250745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655879167916799814167163 20483818751875199721250745)
              ·
                refine ⟨15362864063906399790938059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20483818751875199721250745 15362864063906399790938059)
                ·
                  refine ⟨23044296095859599686407089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15362864063906399790938059 23044296095859599686407089)
                  ·
                    refine ⟨17283222071894699764805317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23044296095859599686407089 17283222071894699764805317)
                    ·
                      refine ⟨3240604138480256205900997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283222071894699764805317 3240604138480256205900997)
                      ·
                        rfl

theorem cell23_6311054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6311054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311054 prefixEnd_6311054 := by exact prefixLift 6311054
  have htrace : WordTrace (prefixWord ++ tailWord_6311054) baseStart_6311054 baseEnd_6311054 := by
    simpa [prefixWord, tailWord_6311054, baseEnd_6311054] using wordTrace_append hprefix tailTrace_6311054
  have hstable : (prefixWord ++ tailWord_6311054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311054).length < 2 ^ (prefixWord ++ tailWord_6311054).sum := by decide
  have hdescent : baseEnd_6311054 < baseStart_6311054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311118 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_6311118 : Nat := 118140960795 + 6311118 * 2 ^ 59
def prefixEnd_6311118 : Nat := 4983230072969 + 3 ^ 40 * 6311118 * 2
def baseEnd_6311118 : Nat := 3240637001242143955500703

theorem tailTrace_6311118 : CollatzResearch.WordTrace tailWord_6311118 prefixEnd_6311118 3240637001242143955500703 := by
  unfold tailWord_6311118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28773172993738101748404751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153456922633269875991492005 28773172993738101748404751)
  ·
    refine ⟨43159759490607152622607127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28773172993738101748404751 43159759490607152622607127)
    ·
      refine ⟨64739639235910728933910691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43159759490607152622607127 64739639235910728933910691)
      ·
        refine ⟨97109458853866093400866037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64739639235910728933910691 97109458853866093400866037)
        ·
          refine ⟨9104011767549946256331191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97109458853866093400866037 9104011767549946256331191)
          ·
            refine ⟨13656017651324919384496787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104011767549946256331191 13656017651324919384496787)
            ·
              refine ⟨20484026476987379076745181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13656017651324919384496787 20484026476987379076745181)
              ·
                refine ⟨7681509928870267153779443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20484026476987379076745181 7681509928870267153779443)
                ·
                  refine ⟨11522264893305400730669165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681509928870267153779443 11522264893305400730669165)
                  ·
                    refine ⟨4320849334989525274000937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11522264893305400730669165 4320849334989525274000937)
                    ·
                      refine ⟨3240637001242143955500703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320849334989525274000937 3240637001242143955500703)
                      ·
                        rfl

theorem cell23_6311118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_6311118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311118 prefixEnd_6311118 := by exact prefixLift 6311118
  have htrace : WordTrace (prefixWord ++ tailWord_6311118) baseStart_6311118 baseEnd_6311118 := by
    simpa [prefixWord, tailWord_6311118, baseEnd_6311118] using wordTrace_append hprefix tailTrace_6311118
  have hstable : (prefixWord ++ tailWord_6311118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311118).length < 2 ^ (prefixWord ++ tailWord_6311118).sum := by decide
  have hdescent : baseEnd_6311118 < baseStart_6311118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311127 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_6311127 : Nat := 118140960795 + 6311127 * 2 ^ 59
def prefixEnd_6311127 : Nat := 4983230072969 + 3 ^ 40 * 6311127 * 2
def baseEnd_6311127 : Nat := 3240641622568034420288161

theorem tailTrace_6311127 : CollatzResearch.WordTrace tailWord_6311127 prefixEnd_6311127 3240641622568034420288161 := by
  unfold tailWord_6311127
  simp only [CollatzResearch.WordTrace]
  refine ⟨230185712206872208524315635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153457141471248139016210423 230185712206872208524315635)
  ·
    refine ⟨345278568310308312786473453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230185712206872208524315635 345278568310308312786473453)
    ·
      refine ⟨129479463116365617294927545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345278568310308312786473453 129479463116365617294927545)
      ·
        refine ⟨97109597337274212971195659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129479463116365617294927545 97109597337274212971195659)
        ·
          refine ⟨145664396005911319456793489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97109597337274212971195659 145664396005911319456793489)
          ·
            refine ⟨109248297004433489592595117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145664396005911319456793489 109248297004433489592595117)
            ·
              refine ⟨40968111376662558597223169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109248297004433489592595117 40968111376662558597223169)
              ·
                refine ⟨30726083532496918947917377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40968111376662558597223169 30726083532496918947917377)
                ·
                  refine ⟨23044562649372689210938033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30726083532496918947917377 23044562649372689210938033)
                  ·
                    refine ⟨17283421987029516908203525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23044562649372689210938033 17283421987029516908203525)
                    ·
                      refine ⟨3240641622568034420288161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283421987029516908203525 3240641622568034420288161)
                      ·
                        rfl

theorem cell23_6311127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_6311127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311127 prefixEnd_6311127 := by exact prefixLift 6311127
  have htrace : WordTrace (prefixWord ++ tailWord_6311127) baseStart_6311127 baseEnd_6311127 := by
    simpa [prefixWord, tailWord_6311127, baseEnd_6311127] using wordTrace_append hprefix tailTrace_6311127
  have hstable : (prefixWord ++ tailWord_6311127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311127).length < 2 ^ (prefixWord ++ tailWord_6311127).sum := by decide
  have hdescent : baseEnd_6311127 < baseStart_6311127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311137 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 7]
def baseStart_6311137 : Nat := 118140960795 + 6311137 * 2 ^ 59
def prefixEnd_6311137 : Nat := 4983230072969 + 3 ^ 40 * 6311137 * 2
def baseEnd_6311137 : Nat := 360071861930508820129235

theorem tailTrace_6311137 : CollatzResearch.WordTrace tailWord_6311137 prefixEnd_6311137 360071861930508820129235 := by
  unfold tailWord_6311137
  simp only [CollatzResearch.WordTrace]
  refine ⟨230186076936835980232179665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153457384624557320154786443 230186076936835980232179665)
  ·
    refine ⟨172639557702626985174134749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230186076936835980232179665 172639557702626985174134749)
    ·
      refine ⟨64739834138485119440300531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172639557702626985174134749 64739834138485119440300531)
      ·
        refine ⟨97109751207727679160450797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64739834138485119440300531 97109751207727679160450797)
        ·
          refine ⟨36416156702897879685169049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97109751207727679160450797 36416156702897879685169049)
          ·
            refine ⟨27312117527173409763876787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36416156702897879685169049 27312117527173409763876787)
            ·
              refine ⟨40968176290760114645815181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27312117527173409763876787 40968176290760114645815181)
              ·
                refine ⟨15363066109035042992180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40968176290760114645815181 15363066109035042992180693)
                ·
                  refine ⟨360071861930508820129235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15363066109035042992180693 360071861930508820129235)
                  ·
                    rfl

theorem cell23_6311137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_6311137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311137 prefixEnd_6311137 := by exact prefixLift 6311137
  have htrace : WordTrace (prefixWord ++ tailWord_6311137) baseStart_6311137 baseEnd_6311137 := by
    simpa [prefixWord, tailWord_6311137, baseEnd_6311137] using wordTrace_append hprefix tailTrace_6311137
  have hstable : (prefixWord ++ tailWord_6311137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311137).length < 2 ^ (prefixWord ++ tailWord_6311137).sum := by decide
  have hdescent : baseEnd_6311137 < baseStart_6311137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311167 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 7]
def baseStart_6311167 : Nat := 118140960795 + 6311167 * 2 ^ 59
def prefixEnd_6311167 : Nat := 4983230072969 + 3 ^ 40 * 6311167 * 2
def baseEnd_6311167 : Nat := 1080220720598071421262659

theorem tailTrace_6311167 : CollatzResearch.WordTrace tailWord_6311167 prefixEnd_6311167 1080220720598071421262659 := by
  unfold tailWord_6311167
  simp only [CollatzResearch.WordTrace]
  refine ⟨230187171126727295355771755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153458114084484863570514503 230187171126727295355771755)
  ·
    refine ⟨345280756690090943033657633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230187171126727295355771755 345280756690090943033657633)
    ·
      refine ⟨258960567517568207275243225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345280756690090943033657633 258960567517568207275243225)
      ·
        refine ⟨194220425638176155456432419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258960567517568207275243225 194220425638176155456432419)
        ·
          refine ⟨291330638457264233184648629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194220425638176155456432419 291330638457264233184648629)
          ·
            refine ⟨27312247355368521861060809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291330638457264233184648629 27312247355368521861060809)
            ·
              refine ⟨20484185516526391395795607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27312247355368521861060809 20484185516526391395795607)
              ·
                refine ⟨30726278274789587093693411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20484185516526391395795607 30726278274789587093693411)
                ·
                  refine ⟨46089417412184380640540117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30726278274789587093693411 46089417412184380640540117)
                  ·
                    refine ⟨1080220720598071421262659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46089417412184380640540117 1080220720598071421262659)
                    ·
                      rfl

theorem cell23_6311167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_6311167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311167 prefixEnd_6311167 := by exact prefixLift 6311167
  have htrace : WordTrace (prefixWord ++ tailWord_6311167) baseStart_6311167 baseEnd_6311167 := by
    simpa [prefixWord, tailWord_6311167, baseEnd_6311167] using wordTrace_append hprefix tailTrace_6311167
  have hstable : (prefixWord ++ tailWord_6311167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311167).length < 2 ^ (prefixWord ++ tailWord_6311167).sum := by decide
  have hdescent : baseEnd_6311167 < baseStart_6311167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311171 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 5]
def baseStart_6311171 : Nat := 118140960795 + 6311171 * 2 ^ 59
def prefixEnd_6311171 : Nat := 4983230072969 + 3 ^ 40 * 6311171 * 2
def baseEnd_6311171 : Nat := 360073801746314694237551

theorem tailTrace_6311171 : CollatzResearch.WordTrace tailWord_6311171 prefixEnd_6311171 360073801746314694237551 := by
  unfold tailWord_6311171
  simp only [CollatzResearch.WordTrace]
  refine ⟨230187317018712804038917367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153458211345808536025944911 230187317018712804038917367)
  ·
    refine ⟨345280975528069206058376051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230187317018712804038917367 345280975528069206058376051)
    ·
      refine ⟨517921463292103809087564077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345280975528069206058376051 517921463292103809087564077)
      ·
        refine ⟨194220548734538928407836529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517921463292103809087564077 194220548734538928407836529)
        ·
          refine ⟨145665411550904196305877397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194220548734538928407836529 145665411550904196305877397)
          ·
            refine ⟨6828066166448634201838003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145665411550904196305877397 6828066166448634201838003)
            ·
              refine ⟨10242099249672951302757005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828066166448634201838003 10242099249672951302757005)
              ·
                refine ⟨3840787218627356738533877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10242099249672951302757005 3840787218627356738533877)
                ·
                  refine ⟨360073801746314694237551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840787218627356738533877 360073801746314694237551)
                  ·
                    rfl

theorem cell23_6311171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 5].length) (baseStart_6311171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311171 prefixEnd_6311171 := by exact prefixLift 6311171
  have htrace : WordTrace (prefixWord ++ tailWord_6311171) baseStart_6311171 baseEnd_6311171 := by
    simpa [prefixWord, tailWord_6311171, baseEnd_6311171] using wordTrace_append hprefix tailTrace_6311171
  have hstable : (prefixWord ++ tailWord_6311171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311171).length < 2 ^ (prefixWord ++ tailWord_6311171).sum := by decide
  have hdescent : baseEnd_6311171 < baseStart_6311171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311177 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_6311177 : Nat := 118140960795 + 6311177 * 2 ^ 59
def prefixEnd_6311177 : Nat := 4983230072969 + 3 ^ 40 * 6311177 * 2
def baseEnd_6311177 : Nat := 3240667296600759224662931

theorem tailTrace_6311177 : CollatzResearch.WordTrace tailWord_6311177 prefixEnd_6311177 3240667296600759224662931 := by
  unfold tailWord_6311177
  simp only [CollatzResearch.WordTrace]
  refine ⟨230187535856691067063635785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153458357237794044709090523 230187535856691067063635785)
  ·
    refine ⟨172640651892518300297726839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230187535856691067063635785 172640651892518300297726839)
    ·
      refine ⟨258960977838777450446590259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172640651892518300297726839 258960977838777450446590259)
      ·
        refine ⟨388441466758166175669885389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258960977838777450446590259 388441466758166175669885389)
        ·
          refine ⟨145665550034312315876207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388441466758166175669885389 145665550034312315876207021)
          ·
            refine ⟨54624581262867118453577633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145665550034312315876207021 54624581262867118453577633)
            ·
              refine ⟨40968435947150338840183225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54624581262867118453577633 40968435947150338840183225)
              ·
                refine ⟨30726326960362754130137419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40968435947150338840183225 30726326960362754130137419)
                ·
                  refine ⟨46089490440544131195206129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30726326960362754130137419 46089490440544131195206129)
                  ·
                    refine ⟨34567117830408098396404597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46089490440544131195206129 34567117830408098396404597)
                    ·
                      refine ⟨3240667296600759224662931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34567117830408098396404597 3240667296600759224662931)
                      ·
                        rfl

theorem cell23_6311177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_6311177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311177 prefixEnd_6311177 := by exact prefixLift 6311177
  have htrace : WordTrace (prefixWord ++ tailWord_6311177) baseStart_6311177 baseEnd_6311177 := by
    simpa [prefixWord, tailWord_6311177, baseEnd_6311177] using wordTrace_append hprefix tailTrace_6311177
  have hstable : (prefixWord ++ tailWord_6311177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311177).length < 2 ^ (prefixWord ++ tailWord_6311177).sum := by decide
  have hdescent : baseEnd_6311177 < baseStart_6311177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311194 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_6311194 : Nat := 118140960795 + 6311194 * 2 ^ 59
def prefixEnd_6311194 : Nat := 4983230072969 + 3 ^ 40 * 6311194 * 2
def baseEnd_6311194 : Nat := 3240676025771885658150353

theorem tailTrace_6311194 : CollatzResearch.WordTrace tailWord_6311194 prefixEnd_6311194 3240676025771885658150353 := by
  unfold tailWord_6311194
  simp only [CollatzResearch.WordTrace]
  refine ⟨57547038974407369741751159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153458770598419652644669757 57547038974407369741751159)
  ·
    refine ⟨86320558461611054612626739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57547038974407369741751159 86320558461611054612626739)
    ·
      refine ⟨129480837692416581918940109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86320558461611054612626739 129480837692416581918940109)
      ·
        refine ⟨48555314134656218219602541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129480837692416581918940109 48555314134656218219602541)
        ·
          refine ⟨18208242800496081832350953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48555314134656218219602541 18208242800496081832350953)
          ·
            refine ⟨13656182100372061374263215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18208242800496081832350953 13656182100372061374263215)
            ·
              refine ⟨20484273150558092061394823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13656182100372061374263215 20484273150558092061394823)
              ·
                refine ⟨30726409725837138092092235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20484273150558092061394823 30726409725837138092092235)
                ·
                  refine ⟨46089614588755707138138353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30726409725837138092092235 46089614588755707138138353)
                  ·
                    refine ⟨34567210941566780353603765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46089614588755707138138353 34567210941566780353603765)
                    ·
                      refine ⟨3240676025771885658150353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34567210941566780353603765 3240676025771885658150353)
                      ·
                        rfl

theorem cell23_6311194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_6311194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311194 prefixEnd_6311194 := by exact prefixLift 6311194
  have htrace : WordTrace (prefixWord ++ tailWord_6311194) baseStart_6311194 baseEnd_6311194 := by
    simpa [prefixWord, tailWord_6311194, baseEnd_6311194] using wordTrace_append hprefix tailTrace_6311194
  have hstable : (prefixWord ++ tailWord_6311194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311194).length < 2 ^ (prefixWord ++ tailWord_6311194).sum := by decide
  have hdescent : baseEnd_6311194 < baseStart_6311194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311204 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6311204 : Nat := 118140960795 + 6311204 * 2 ^ 59
def prefixEnd_6311204 : Nat := 4983230072969 + 3 ^ 40 * 6311204 * 2
def baseEnd_6311204 : Nat := 3240681160578430619025307

theorem tailTrace_6311204 : CollatzResearch.WordTrace tailWord_6311204 prefixEnd_6311204 3240681160578430619025307 := by
  unfold tailWord_6311204
  simp only [CollatzResearch.WordTrace]
  refine ⟨115094260313796625337434333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153459013751728833783245777 115094260313796625337434333)
  ·
    refine ⟨43160347617673734501537875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115094260313796625337434333 43160347617673734501537875)
    ·
      refine ⟨64740521426510601752306813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43160347617673734501537875 64740521426510601752306813)
      ·
        refine ⟨24277695534941475657115055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64740521426510601752306813 24277695534941475657115055)
        ·
          refine ⟨36416543302412213485672583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24277695534941475657115055 36416543302412213485672583)
          ·
            refine ⟨54624814953618320228508875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36416543302412213485672583 54624814953618320228508875)
            ·
              refine ⟨81937222430427480342763313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54624814953618320228508875 81937222430427480342763313)
              ·
                refine ⟨61452916822820610257072485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81937222430427480342763313 61452916822820610257072485)
                ·
                  refine ⟨11522421904278864423201091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61452916822820610257072485 11522421904278864423201091)
                  ·
                    refine ⟨17283632856418296634801637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11522421904278864423201091 17283632856418296634801637)
                    ·
                      refine ⟨3240681160578430619025307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283632856418296634801637 3240681160578430619025307)
                      ·
                        rfl

theorem cell23_6311204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6311204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311204 prefixEnd_6311204 := by exact prefixLift 6311204
  have htrace : WordTrace (prefixWord ++ tailWord_6311204) baseStart_6311204 baseEnd_6311204 := by
    simpa [prefixWord, tailWord_6311204, baseEnd_6311204] using wordTrace_append hprefix tailTrace_6311204
  have hstable : (prefixWord ++ tailWord_6311204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311204).length < 2 ^ (prefixWord ++ tailWord_6311204).sum := by decide
  have hdescent : baseEnd_6311204 < baseStart_6311204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311221 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6311221 : Nat := 118140960795 + 6311221 * 2 ^ 59
def prefixEnd_6311221 : Nat := 4983230072969 + 3 ^ 40 * 6311221 * 2
def baseEnd_6311221 : Nat := 3240689889749557052512729

theorem tailTrace_6311221 : CollatzResearch.WordTrace tailWord_6311221 prefixEnd_6311221 3240689889749557052512729 := by
  unfold tailWord_6311221
  simp only [CollatzResearch.WordTrace]
  refine ⟨230189140668531662578237517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153459427112354441718825011 230189140668531662578237517)
  ·
    refine ⟨86320927750699373466839069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230189140668531662578237517 86320927750699373466839069)
    ·
      refine ⟨32370347906512265050064651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86320927750699373466839069 32370347906512265050064651)
      ·
        refine ⟨48555521859768397575096977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32370347906512265050064651 48555521859768397575096977)
        ·
          refine ⟨36416641394826298181322733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48555521859768397575096977 36416641394826298181322733)
          ·
            refine ⟨13656240523059861817996025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36416641394826298181322733 13656240523059861817996025)
            ·
              refine ⟨10242180392294896363497019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13656240523059861817996025 10242180392294896363497019)
              ·
                refine ⟨15363270588442344545245529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242180392294896363497019 15363270588442344545245529)
                ·
                  refine ⟨11522452941331758408934147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15363270588442344545245529 11522452941331758408934147)
                  ·
                    refine ⟨17283679411997637613401221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11522452941331758408934147 17283679411997637613401221)
                    ·
                      refine ⟨3240689889749557052512729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17283679411997637613401221 3240689889749557052512729)
                      ·
                        rfl

theorem cell23_6311221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6311221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311221 prefixEnd_6311221 := by exact prefixLift 6311221
  have htrace : WordTrace (prefixWord ++ tailWord_6311221) baseStart_6311221 baseEnd_6311221 := by
    simpa [prefixWord, tailWord_6311221, baseEnd_6311221] using wordTrace_append hprefix tailTrace_6311221
  have hstable : (prefixWord ++ tailWord_6311221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311221).length < 2 ^ (prefixWord ++ tailWord_6311221).sum := by decide
  have hdescent : baseEnd_6311221 < baseStart_6311221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311244 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 6]
def baseStart_6311244 : Nat := 118140960795 + 6311244 * 2 ^ 59
def prefixEnd_6311244 : Nat := 4983230072969 + 3 ^ 40 * 6311244 * 2
def baseEnd_6311244 : Nat := 360077966644956718058347

theorem tailTrace_6311244 : CollatzResearch.WordTrace tailWord_6311244 prefixEnd_6311244 360077966644956718058347 := by
  unfold tailWord_6311244
  simp only [CollatzResearch.WordTrace]
  refine ⟨115094989773724168753162393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153459986364965558337549857 115094989773724168753162393)
  ·
    refine ⟨86321242330293126564871795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115094989773724168753162393 86321242330293126564871795)
    ·
      refine ⟨129481863495439689847307693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86321242330293126564871795 129481863495439689847307693)
      ·
        refine ⟨48555698810789883692740385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129481863495439689847307693 48555698810789883692740385)
        ·
          refine ⟨36416774108092412769555289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48555698810789883692740385 36416774108092412769555289)
          ·
            refine ⟨27312580581069309577166467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36416774108092412769555289 27312580581069309577166467)
            ·
              refine ⟨40968870871603964365749701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27312580581069309577166467 40968870871603964365749701)
              ·
                refine ⟨7681663288425743318578069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40968870871603964365749701 7681663288425743318578069)
                ·
                  refine ⟨360077966644956718058347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7681663288425743318578069 360077966644956718058347)
                  ·
                    rfl

theorem cell23_6311244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_6311244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311244 prefixEnd_6311244 := by exact prefixLift 6311244
  have htrace : WordTrace (prefixWord ++ tailWord_6311244) baseStart_6311244 baseEnd_6311244 := by
    simpa [prefixWord, tailWord_6311244, baseEnd_6311244] using wordTrace_append hprefix tailTrace_6311244
  have hstable : (prefixWord ++ tailWord_6311244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311244).length < 2 ^ (prefixWord ++ tailWord_6311244).sum := by decide
  have hdescent : baseEnd_6311244 < baseStart_6311244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311321 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_6311321 : Nat := 118140960795 + 6311321 * 2 ^ 59
def prefixEnd_6311321 : Nat := 4983230072969 + 3 ^ 40 * 6311321 * 2
def baseEnd_6311321 : Nat := 1080247079271668887087423

theorem tailTrace_6311321 : CollatzResearch.WordTrace tailWord_6311321 prefixEnd_6311321 1080247079271668887087423 := by
  unfold tailWord_6311321
  simp only [CollatzResearch.WordTrace]
  refine ⟨230192787968169379656877817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153461858645446253104585211 230192787968169379656877817)
  ·
    refine ⟨172644590976127034742658363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230192787968169379656877817 172644590976127034742658363)
    ·
      refine ⟨258966886464190552113987545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172644590976127034742658363 258966886464190552113987545)
      ·
        refine ⟨194225164848142914085490659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258966886464190552113987545 194225164848142914085490659)
        ·
          refine ⟨291337747272214371128235989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194225164848142914085490659 291337747272214371128235989)
          ·
            refine ⟨6828228451692524323318031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 291337747272214371128235989 6828228451692524323318031)
            ·
              refine ⟨10242342677538786484977047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828228451692524323318031 10242342677538786484977047)
              ·
                refine ⟨15363514016308179727465571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242342677538786484977047 15363514016308179727465571)
                ·
                  refine ⟨23045271024462269591198357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15363514016308179727465571 23045271024462269591198357)
                  ·
                    refine ⟨1080247079271668887087423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23045271024462269591198357 1080247079271668887087423)
                    ·
                      rfl

theorem cell23_6311321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_6311321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311321 prefixEnd_6311321 := by exact prefixLift 6311321
  have htrace : WordTrace (prefixWord ++ tailWord_6311321) baseStart_6311321 baseEnd_6311321 := by
    simpa [prefixWord, tailWord_6311321, baseEnd_6311321] using wordTrace_append hprefix tailTrace_6311321
  have hstable : (prefixWord ++ tailWord_6311321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311321).length < 2 ^ (prefixWord ++ tailWord_6311321).sum := by decide
  have hdescent : baseEnd_6311321 < baseStart_6311321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311328 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2]
def baseStart_6311328 : Nat := 118140960795 + 6311328 * 2 ^ 59
def prefixEnd_6311328 : Nat := 4983230072969 + 3 ^ 40 * 6311328 * 2
def baseEnd_6311328 : Nat := 3240744832179588133874737

theorem tailTrace_6311328 : CollatzResearch.WordTrace tailWord_6311328 prefixEnd_6311328 3240744832179588133874737 := by
  unfold tailWord_6311328
  simp only [CollatzResearch.WordTrace]
  refine ⟨115096521639572009926191319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153462028852762679901588425 115096521639572009926191319)
  ·
    refine ⟨172644782459358014889286979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115096521639572009926191319 172644782459358014889286979)
    ·
      refine ⟨258967173689037022333930469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172644782459358014889286979 258967173689037022333930469)
      ·
        refine ⟨48556345066694441687611963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258967173689037022333930469 48556345066694441687611963)
        ·
          refine ⟨72834517600041662531417945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48556345066694441687611963 72834517600041662531417945)
          ·
            refine ⟨54625888200031246898563459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72834517600041662531417945 54625888200031246898563459)
            ·
              refine ⟨81938832300046870347845189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54625888200031246898563459 81938832300046870347845189)
              ·
                refine ⟨15363531056258788190220973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81938832300046870347845189 15363531056258788190220973)
                ·
                  refine ⟨5761324146097045571332865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15363531056258788190220973 5761324146097045571332865)
                  ·
                    refine ⟨4320993109572784178499649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5761324146097045571332865 4320993109572784178499649)
                    ·
                      refine ⟨3240744832179588133874737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4320993109572784178499649 3240744832179588133874737)
                      ·
                        rfl

theorem cell23_6311328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_6311328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311328 prefixEnd_6311328 := by exact prefixLift 6311328
  have htrace : WordTrace (prefixWord ++ tailWord_6311328) baseStart_6311328 baseEnd_6311328 := by
    simpa [prefixWord, tailWord_6311328, baseEnd_6311328] using wordTrace_append hprefix tailTrace_6311328
  have hstable : (prefixWord ++ tailWord_6311328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311328).length < 2 ^ (prefixWord ++ tailWord_6311328).sum := by decide
  have hdescent : baseEnd_6311328 < baseStart_6311328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311382 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6311382 : Nat := 118140960795 + 6311382 * 2 ^ 59
def prefixEnd_6311382 : Nat := 4983230072969 + 3 ^ 40 * 6311382 * 2
def baseEnd_6311382 : Nat := 3240772560134930922599489

theorem tailTrace_6311382 : CollatzResearch.WordTrace tailWord_6311382 prefixEnd_6311382 3240772560134930922599489 := by
  unfold tailWord_6311382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14387188301309274192178025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153463341880632258049898933 14387188301309274192178025)
  ·
    refine ⟨10790391225981955644133519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14387188301309274192178025 10790391225981955644133519)
    ·
      refine ⟨16185586838972933466200279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790391225981955644133519 16185586838972933466200279)
      ·
        refine ⟨24278380258459400199300419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16185586838972933466200279 24278380258459400199300419)
        ·
          refine ⟨36417570387689100298950629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24278380258459400199300419 36417570387689100298950629)
          ·
            refine ⟨6828294447691706306053243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36417570387689100298950629 6828294447691706306053243)
            ·
              refine ⟨10242441671537559459079865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828294447691706306053243 10242441671537559459079865)
              ·
                refine ⟨7681831253653169594309899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10242441671537559459079865 7681831253653169594309899)
                ·
                  refine ⟨11522746880479754391464849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681831253653169594309899 11522746880479754391464849)
                  ·
                    refine ⟨8642060160359815793598637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11522746880479754391464849 8642060160359815793598637)
                    ·
                      refine ⟨3240772560134930922599489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642060160359815793598637 3240772560134930922599489)
                      ·
                        rfl

theorem cell23_6311382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6311382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311382 prefixEnd_6311382 := by exact prefixLift 6311382
  have htrace : WordTrace (prefixWord ++ tailWord_6311382) baseStart_6311382 baseEnd_6311382 := by
    simpa [prefixWord, tailWord_6311382, baseEnd_6311382] using wordTrace_append hprefix tailTrace_6311382
  have hstable : (prefixWord ++ tailWord_6311382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311382).length < 2 ^ (prefixWord ++ tailWord_6311382).sum := by decide
  have hdescent : baseEnd_6311382 < baseStart_6311382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311404 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_6311404 : Nat := 118140960795 + 6311404 * 2 ^ 59
def prefixEnd_6311404 : Nat := 4983230072969 + 3 ^ 40 * 6311404 * 2
def baseEnd_6311404 : Nat := 3240783856709329836524387

theorem tailTrace_6311404 : CollatzResearch.WordTrace tailWord_6311404 prefixEnd_6311404 3240783856709329836524387 := by
  unfold tailWord_6311404
  simp only [CollatzResearch.WordTrace]
  refine ⟨115097907613434342416074633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153463876817912456554766177 115097907613434342416074633)
  ·
    refine ⟨86323430710075756812055975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115097907613434342416074633 86323430710075756812055975)
    ·
      refine ⟨129485146065113635218083963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86323430710075756812055975 129485146065113635218083963)
      ·
        refine ⟨194227719097670452827125945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129485146065113635218083963 194227719097670452827125945)
        ·
          refine ⟨145670789323252839620344459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194227719097670452827125945 145670789323252839620344459)
          ·
            refine ⟨218506183984879259430516689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145670789323252839620344459 218506183984879259430516689)
            ·
              refine ⟨163879637988659444572887517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218506183984879259430516689 163879637988659444572887517)
              ·
                refine ⟨61454864245747291714832819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163879637988659444572887517 61454864245747291714832819)
                ·
                  refine ⟨92182296368620937572249229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61454864245747291714832819 92182296368620937572249229)
                  ·
                    refine ⟨34568361138232851589593461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92182296368620937572249229 34568361138232851589593461)
                    ·
                      refine ⟨3240783856709329836524387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34568361138232851589593461 3240783856709329836524387)
                      ·
                        rfl

theorem cell23_6311404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_6311404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311404 prefixEnd_6311404 := by exact prefixLift 6311404
  have htrace : WordTrace (prefixWord ++ tailWord_6311404) baseStart_6311404 baseEnd_6311404 := by
    simpa [prefixWord, tailWord_6311404, baseEnd_6311404] using wordTrace_append hprefix tailTrace_6311404
  have hstable : (prefixWord ++ tailWord_6311404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311404).length < 2 ^ (prefixWord ++ tailWord_6311404).sum := by decide
  have hdescent : baseEnd_6311404 < baseStart_6311404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311421 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_6311421 : Nat := 118140960795 + 6311421 * 2 ^ 59
def prefixEnd_6311421 : Nat := 4983230072969 + 3 ^ 40 * 6311421 * 2
def baseEnd_6311421 : Nat := 3240792585880456270011809

theorem tailTrace_6311421 : CollatzResearch.WordTrace tailWord_6311421 prefixEnd_6311421 3240792585880456270011809 := by
  unfold tailWord_6311421
  simp only [CollatzResearch.WordTrace]
  refine ⟨230196435267807096735518117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153464290178538064490345411 230196435267807096735518117)
  ·
    refine ⟨43161831612713830637909647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230196435267807096735518117 43161831612713830637909647)
    ·
      refine ⟨64742747419070745956864471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43161831612713830637909647 64742747419070745956864471)
      ·
        refine ⟨97114121128606118935296707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64742747419070745956864471 97114121128606118935296707)
        ·
          refine ⟨145671181692909178402945061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97114121128606118935296707 145671181692909178402945061)
          ·
            refine ⟨27313346567420470950552199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145671181692909178402945061 27313346567420470950552199)
            ·
              refine ⟨40970019851130706425828299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27313346567420470950552199 40970019851130706425828299)
              ·
                refine ⟨61455029776696059638742449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40970019851130706425828299 61455029776696059638742449)
                ·
                  refine ⟨46091272332522044729056837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61455029776696059638742449 46091272332522044729056837)
                  ·
                    refine ⟨8642113562347883386698157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46091272332522044729056837 8642113562347883386698157)
                    ·
                      refine ⟨3240792585880456270011809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642113562347883386698157 3240792585880456270011809)
                      ·
                        rfl

theorem cell23_6311421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_6311421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311421 prefixEnd_6311421 := by exact prefixLift 6311421
  have htrace : WordTrace (prefixWord ++ tailWord_6311421) baseStart_6311421 baseEnd_6311421 := by
    simpa [prefixWord, tailWord_6311421, baseEnd_6311421] using wordTrace_append hprefix tailTrace_6311421
  have hstable : (prefixWord ++ tailWord_6311421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311421).length < 2 ^ (prefixWord ++ tailWord_6311421).sum := by decide
  have hdescent : baseEnd_6311421 < baseStart_6311421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311428 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_6311428 : Nat := 118140960795 + 6311428 * 2 ^ 59
def prefixEnd_6311428 : Nat := 4983230072969 + 3 ^ 40 * 6311428 * 2
def baseEnd_6311428 : Nat := 1080265393415012580874759

theorem tailTrace_6311428 : CollatzResearch.WordTrace tailWord_6311428 prefixEnd_6311428 1080265393415012580874759 := by
  unfold tailWord_6311428
  simp only [CollatzResearch.WordTrace]
  refine ⟨115098345289390868465511469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153464460385854491287348625 115098345289390868465511469)
  ·
    refine ⟨43161879483521575674566801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115098345289390868465511469 43161879483521575674566801)
    ·
      refine ⟨32371409612641181755925101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43161879483521575674566801 32371409612641181755925101)
      ·
        refine ⟨12139278604740443158471913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32371409612641181755925101 12139278604740443158471913)
        ·
          refine ⟨9104458953555332368853935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12139278604740443158471913 9104458953555332368853935)
          ·
            refine ⟨13656688430332998553280903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104458953555332368853935 13656688430332998553280903)
            ·
              refine ⟨20485032645499497829921355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13656688430332998553280903 20485032645499497829921355)
              ·
                refine ⟨30727548968249246744882033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20485032645499497829921355 30727548968249246744882033)
                ·
                  refine ⟨23045661726186935058661525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30727548968249246744882033 23045661726186935058661525)
                  ·
                    refine ⟨1080265393415012580874759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23045661726186935058661525 1080265393415012580874759)
                    ·
                      rfl

theorem cell23_6311428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_6311428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311428 prefixEnd_6311428 := by exact prefixLift 6311428
  have htrace : WordTrace (prefixWord ++ tailWord_6311428) baseStart_6311428 baseEnd_6311428 := by
    simpa [prefixWord, tailWord_6311428, baseEnd_6311428] using wordTrace_append hprefix tailTrace_6311428
  have hstable : (prefixWord ++ tailWord_6311428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311428).length < 2 ^ (prefixWord ++ tailWord_6311428).sum := by decide
  have hdescent : baseEnd_6311428 < baseStart_6311428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311431 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6311431 : Nat := 118140960795 + 6311431 * 2 ^ 59
def prefixEnd_6311431 : Nat := 4983230072969 + 3 ^ 40 * 6311431 * 2
def baseEnd_6311431 : Nat := 3240797720687001230886763

theorem tailTrace_6311431 : CollatzResearch.WordTrace tailWord_6311431 prefixEnd_6311431 3240797720687001230886763 := by
  unfold tailWord_6311431
  simp only [CollatzResearch.WordTrace]
  refine ⟨230196799997770868443382147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153464533331847245628921431 230196799997770868443382147)
  ·
    refine ⟨345295199996656302665073221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230196799997770868443382147 345295199996656302665073221)
    ·
      refine ⟨64742849999373056749701229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345295199996656302665073221 64742849999373056749701229)
      ·
        refine ⟨24278568749764896281137961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64742849999373056749701229 24278568749764896281137961)
        ·
          refine ⟨18208926562323672210853471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24278568749764896281137961 18208926562323672210853471)
          ·
            refine ⟨27313389843485508316280207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18208926562323672210853471 27313389843485508316280207)
            ·
              refine ⟨40970084765228262474420311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27313389843485508316280207 40970084765228262474420311)
              ·
                refine ⟨61455127147842393711630467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40970084765228262474420311 61455127147842393711630467)
                ·
                  refine ⟨92182690721763590567445701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61455127147842393711630467 92182690721763590567445701)
                  ·
                    refine ⟨17284254510330673231396069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92182690721763590567445701 17284254510330673231396069)
                    ·
                      refine ⟨3240797720687001230886763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17284254510330673231396069 3240797720687001230886763)
                      ·
                        rfl

theorem cell23_6311431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6311431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311431 prefixEnd_6311431 := by exact prefixLift 6311431
  have htrace : WordTrace (prefixWord ++ tailWord_6311431) baseStart_6311431 baseEnd_6311431 := by
    simpa [prefixWord, tailWord_6311431, baseEnd_6311431] using wordTrace_append hprefix tailTrace_6311431
  have hstable : (prefixWord ++ tailWord_6311431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311431).length < 2 ^ (prefixWord ++ tailWord_6311431).sum := by decide
  have hdescent : baseEnd_6311431 < baseStart_6311431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311435 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 4, 2]
def baseStart_6311435 : Nat := 118140960795 + 6311435 * 2 ^ 59
def prefixEnd_6311435 : Nat := 4983230072969 + 3 ^ 40 * 6311435 * 2
def baseEnd_6311435 : Nat := 3240799774609619215236745

theorem tailTrace_6311435 : CollatzResearch.WordTrace tailWord_6311435 prefixEnd_6311435 3240799774609619215236745 := by
  unfold tailWord_6311435
  simp only [CollatzResearch.WordTrace]
  refine ⟨230196945889756377126527759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153464630593170918084351839 230196945889756377126527759)
  ·
    refine ⟨345295418834634565689791639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230196945889756377126527759 345295418834634565689791639)
    ·
      refine ⟨517943128251951848534687459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345295418834634565689791639 517943128251951848534687459)
      ·
        refine ⟨776914692377927772802031189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517943128251951848534687459 776914692377927772802031189)
        ·
          refine ⟨9104469051303841087523803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 776914692377927772802031189 9104469051303841087523803)
          ·
            refine ⟨13656703576955761631285705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104469051303841087523803 13656703576955761631285705)
            ·
              refine ⟨10242527682716821223464279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13656703576955761631285705 10242527682716821223464279)
              ·
                refine ⟨15363791524075231835196419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242527682716821223464279 15363791524075231835196419)
                ·
                  refine ⟨23045687286112847752794629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15363791524075231835196419 23045687286112847752794629)
                  ·
                    refine ⟨4321066366146158953648993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23045687286112847752794629 4321066366146158953648993)
                    ·
                      refine ⟨3240799774609619215236745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321066366146158953648993 3240799774609619215236745)
                      ·
                        rfl

theorem cell23_6311435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4, 2].length) (baseStart_6311435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311435 prefixEnd_6311435 := by exact prefixLift 6311435
  have htrace : WordTrace (prefixWord ++ tailWord_6311435) baseStart_6311435 baseEnd_6311435 := by
    simpa [prefixWord, tailWord_6311435, baseEnd_6311435] using wordTrace_append hprefix tailTrace_6311435
  have hstable : (prefixWord ++ tailWord_6311435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311435).length < 2 ^ (prefixWord ++ tailWord_6311435).sum := by decide
  have hdescent : baseEnd_6311435 < baseStart_6311435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311458 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_6311458 : Nat := 118140960795 + 6311458 * 2 ^ 59
def prefixEnd_6311458 : Nat := 4983230072969 + 3 ^ 40 * 6311458 * 2
def baseEnd_6311458 : Nat := 360090176073852513916571

theorem tailTrace_6311458 : CollatzResearch.WordTrace tailWord_6311458 prefixEnd_6311458 360090176073852513916571 := by
  unfold tailWord_6311458
  simp only [CollatzResearch.WordTrace]
  refine ⟨57549446192168263013653757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153465189845782034703076685 57549446192168263013653757)
  ·
    refine ⟨21581042322063098630120159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57549446192168263013653757 21581042322063098630120159)
    ·
      refine ⟨32371563483094647945180239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21581042322063098630120159 32371563483094647945180239)
      ·
        refine ⟨48557345224641971917770359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32371563483094647945180239 48557345224641971917770359)
        ·
          refine ⟨72836017836962957876655539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48557345224641971917770359 72836017836962957876655539)
          ·
            refine ⟨109254026755444436814983309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72836017836962957876655539 109254026755444436814983309)
            ·
              refine ⟨40970260033291663805618741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109254026755444436814983309 40970260033291663805618741)
              ·
                refine ⟨3840961878121093481776757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40970260033291663805618741 3840961878121093481776757)
                ·
                  refine ⟨360090176073852513916571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840961878121093481776757 360090176073852513916571)
                  ·
                    rfl

theorem cell23_6311458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_6311458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311458 prefixEnd_6311458 := by exact prefixLift 6311458
  have htrace : WordTrace (prefixWord ++ tailWord_6311458) baseStart_6311458 baseEnd_6311458 := by
    simpa [prefixWord, tailWord_6311458, baseEnd_6311458] using wordTrace_append hprefix tailTrace_6311458
  have hstable : (prefixWord ++ tailWord_6311458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311458).length < 2 ^ (prefixWord ++ tailWord_6311458).sum := by decide
  have hdescent : baseEnd_6311458 < baseStart_6311458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311508 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6311508 : Nat := 118140960795 + 6311508 * 2 ^ 59
def prefixEnd_6311508 : Nat := 4983230072969 + 3 ^ 40 * 6311508 * 2
def baseEnd_6311508 : Nat := 3240837258697397429623909

theorem tailTrace_6311508 : CollatzResearch.WordTrace tailWord_6311508 prefixEnd_6311508 3240837258697397429623909 := by
  unfold tailWord_6311508
  simp only [CollatzResearch.WordTrace]
  refine ⟨115099804209245955296967589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153466405612327940395956785 115099804209245955296967589)
  ·
    refine ⟨21581213289233616618181423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115099804209245955296967589 21581213289233616618181423)
    ·
      refine ⟨32371819933850424927272135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21581213289233616618181423 32371819933850424927272135)
      ·
        refine ⟨48557729900775637390908203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32371819933850424927272135 48557729900775637390908203)
        ·
          refine ⟨72836594851163456086362305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48557729900775637390908203 72836594851163456086362305)
          ·
            refine ⟨54627446138372592064771729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72836594851163456086362305 54627446138372592064771729)
            ·
              refine ⟨40970584603779444048578797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54627446138372592064771729 40970584603779444048578797)
              ·
                refine ⟨15363969226417291518217049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40970584603779444048578797 15363969226417291518217049)
                ·
                  refine ⟨11522976919812968638662787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15363969226417291518217049 11522976919812968638662787)
                  ·
                    refine ⟨17284465379719452957994181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11522976919812968638662787 17284465379719452957994181)
                    ·
                      refine ⟨3240837258697397429623909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17284465379719452957994181 3240837258697397429623909)
                      ·
                        rfl

theorem cell23_6311508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6311508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311508 prefixEnd_6311508 := by exact prefixLift 6311508
  have htrace : WordTrace (prefixWord ++ tailWord_6311508) baseStart_6311508 baseEnd_6311508 := by
    simpa [prefixWord, tailWord_6311508, baseEnd_6311508] using wordTrace_append hprefix tailTrace_6311508
  have hstable : (prefixWord ++ tailWord_6311508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311508).length < 2 ^ (prefixWord ++ tailWord_6311508).sum := by decide
  have hdescent : baseEnd_6311508 < baseStart_6311508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311568 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2]
def baseStart_6311568 : Nat := 118140960795 + 6311568 * 2 ^ 59
def prefixEnd_6311568 : Nat := 4983230072969 + 3 ^ 40 * 6311568 * 2
def baseEnd_6311568 : Nat := 3240868067536667194873633

theorem tailTrace_6311568 : CollatzResearch.WordTrace tailWord_6311568 prefixEnd_6311568 3240868067536667194873633 := by
  unfold tailWord_6311568
  simp only [CollatzResearch.WordTrace]
  refine ⟨115100898399137270420559679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153467864532183027227412905 115100898399137270420559679)
  ·
    refine ⟨172651347598705905630839519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115100898399137270420559679 172651347598705905630839519)
    ·
      refine ⟨258977021398058858446259279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172651347598705905630839519 258977021398058858446259279)
      ·
        refine ⟨388465532097088287669388919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258977021398058858446259279 388465532097088287669388919)
        ·
          refine ⟨582698298145632431504083379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388465532097088287669388919 582698298145632431504083379)
          ·
            refine ⟨874047447218448647256125069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582698298145632431504083379 874047447218448647256125069)
            ·
              refine ⟨327767792706918242721046901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874047447218448647256125069 327767792706918242721046901)
              ·
                refine ⟨30728230566273585255098147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327767792706918242721046901 30728230566273585255098147)
                ·
                  refine ⟨46092345849410377882647221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30728230566273585255098147 46092345849410377882647221)
                  ·
                    refine ⟨4321157423382222926498177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46092345849410377882647221 4321157423382222926498177)
                    ·
                      refine ⟨3240868067536667194873633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321157423382222926498177 3240868067536667194873633)
                      ·
                        rfl

theorem cell23_6311568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2].length) (baseStart_6311568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311568 prefixEnd_6311568 := by exact prefixLift 6311568
  have htrace : WordTrace (prefixWord ++ tailWord_6311568) baseStart_6311568 baseEnd_6311568 := by
    simpa [prefixWord, tailWord_6311568, baseEnd_6311568] using wordTrace_append hprefix tailTrace_6311568
  have hstable : (prefixWord ++ tailWord_6311568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311568).length < 2 ^ (prefixWord ++ tailWord_6311568).sum := by decide
  have hdescent : baseEnd_6311568 < baseStart_6311568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311611 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_6311611 : Nat := 118140960795 + 6311611 * 2 ^ 59
def prefixEnd_6311611 : Nat := 4983230072969 + 3 ^ 40 * 6311611 * 2
def baseEnd_6311611 : Nat := 3240890147204810526635935

theorem tailTrace_6311611 : CollatzResearch.WordTrace tailWord_6311611 prefixEnd_6311611 3240890147204810526635935 := by
  unfold tailWord_6311611
  simp only [CollatzResearch.WordTrace]
  refine ⟨230203365137118759184934687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153468910091412506123289791 230203365137118759184934687)
  ·
    refine ⟨345305047705678138777402031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230203365137118759184934687 345305047705678138777402031)
    ·
      refine ⟨517957571558517208166103047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345305047705678138777402031 517957571558517208166103047)
      ·
        refine ⟨776936357337775812249154571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517957571558517208166103047 776936357337775812249154571)
        ·
          refine ⟨1165404536006663718373731857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776936357337775812249154571 1165404536006663718373731857)
          ·
            refine ⟨874053402004997788780298893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165404536006663718373731857 874053402004997788780298893)
            ·
              refine ⟨327770025751874170792612085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874053402004997788780298893 327770025751874170792612085)
              ·
                refine ⟨30728439914238203511807383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327770025751874170792612085 30728439914238203511807383)
                ·
                  refine ⟨46092659871357305267711075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30728439914238203511807383 46092659871357305267711075)
                  ·
                    refine ⟨69138989807035957901566613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46092659871357305267711075 69138989807035957901566613)
                    ·
                      refine ⟨3240890147204810526635935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69138989807035957901566613 3240890147204810526635935)
                      ·
                        rfl

theorem cell23_6311611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_6311611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311611 prefixEnd_6311611 := by exact prefixLift 6311611
  have htrace : WordTrace (prefixWord ++ tailWord_6311611) baseStart_6311611 baseEnd_6311611 := by
    simpa [prefixWord, tailWord_6311611, baseEnd_6311611] using wordTrace_append hprefix tailTrace_6311611
  have hstable : (prefixWord ++ tailWord_6311611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311611).length < 2 ^ (prefixWord ++ tailWord_6311611).sum := by decide
  have hdescent : baseEnd_6311611 < baseStart_6311611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311629 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6311629 : Nat := 118140960795 + 6311629 * 2 ^ 59
def prefixEnd_6311629 : Nat := 4983230072969 + 3 ^ 40 * 6311629 * 2
def baseEnd_6311629 : Nat := 1080299796618863818736951

theorem tailTrace_6311629 : CollatzResearch.WordTrace tailWord_6311629 prefixEnd_6311629 1080299796618863818736951 := by
  unfold tailWord_6311629
  simp only [CollatzResearch.WordTrace]
  refine ⟨230204021651053548259089941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153469347767369032172726627 230204021651053548259089941)
  ·
    refine ⟨10790813514893135074644841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230204021651053548259089941 10790813514893135074644841)
    ·
      refine ⟨8093110136169851305983631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10790813514893135074644841 8093110136169851305983631)
      ·
        refine ⟨12139665204254776958975447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093110136169851305983631 12139665204254776958975447)
        ·
          refine ⟨18209497806382165438463171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12139665204254776958975447 18209497806382165438463171)
          ·
            refine ⟨27314246709573248157694757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18209497806382165438463171 27314246709573248157694757)
            ·
              refine ⟨5121421258044984029567767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27314246709573248157694757 5121421258044984029567767)
              ·
                refine ⟨7682131887067476044351651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121421258044984029567767 7682131887067476044351651)
                ·
                  refine ⟨11523197830601214066527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682131887067476044351651 11523197830601214066527477)
                  ·
                    refine ⟨1080299796618863818736951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11523197830601214066527477 1080299796618863818736951)
                    ·
                      rfl

theorem cell23_6311629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6311629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311629 prefixEnd_6311629 := by exact prefixLift 6311629
  have htrace : WordTrace (prefixWord ++ tailWord_6311629) baseStart_6311629 baseEnd_6311629 := by
    simpa [prefixWord, tailWord_6311629, baseEnd_6311629] using wordTrace_append hprefix tailTrace_6311629
  have hstable : (prefixWord ++ tailWord_6311629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311629).length < 2 ^ (prefixWord ++ tailWord_6311629).sum := by decide
  have hdescent : baseEnd_6311629 < baseStart_6311629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311642 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_6311642 : Nat := 118140960795 + 6311642 * 2 ^ 59
def prefixEnd_6311642 : Nat := 4983230072969 + 3 ^ 40 * 6311642 * 2
def baseEnd_6311642 : Nat := 1080302021701699968449431

theorem tailTrace_6311642 : CollatzResearch.WordTrace tailWord_6311642 prefixEnd_6311642 1080302021701699968449431 := by
  unfold tailWord_6311642
  simp only [CollatzResearch.WordTrace]
  refine ⟨57551123950001612869828295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153469663866670967652875453 57551123950001612869828295)
  ·
    refine ⟨86326685925002419304742443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57551123950001612869828295 86326685925002419304742443)
    ·
      refine ⟨129490028887503628957113665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86326685925002419304742443 129490028887503628957113665)
      ·
        refine ⟨97117521665627721717835249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129490028887503628957113665 97117521665627721717835249)
        ·
          refine ⟨72838141249220791288376437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97117521665627721717835249 72838141249220791288376437)
          ·
            refine ⟨6828575742114449183285291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72838141249220791288376437 6828575742114449183285291)
            ·
              refine ⟨10242863613171673774927937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828575742114449183285291 10242863613171673774927937)
              ·
                refine ⟨7682147709878755331195953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10242863613171673774927937 7682147709878755331195953)
                ·
                  refine ⟨5761610782409066498396965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682147709878755331195953 5761610782409066498396965)
                  ·
                    refine ⟨1080302021701699968449431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761610782409066498396965 1080302021701699968449431)
                    ·
                      rfl

theorem cell23_6311642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_6311642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311642 prefixEnd_6311642 := by exact prefixLift 6311642
  have htrace : WordTrace (prefixWord ++ tailWord_6311642) baseStart_6311642 baseEnd_6311642 := by
    simpa [prefixWord, tailWord_6311642, baseEnd_6311642] using wordTrace_append hprefix tailTrace_6311642
  have hstable : (prefixWord ++ tailWord_6311642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311642).length < 2 ^ (prefixWord ++ tailWord_6311642).sum := by decide
  have hdescent : baseEnd_6311642 < baseStart_6311642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311648 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_6311648 : Nat := 118140960795 + 6311648 * 2 ^ 59
def prefixEnd_6311648 : Nat := 4983230072969 + 3 ^ 40 * 6311648 * 2
def baseEnd_6311648 : Nat := 3240909145989026881873265

theorem tailTrace_6311648 : CollatzResearch.WordTrace tailWord_6311648 prefixEnd_6311648 3240909145989026881873265 := by
  unfold tailWord_6311648
  simp only [CollatzResearch.WordTrace]
  refine ⟨115102357318992357252015799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153469809758656476336021065 115102357318992357252015799)
  ·
    refine ⟨172653535978488535878023699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115102357318992357252015799 172653535978488535878023699)
    ·
      refine ⟨258980303967732803817035549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172653535978488535878023699 258980303967732803817035549)
      ·
        refine ⟨97117613987899801431388331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258980303967732803817035549 97117613987899801431388331)
        ·
          refine ⟨145676420981849702147082497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97117613987899801431388331 145676420981849702147082497)
          ·
            refine ⟨109257315736387276610311873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145676420981849702147082497 109257315736387276610311873)
            ·
              refine ⟨81942986802290457457733905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109257315736387276610311873 81942986802290457457733905)
              ·
                refine ⟨61457240101717843093300429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81942986802290457457733905 61457240101717843093300429)
                ·
                  refine ⟨23046465038144191159987661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61457240101717843093300429 23046465038144191159987661)
                  ·
                    refine ⟨8642424389304071684995373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23046465038144191159987661 8642424389304071684995373)
                    ·
                      refine ⟨3240909145989026881873265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642424389304071684995373 3240909145989026881873265)
                      ·
                        rfl

theorem cell23_6311648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_6311648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311648 prefixEnd_6311648 := by exact prefixLift 6311648
  have htrace : WordTrace (prefixWord ++ tailWord_6311648) baseStart_6311648 baseEnd_6311648 := by
    simpa [prefixWord, tailWord_6311648, baseEnd_6311648] using wordTrace_append hprefix tailTrace_6311648
  have hstable : (prefixWord ++ tailWord_6311648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311648).length < 2 ^ (prefixWord ++ tailWord_6311648).sum := by decide
  have hdescent : baseEnd_6311648 < baseStart_6311648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311649 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_6311649 : Nat := 118140960795 + 6311649 * 2 ^ 59
def prefixEnd_6311649 : Nat := 4983230072969 + 3 ^ 40 * 6311649 * 2
def baseEnd_6311649 : Nat := 3240909659469681377960761

theorem tailTrace_6311649 : CollatzResearch.WordTrace tailWord_6311649 prefixEnd_6311649 3240909659469681377960761 := by
  unfold tailWord_6311649
  simp only [CollatzResearch.WordTrace]
  refine ⟨230204751110981091674818001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153469834073987394449878667 230204751110981091674818001)
  ·
    refine ⟨172653563333235818756113501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230204751110981091674818001 172653563333235818756113501)
    ·
      refine ⟨64745086249963432033542563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172653563333235818756113501 64745086249963432033542563)
      ·
        refine ⟨97117629374945148050313845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64745086249963432033542563 97117629374945148050313845)
        ·
          refine ⟨9104777753901107629716923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97117629374945148050313845 9104777753901107629716923)
          ·
            refine ⟨13657166630851661444575385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104777753901107629716923 13657166630851661444575385)
            ·
              refine ⟨10242874973138746083431539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13657166630851661444575385 10242874973138746083431539)
              ·
                refine ⟨15364312459708119125147309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242874973138746083431539 15364312459708119125147309)
                ·
                  refine ⟨5761617172390544671930241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15364312459708119125147309 5761617172390544671930241)
                  ·
                    refine ⟨4321212879292908503947681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5761617172390544671930241 4321212879292908503947681)
                    ·
                      refine ⟨3240909659469681377960761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321212879292908503947681 3240909659469681377960761)
                      ·
                        rfl

theorem cell23_6311649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_6311649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311649 prefixEnd_6311649 := by exact prefixLift 6311649
  have htrace : WordTrace (prefixWord ++ tailWord_6311649) baseStart_6311649 baseEnd_6311649 := by
    simpa [prefixWord, tailWord_6311649, baseEnd_6311649] using wordTrace_append hprefix tailTrace_6311649
  have hstable : (prefixWord ++ tailWord_6311649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311649).length < 2 ^ (prefixWord ++ tailWord_6311649).sum := by decide
  have hdescent : baseEnd_6311649 < baseStart_6311649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311665 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_6311665 : Nat := 118140960795 + 6311665 * 2 ^ 59
def prefixEnd_6311665 : Nat := 4983230072969 + 3 ^ 40 * 6311665 * 2
def baseEnd_6311665 : Nat := 3240917875160153315360687

theorem tailTrace_6311665 : CollatzResearch.WordTrace tailWord_6311665 prefixEnd_6311665 3240917875160153315360687 := by
  unfold tailWord_6311665
  simp only [CollatzResearch.WordTrace]
  refine ⟨230205334678923126407400449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153470223119282084271600299 230205334678923126407400449)
  ·
    refine ⟨172654001009192344805550337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230205334678923126407400449 172654001009192344805550337)
    ·
      refine ⟨129490500756894258604162753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172654001009192344805550337 129490500756894258604162753)
      ·
        refine ⟨97117875567670693953122065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129490500756894258604162753 97117875567670693953122065)
        ·
          refine ⟨72838406675753020464841549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97117875567670693953122065 72838406675753020464841549)
          ·
            refine ⟨27314402503407382674315581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72838406675753020464841549 27314402503407382674315581)
            ·
              refine ⟨10242900938777768502868343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27314402503407382674315581 10242900938777768502868343)
              ·
                refine ⟨15364351408166652754302515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242900938777768502868343 15364351408166652754302515)
                ·
                  refine ⟨23046527112249979131453773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15364351408166652754302515 23046527112249979131453773)
                  ·
                    refine ⟨8642447667093742174295165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23046527112249979131453773 8642447667093742174295165)
                    ·
                      refine ⟨3240917875160153315360687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642447667093742174295165 3240917875160153315360687)
                      ·
                        rfl

theorem cell23_6311665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_6311665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311665 prefixEnd_6311665 := by exact prefixLift 6311665
  have htrace : WordTrace (prefixWord ++ tailWord_6311665) baseStart_6311665 baseEnd_6311665 := by
    simpa [prefixWord, tailWord_6311665, baseEnd_6311665] using wordTrace_append hprefix tailTrace_6311665
  have hstable : (prefixWord ++ tailWord_6311665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311665).length < 2 ^ (prefixWord ++ tailWord_6311665).sum := by decide
  have hdescent : baseEnd_6311665 < baseStart_6311665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311682 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6311682 : Nat := 118140960795 + 6311682 * 2 ^ 59
def prefixEnd_6311682 : Nat := 4983230072969 + 3 ^ 40 * 6311682 * 2
def baseEnd_6311682 : Nat := 3240926604331279748848109

theorem tailTrace_6311682 : CollatzResearch.WordTrace tailWord_6311682 prefixEnd_6311682 3240926604331279748848109 := by
  unfold tailWord_6311682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57551488679965384577692325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153470636479907692207179533 57551488679965384577692325)
  ·
    refine ⟨10790904127493509608317311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57551488679965384577692325 10790904127493509608317311)
    ·
      refine ⟨16186356191240264412475967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790904127493509608317311 16186356191240264412475967)
      ·
        refine ⟨24279534286860396618713951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16186356191240264412475967 24279534286860396618713951)
        ·
          refine ⟨36419301430290594928070927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24279534286860396618713951 36419301430290594928070927)
          ·
            refine ⟨54628952145435892392106391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36419301430290594928070927 54628952145435892392106391)
            ·
              refine ⟨81943428218153838588159587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54628952145435892392106391 81943428218153838588159587)
              ·
                refine ⟨122915142327230757882239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81943428218153838588159587 122915142327230757882239381)
                ·
                  refine ⟨5761647296588941775729971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122915142327230757882239381 5761647296588941775729971)
                  ·
                    refine ⟨8642470944883412663594957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761647296588941775729971 8642470944883412663594957)
                    ·
                      refine ⟨3240926604331279748848109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642470944883412663594957 3240926604331279748848109)
                      ·
                        rfl

theorem cell23_6311682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6311682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311682 prefixEnd_6311682 := by exact prefixLift 6311682
  have htrace : WordTrace (prefixWord ++ tailWord_6311682) baseStart_6311682 baseEnd_6311682 := by
    simpa [prefixWord, tailWord_6311682, baseEnd_6311682] using wordTrace_append hprefix tailTrace_6311682
  have hstable : (prefixWord ++ tailWord_6311682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311682).length < 2 ^ (prefixWord ++ tailWord_6311682).sum := by decide
  have hdescent : baseEnd_6311682 < baseStart_6311682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311692 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_6311692 : Nat := 118140960795 + 6311692 * 2 ^ 59
def prefixEnd_6311692 : Nat := 4983230072969 + 3 ^ 40 * 6311692 * 2
def baseEnd_6311692 : Nat := 3240931739137824709723063

theorem tailTrace_6311692 : CollatzResearch.WordTrace tailWord_6311692 prefixEnd_6311692 3240931739137824709723063 := by
  unfold tailWord_6311692
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103159724912655009316665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153470879633216873345755553 115103159724912655009316665)
  ·
    refine ⟨86327369793684491256987499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115103159724912655009316665 86327369793684491256987499)
    ·
      refine ⟨129491054690526736885481249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86327369793684491256987499 129491054690526736885481249)
      ·
        refine ⟨97118291017895052664110937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129491054690526736885481249 97118291017895052664110937)
        ·
          refine ⟨72838718263421289498083203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97118291017895052664110937 72838718263421289498083203)
          ·
            refine ⟨109258077395131934247124805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72838718263421289498083203 109258077395131934247124805)
            ·
              refine ⟨20485889511587237671335901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109258077395131934247124805 20485889511587237671335901)
              ·
                refine ⟨7682208566845214126750963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20485889511587237671335901 7682208566845214126750963)
                ·
                  refine ⟨11523312850267821190126445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682208566845214126750963 11523312850267821190126445)
                  ·
                    refine ⟨4321242318850432946297417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11523312850267821190126445 4321242318850432946297417)
                    ·
                      refine ⟨3240931739137824709723063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321242318850432946297417 3240931739137824709723063)
                      ·
                        rfl

theorem cell23_6311692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_6311692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311692 prefixEnd_6311692 := by exact prefixLift 6311692
  have htrace : WordTrace (prefixWord ++ tailWord_6311692) baseStart_6311692 baseEnd_6311692 := by
    simpa [prefixWord, tailWord_6311692, baseEnd_6311692] using wordTrace_append hprefix tailTrace_6311692
  have hstable : (prefixWord ++ tailWord_6311692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311692).length < 2 ^ (prefixWord ++ tailWord_6311692).sum := by decide
  have hdescent : baseEnd_6311692 < baseStart_6311692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311700 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6311700 : Nat := 118140960795 + 6311700 * 2 ^ 59
def prefixEnd_6311700 : Nat := 4983230072969 + 3 ^ 40 * 6311700 * 2
def baseEnd_6311700 : Nat := 3240935846983060678423027

theorem tailTrace_6311700 : CollatzResearch.WordTrace tailWord_6311700 prefixEnd_6311700 3240935846983060678423027 := by
  unfold tailWord_6311700
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103305616898163692462277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153471074155864218256616369 115103305616898163692462277)
  ·
    refine ⟨21581869803168405692336677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115103305616898163692462277 21581869803168405692336677)
    ·
      refine ⟨4046600588094076067313127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21581869803168405692336677 4046600588094076067313127)
      ·
        refine ⟨6069900882141114100969691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046600588094076067313127 6069900882141114100969691)
        ·
          refine ⟨9104851323211671151454537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069900882141114100969691 9104851323211671151454537)
          ·
            refine ⟨6828638492408753363590903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9104851323211671151454537 6828638492408753363590903)
            ·
              refine ⟨10242957738613130045386355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828638492408753363590903 10242957738613130045386355)
              ·
                refine ⟨15364436607919695068079533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242957738613130045386355 15364436607919695068079533)
                ·
                  refine ⟨5761663727969885650529825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15364436607919695068079533 5761663727969885650529825)
                  ·
                    refine ⟨4321247795977414237897369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5761663727969885650529825 4321247795977414237897369)
                    ·
                      refine ⟨3240935846983060678423027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321247795977414237897369 3240935846983060678423027)
                      ·
                        rfl

theorem cell23_6311700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6311700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311700 prefixEnd_6311700 := by exact prefixLift 6311700
  have htrace : WordTrace (prefixWord ++ tailWord_6311700) baseStart_6311700 baseEnd_6311700 := by
    simpa [prefixWord, tailWord_6311700, baseEnd_6311700] using wordTrace_append hprefix tailTrace_6311700
  have hstable : (prefixWord ++ tailWord_6311700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311700).length < 2 ^ (prefixWord ++ tailWord_6311700).sum := by decide
  have hdescent : baseEnd_6311700 < baseStart_6311700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311708 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6311708 : Nat := 118140960795 + 6311708 * 2 ^ 59
def prefixEnd_6311708 : Nat := 4983230072969 + 3 ^ 40 * 6311708 * 2
def baseEnd_6311708 : Nat := 3240939954828296647122989

theorem tailTrace_6311708 : CollatzResearch.WordTrace tailWord_6311708 prefixEnd_6311708 3240939954828296647122989 := by
  unfold tailWord_6311708
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103451508883672375607889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153471268678511563167477185 115103451508883672375607889)
  ·
    refine ⟨86327588631662754281705917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115103451508883672375607889 86327588631662754281705917)
    ·
      refine ⟨32372845736873532855639719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86327588631662754281705917 32372845736873532855639719)
      ·
        refine ⟨48559268605310299283459579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32372845736873532855639719 48559268605310299283459579)
        ·
          refine ⟨72838902907965448925189369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48559268605310299283459579 72838902907965448925189369)
          ·
            refine ⟨54629177180974086693892027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72838902907965448925189369 54629177180974086693892027)
            ·
              refine ⟨81943765771461130040838041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54629177180974086693892027 81943765771461130040838041)
              ·
                refine ⟨61457824328595847530628531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81943765771461130040838041 61457824328595847530628531)
                ·
                  refine ⟨92186736492893771295942797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61457824328595847530628531 92186736492893771295942797)
                  ·
                    refine ⟨34570026184835164235978549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92186736492893771295942797 34570026184835164235978549)
                    ·
                      refine ⟨3240939954828296647122989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34570026184835164235978549 3240939954828296647122989)
                      ·
                        rfl

theorem cell23_6311708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6311708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311708 prefixEnd_6311708 := by exact prefixLift 6311708
  have htrace : WordTrace (prefixWord ++ tailWord_6311708) baseStart_6311708 baseEnd_6311708 := by
    simpa [prefixWord, tailWord_6311708, baseEnd_6311708] using wordTrace_append hprefix tailTrace_6311708
  have hstable : (prefixWord ++ tailWord_6311708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311708).length < 2 ^ (prefixWord ++ tailWord_6311708).sum := by decide
  have hdescent : baseEnd_6311708 < baseStart_6311708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311710 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6311710 : Nat := 118140960795 + 6311710 * 2 ^ 59
def prefixEnd_6311710 : Nat := 4983230072969 + 3 ^ 40 * 6311710 * 2
def baseEnd_6311710 : Nat := 1080313660596535213099327

theorem tailTrace_6311710 : CollatzResearch.WordTrace tailWord_6311710 prefixEnd_6311710 1080313660596535213099327 := by
  unfold tailWord_6311710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775871995470012386598573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153471317309173399395192389 28775871995470012386598573)
  ·
    refine ⟨10790951998301254644974465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28775871995470012386598573 10790951998301254644974465)
    ·
      refine ⟨8093213998725940983730849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10790951998301254644974465 8093213998725940983730849)
      ·
        refine ⟨6069910499044455737798137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8093213998725940983730849 6069910499044455737798137)
        ·
          refine ⟨4552432874283341803348603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6069910499044455737798137 4552432874283341803348603)
          ·
            refine ⟨6828649311425012705022905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552432874283341803348603 6828649311425012705022905)
            ·
              refine ⟨5121486983568759528767179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828649311425012705022905 5121486983568759528767179)
              ·
                refine ⟨7682230475353139293150769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121486983568759528767179 7682230475353139293150769)
                ·
                  refine ⟨5761672856514854469863077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682230475353139293150769 5761672856514854469863077)
                  ·
                    refine ⟨1080313660596535213099327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761672856514854469863077 1080313660596535213099327)
                    ·
                      rfl

theorem cell23_6311710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6311710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311710 prefixEnd_6311710 := by exact prefixLift 6311710
  have htrace : WordTrace (prefixWord ++ tailWord_6311710) baseStart_6311710 baseEnd_6311710 := by
    simpa [prefixWord, tailWord_6311710, baseEnd_6311710] using wordTrace_append hprefix tailTrace_6311710
  have hstable : (prefixWord ++ tailWord_6311710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311710).length < 2 ^ (prefixWord ++ tailWord_6311710).sum := by decide
  have hdescent : baseEnd_6311710 < baseStart_6311710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311716 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_6311716 : Nat := 118140960795 + 6311716 * 2 ^ 59
def prefixEnd_6311716 : Nat := 4983230072969 + 3 ^ 40 * 6311716 * 2
def baseEnd_6311716 : Nat := 3240944062673532615822953

theorem tailTrace_6311716 : CollatzResearch.WordTrace tailWord_6311716 prefixEnd_6311716 3240944062673532615822953 := by
  unfold tailWord_6311716
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103597400869181058753501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153471463201158908078338001 115103597400869181058753501)
  ·
    refine ⟨43163849025325942897032563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115103597400869181058753501 43163849025325942897032563)
    ·
      refine ⟨64745773537988914345548845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43163849025325942897032563 64745773537988914345548845)
      ·
        refine ⟨24279665076745842879580817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64745773537988914345548845 24279665076745842879580817)
        ·
          refine ⟨18209748807559382159685613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24279665076745842879580817 18209748807559382159685613)
          ·
            refine ⟨6828655802834768309882105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18209748807559382159685613 6828655802834768309882105)
            ·
              refine ⟨5121491852126076232411579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828655802834768309882105 5121491852126076232411579)
              ·
                refine ⟨7682237778189114348617369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121491852126076232411579 7682237778189114348617369)
                ·
                  refine ⟨5761678333641835761463027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682237778189114348617369 5761678333641835761463027)
                  ·
                    refine ⟨8642517500462753642194541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761678333641835761463027 8642517500462753642194541)
                    ·
                      refine ⟨3240944062673532615822953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642517500462753642194541 3240944062673532615822953)
                      ·
                        rfl

theorem cell23_6311716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_6311716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311716 prefixEnd_6311716 := by exact prefixLift 6311716
  have htrace : WordTrace (prefixWord ++ tailWord_6311716) baseStart_6311716 baseEnd_6311716 := by
    simpa [prefixWord, tailWord_6311716, baseEnd_6311716] using wordTrace_append hprefix tailTrace_6311716
  have hstable : (prefixWord ++ tailWord_6311716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311716).length < 2 ^ (prefixWord ++ tailWord_6311716).sum := by decide
  have hdescent : baseEnd_6311716 < baseStart_6311716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311756 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6311756 : Nat := 118140960795 + 6311756 * 2 ^ 59
def prefixEnd_6311756 : Nat := 4983230072969 + 3 ^ 40 * 6311756 * 2
def baseEnd_6311756 : Nat := 3240964601899712459322769

theorem tailTrace_6311756 : CollatzResearch.WordTrace tailWord_6311756 prefixEnd_6311756 3240964601899712459322769 := by
  unfold tailWord_6311756
  simp only [CollatzResearch.WordTrace]
  refine ⟨115104326860796724474481561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153472435814395632632642081 115104326860796724474481561)
  ·
    refine ⟨86328245145597543355861171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115104326860796724474481561 86328245145597543355861171)
    ·
      refine ⟨129492367718396315033791757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86328245145597543355861171 129492367718396315033791757)
      ·
        refine ⟨48559637894398618137671909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129492367718396315033791757 48559637894398618137671909)
        ·
          refine ⟨9104932105199740900813483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48559637894398618137671909 9104932105199740900813483)
          ·
            refine ⟨13657398157799611351220225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104932105199740900813483 13657398157799611351220225)
            ·
              refine ⟨10243048618349708513415169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13657398157799611351220225 10243048618349708513415169)
              ·
                refine ⟨7682286463762281385061377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243048618349708513415169 7682286463762281385061377)
                ·
                  refine ⟨5761714847821711038796033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682286463762281385061377 5761714847821711038796033)
                  ·
                    refine ⟨4321286135866283279097025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5761714847821711038796033 4321286135866283279097025)
                    ·
                      refine ⟨3240964601899712459322769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321286135866283279097025 3240964601899712459322769)
                      ·
                        rfl

theorem cell23_6311756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6311756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311756 prefixEnd_6311756 := by exact prefixLift 6311756
  have htrace : WordTrace (prefixWord ++ tailWord_6311756) baseStart_6311756 baseEnd_6311756 := by
    simpa [prefixWord, tailWord_6311756, baseEnd_6311756] using wordTrace_append hprefix tailTrace_6311756
  have hstable : (prefixWord ++ tailWord_6311756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311756).length < 2 ^ (prefixWord ++ tailWord_6311756).sum := by decide
  have hdescent : baseEnd_6311756 < baseStart_6311756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311758 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_6311758 : Nat := 118140960795 + 6311758 * 2 ^ 59
def prefixEnd_6311758 : Nat := 4983230072969 + 3 ^ 40 * 6311758 * 2
def baseEnd_6311758 : Nat := 1080321876287007150499253

theorem tailTrace_6311758 : CollatzResearch.WordTrace tailWord_6311758 prefixEnd_6311758 1080321876287007150499253 := by
  unfold tailWord_6311758
  simp only [CollatzResearch.WordTrace]
  refine ⟨28776090833448275411316991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153472484445057468860357285 28776090833448275411316991)
  ·
    refine ⟨43164136250172413116975487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28776090833448275411316991 43164136250172413116975487)
    ·
      refine ⟨64746204375258619675463231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43164136250172413116975487 64746204375258619675463231)
      ·
        refine ⟨97119306562887929513194847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64746204375258619675463231 97119306562887929513194847)
        ·
          refine ⟨145678959844331894269792271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97119306562887929513194847 145678959844331894269792271)
          ·
            refine ⟨218518439766497841404688407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145678959844331894269792271 218518439766497841404688407)
            ·
              refine ⟨327777659649746762107032611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218518439766497841404688407 327777659649746762107032611)
              ·
                refine ⟨491666489474620143160548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327777659649746762107032611 491666489474620143160548917)
                ·
                  refine ⟨46093733388245638421301461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 491666489474620143160548917 46093733388245638421301461)
                  ·
                    refine ⟨1080321876287007150499253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46093733388245638421301461 1080321876287007150499253)
                    ·
                      rfl

theorem cell23_6311758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_6311758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311758 prefixEnd_6311758 := by exact prefixLift 6311758
  have htrace : WordTrace (prefixWord ++ tailWord_6311758) baseStart_6311758 baseEnd_6311758 := by
    simpa [prefixWord, tailWord_6311758, baseEnd_6311758] using wordTrace_append hprefix tailTrace_6311758
  have hstable : (prefixWord ++ tailWord_6311758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311758).length < 2 ^ (prefixWord ++ tailWord_6311758).sum := by decide
  have hdescent : baseEnd_6311758 < baseStart_6311758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311762 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_6311762 : Nat := 118140960795 + 6311762 * 2 ^ 59
def prefixEnd_6311762 : Nat := 4983230072969 + 3 ^ 40 * 6311762 * 2
def baseEnd_6311762 : Nat := 360107520309293270649749

theorem tailTrace_6311762 : CollatzResearch.WordTrace tailWord_6311762 prefixEnd_6311762 360107520309293270649749 := by
  unfold tailWord_6311762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552218139892927993420385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153472581706381141315787693 57552218139892927993420385)
  ·
    refine ⟨43164163604919695995065289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57552218139892927993420385 43164163604919695995065289)
    ·
      refine ⟨32373122703689771996298967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43164163604919695995065289 32373122703689771996298967)
      ·
        refine ⟨48559684055534657994448451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32373122703689771996298967 48559684055534657994448451)
        ·
          refine ⟨72839526083301986991672677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48559684055534657994448451 72839526083301986991672677)
          ·
            refine ⟨13657411140619122560938627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72839526083301986991672677 13657411140619122560938627)
            ·
              refine ⟨20486116710928683841407941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13657411140619122560938627 20486116710928683841407941)
              ·
                refine ⟨3841146883299128220263989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20486116710928683841407941 3841146883299128220263989)
                ·
                  refine ⟨360107520309293270649749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841146883299128220263989 360107520309293270649749)
                  ·
                    rfl

theorem cell23_6311762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_6311762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311762 prefixEnd_6311762 := by exact prefixLift 6311762
  have htrace : WordTrace (prefixWord ++ tailWord_6311762) baseStart_6311762 baseEnd_6311762 := by
    simpa [prefixWord, tailWord_6311762, baseEnd_6311762] using wordTrace_append hprefix tailTrace_6311762
  have hstable : (prefixWord ++ tailWord_6311762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311762).length < 2 ^ (prefixWord ++ tailWord_6311762).sum := by decide
  have hdescent : baseEnd_6311762 < baseStart_6311762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311795 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 6, 2]
def baseStart_6311795 : Nat := 118140960795 + 6311795 * 2 ^ 59
def prefixEnd_6311795 : Nat := 4983230072969 + 3 ^ 40 * 6311795 * 2
def baseEnd_6311795 : Nat := 3240984627645237806735089

theorem tailTrace_6311795 : CollatzResearch.WordTrace tailWord_6311795 prefixEnd_6311795 3240984627645237806735089 := by
  unfold tailWord_6311795
  simp only [CollatzResearch.WordTrace]
  refine ⟨230210076168452158609632839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153473384112301439073088559 230210076168452158609632839)
  ·
    refine ⟨345315114252678237914449259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230210076168452158609632839 345315114252678237914449259)
    ·
      refine ⟨517972671379017356871673889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345315114252678237914449259 517972671379017356871673889)
      ·
        refine ⟨388479503534263017653755417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517972671379017356871673889 388479503534263017653755417)
        ·
          refine ⟨291359627650697263240316563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388479503534263017653755417 291359627650697263240316563)
          ·
            refine ⟨437039441476045894860474845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291359627650697263240316563 437039441476045894860474845)
            ·
              refine ⟨163889790553517210572678067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437039441476045894860474845 163889790553517210572678067)
              ·
                refine ⟨245834685830275815859017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163889790553517210572678067 245834685830275815859017101)
                ·
                  refine ⟨92188007186353430947131413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245834685830275815859017101 92188007186353430947131413)
                  ·
                    refine ⟨4321312836860317075646785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92188007186353430947131413 4321312836860317075646785)
                    ·
                      refine ⟨3240984627645237806735089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321312836860317075646785 3240984627645237806735089)
                      ·
                        rfl

theorem cell23_6311795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6, 2].length) (baseStart_6311795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311795 prefixEnd_6311795 := by exact prefixLift 6311795
  have htrace : WordTrace (prefixWord ++ tailWord_6311795) baseStart_6311795 baseEnd_6311795 := by
    simpa [prefixWord, tailWord_6311795, baseEnd_6311795] using wordTrace_append hprefix tailTrace_6311795
  have hstable : (prefixWord ++ tailWord_6311795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311795).length < 2 ^ (prefixWord ++ tailWord_6311795).sum := by decide
  have hdescent : baseEnd_6311795 < baseStart_6311795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311805 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_6311805 : Nat := 118140960795 + 6311805 * 2 ^ 59
def prefixEnd_6311805 : Nat := 4983230072969 + 3 ^ 40 * 6311805 * 2
def baseEnd_6311805 : Nat := 1080329920817260922536681

theorem tailTrace_6311805 : CollatzResearch.WordTrace tailWord_6311805 prefixEnd_6311805 1080329920817260922536681 := by
  unfold tailWord_6311805
  simp only [CollatzResearch.WordTrace]
  refine ⟨230210440898415930317496869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153473627265610620211664579 230210440898415930317496869)
  ·
    refine ⟨43164457668452986934530663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230210440898415930317496869 43164457668452986934530663)
    ·
      refine ⟨64746686502679480401795995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43164457668452986934530663 64746686502679480401795995)
      ·
        refine ⟨97120029754019220602693993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64746686502679480401795995 97120029754019220602693993)
        ·
          refine ⟨72840022315514415452020495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97120029754019220602693993 72840022315514415452020495)
          ·
            refine ⟨109260033473271623178030743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72840022315514415452020495 109260033473271623178030743)
            ·
              refine ⟨163890050209907434767046115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109260033473271623178030743 163890050209907434767046115)
              ·
                refine ⟨245835075314861152150569173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163890050209907434767046115 245835075314861152150569173)
                ·
                  refine ⟨5761759577692058253528965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245835075314861152150569173 5761759577692058253528965)
                  ·
                    refine ⟨1080329920817260922536681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761759577692058253528965 1080329920817260922536681)
                    ·
                      rfl

theorem cell23_6311805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_6311805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311805 prefixEnd_6311805 := by exact prefixLift 6311805
  have htrace : WordTrace (prefixWord ++ tailWord_6311805) baseStart_6311805 baseEnd_6311805 := by
    simpa [prefixWord, tailWord_6311805, baseEnd_6311805] using wordTrace_append hprefix tailTrace_6311805
  have hstable : (prefixWord ++ tailWord_6311805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311805).length < 2 ^ (prefixWord ++ tailWord_6311805).sum := by decide
  have hdescent : baseEnd_6311805 < baseStart_6311805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311808 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_6311808 : Nat := 118140960795 + 6311808 * 2 ^ 59
def prefixEnd_6311808 : Nat := 4983230072969 + 3 ^ 40 * 6311808 * 2
def baseEnd_6311808 : Nat := 3240991302893746255872529

theorem tailTrace_6311808 : CollatzResearch.WordTrace tailWord_6311808 prefixEnd_6311808 3240991302893746255872529 := by
  unfold tailWord_6311808
  simp only [CollatzResearch.WordTrace]
  refine ⟨115105275158702530914928039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153473700211603374553237385 115105275158702530914928039)
  ·
    refine ⟨172657912738053796372392059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115105275158702530914928039 172657912738053796372392059)
    ·
      refine ⟨258986869107080694558588089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172657912738053796372392059 258986869107080694558588089)
      ·
        refine ⟨194240151830310520918941067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258986869107080694558588089 194240151830310520918941067)
        ·
          refine ⟨291360227745465781378411601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194240151830310520918941067 291360227745465781378411601)
          ·
            refine ⟨218520170809099336033808701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291360227745465781378411601 218520170809099336033808701)
            ·
              refine ⟨81945064053412251012678263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218520170809099336033808701 81945064053412251012678263)
              ·
                refine ⟨122917596080118376519017395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81945064053412251012678263 122917596080118376519017395)
                ·
                  refine ⟨184376394120177564778526093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122917596080118376519017395 184376394120177564778526093)
                  ·
                    refine ⟨69141147795066586791947285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184376394120177564778526093 69141147795066586791947285)
                    ·
                      refine ⟨3240991302893746255872529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69141147795066586791947285 3240991302893746255872529)
                      ·
                        rfl

theorem cell23_6311808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_6311808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311808 prefixEnd_6311808 := by exact prefixLift 6311808
  have htrace : WordTrace (prefixWord ++ tailWord_6311808) baseStart_6311808 baseEnd_6311808 := by
    simpa [prefixWord, tailWord_6311808, baseEnd_6311808] using wordTrace_append hprefix tailTrace_6311808
  have hstable : (prefixWord ++ tailWord_6311808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311808).length < 2 ^ (prefixWord ++ tailWord_6311808).sum := by decide
  have hdescent : baseEnd_6311808 < baseStart_6311808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311812 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_6311812 : Nat := 118140960795 + 6311812 * 2 ^ 59
def prefixEnd_6311812 : Nat := 4983230072969 + 3 ^ 40 * 6311812 * 2
def baseEnd_6311812 : Nat := 3240993356816364240222511

theorem tailTrace_6311812 : CollatzResearch.WordTrace tailWord_6311812 prefixEnd_6311812 3240993356816364240222511 := by
  unfold tailWord_6311812
  simp only [CollatzResearch.WordTrace]
  refine ⟨115105348104695285256500845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153473797472927047008667793 115105348104695285256500845)
  ·
    refine ⟨43164505539260731971187817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115105348104695285256500845 43164505539260731971187817)
    ·
      refine ⟨32373379154445548978390863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43164505539260731971187817 32373379154445548978390863)
      ·
        refine ⟨48560068731668323467586295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32373379154445548978390863 48560068731668323467586295)
        ·
          refine ⟨72840103097502485201379443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48560068731668323467586295 72840103097502485201379443)
          ·
            refine ⟨109260154646253727802069165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72840103097502485201379443 109260154646253727802069165)
            ·
              refine ⟨40972557992345147925775937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109260154646253727802069165 40972557992345147925775937)
              ·
                refine ⟨30729418494258860944331953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40972557992345147925775937 30729418494258860944331953)
                ·
                  refine ⟨23047063870694145708248965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30729418494258860944331953 23047063870694145708248965)
                  ·
                    refine ⟨4321324475755152320296681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23047063870694145708248965 4321324475755152320296681)
                    ·
                      refine ⟨3240993356816364240222511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321324475755152320296681 3240993356816364240222511)
                      ·
                        rfl

theorem cell23_6311812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_6311812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311812 prefixEnd_6311812 := by exact prefixLift 6311812
  have htrace : WordTrace (prefixWord ++ tailWord_6311812) baseStart_6311812 baseEnd_6311812 := by
    simpa [prefixWord, tailWord_6311812, baseEnd_6311812] using wordTrace_append hprefix tailTrace_6311812
  have hstable : (prefixWord ++ tailWord_6311812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311812).length < 2 ^ (prefixWord ++ tailWord_6311812).sum := by decide
  have hdescent : baseEnd_6311812 < baseStart_6311812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311895 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 6]
def baseStart_6311895 : Nat := 118140960795 + 6311895 * 2 ^ 59
def prefixEnd_6311895 : Nat := 4983230072969 + 3 ^ 40 * 6311895 * 2
def baseEnd_6311895 : Nat := 1080345325236895805161543

theorem tailTrace_6311895 : CollatzResearch.WordTrace tailWord_6311895 prefixEnd_6311895 1080345325236895805161543 := by
  unfold tailWord_6311895
  simp only [CollatzResearch.WordTrace]
  refine ⟨230213723468089875688273139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153475815645393250458848759 230213723468089875688273139)
  ·
    refine ⟨345320585202134813532409709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230213723468089875688273139 345320585202134813532409709)
    ·
      refine ⟨129495219450800555074653641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345320585202134813532409709 129495219450800555074653641)
      ·
        refine ⟨97121414588100416305990231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129495219450800555074653641 97121414588100416305990231)
        ·
          refine ⟨145682121882150624458985347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97121414588100416305990231 145682121882150624458985347)
          ·
            refine ⟨218523182823225936688478021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145682121882150624458985347 218523182823225936688478021)
            ·
              refine ⟨40973096779354863129089629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218523182823225936688478021 40973096779354863129089629)
              ·
                refine ⟨15364911292258073673408611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40973096779354863129089629 15364911292258073673408611)
                ·
                  refine ⟨23047366938387110510112917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15364911292258073673408611 23047366938387110510112917)
                  ·
                    refine ⟨1080345325236895805161543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23047366938387110510112917 1080345325236895805161543)
                    ·
                      rfl

theorem cell23_6311895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_6311895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311895 prefixEnd_6311895 := by exact prefixLift 6311895
  have htrace : WordTrace (prefixWord ++ tailWord_6311895) baseStart_6311895 baseEnd_6311895 := by
    simpa [prefixWord, tailWord_6311895, baseEnd_6311895] using wordTrace_append hprefix tailTrace_6311895
  have hstable : (prefixWord ++ tailWord_6311895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311895).length < 2 ^ (prefixWord ++ tailWord_6311895).sum := by decide
  have hdescent : baseEnd_6311895 < baseStart_6311895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311905 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6311905 : Nat := 118140960795 + 6311905 * 2 ^ 59
def prefixEnd_6311905 : Nat := 4983230072969 + 3 ^ 40 * 6311905 * 2
def baseEnd_6311905 : Nat := 3241041110517232376359583

theorem tailTrace_6311905 : CollatzResearch.WordTrace tailWord_6311905 prefixEnd_6311905 3241041110517232376359583 := by
  unfold tailWord_6311905
  simp only [CollatzResearch.WordTrace]
  refine ⟨230214088198053647396137169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153476058798702431597424779 230214088198053647396137169)
  ·
    refine ⟨172660566148540235547102877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230214088198053647396137169 172660566148540235547102877)
    ·
      refine ⟨64747712305702588330163579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172660566148540235547102877 64747712305702588330163579)
      ·
        refine ⟨97121568458553882495245369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64747712305702588330163579 97121568458553882495245369)
        ·
          refine ⟨72841176343915411871434027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97121568458553882495245369 72841176343915411871434027)
          ·
            refine ⟨109261764515873117807151041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72841176343915411871434027 109261764515873117807151041)
            ·
              refine ⟨81946323386904838355363281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109261764515873117807151041 81946323386904838355363281)
              ·
                refine ⟨61459742540178628766522461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81946323386904838355363281 61459742540178628766522461)
                ·
                  refine ⟨23047403452566985787445923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61459742540178628766522461 23047403452566985787445923)
                  ·
                    refine ⟨34571105178850478681168885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23047403452566985787445923 34571105178850478681168885)
                    ·
                      refine ⟨3241041110517232376359583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34571105178850478681168885 3241041110517232376359583)
                      ·
                        rfl

theorem cell23_6311905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6311905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311905 prefixEnd_6311905 := by exact prefixLift 6311905
  have htrace : WordTrace (prefixWord ++ tailWord_6311905) baseStart_6311905 baseEnd_6311905 := by
    simpa [prefixWord, tailWord_6311905, baseEnd_6311905] using wordTrace_append hprefix tailTrace_6311905
  have hstable : (prefixWord ++ tailWord_6311905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311905).length < 2 ^ (prefixWord ++ tailWord_6311905).sum := by decide
  have hdescent : baseEnd_6311905 < baseStart_6311905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311919 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 1, 1, 4]
def baseStart_6311919 : Nat := 118140960795 + 6311919 * 2 ^ 59
def prefixEnd_6311919 : Nat := 4983230072969 + 3 ^ 40 * 6311919 * 2
def baseEnd_6311919 : Nat := 3241048299246395321584519

theorem tailTrace_6311919 : CollatzResearch.WordTrace tailWord_6311919 prefixEnd_6311919 3241048299246395321584519 := by
  unfold tailWord_6311919
  simp only [CollatzResearch.WordTrace]
  refine ⟨230214598820002927787146811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153476399213335285191431207 230214598820002927787146811)
  ·
    refine ⟨345321898230004391680720217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230214598820002927787146811 345321898230004391680720217)
    ·
      refine ⟨258991423672503293760540163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345321898230004391680720217 258991423672503293760540163)
      ·
        refine ⟨388487135508754940640810245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258991423672503293760540163 388487135508754940640810245)
        ·
          refine ⟨72841337907891551370151921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388487135508754940640810245 72841337907891551370151921)
          ·
            refine ⟨54631003430918663527613941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72841337907891551370151921 54631003430918663527613941)
            ·
              refine ⟨5121656571648624705713807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54631003430918663527613941 5121656571648624705713807)
              ·
                refine ⟨7682484857472937058570711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121656571648624705713807 7682484857472937058570711)
                ·
                  refine ⟨11523727286209405587856067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682484857472937058570711 11523727286209405587856067)
                  ·
                    refine ⟨17285590929314108381784101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11523727286209405587856067 17285590929314108381784101)
                    ·
                      refine ⟨3241048299246395321584519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17285590929314108381784101 3241048299246395321584519)
                      ·
                        rfl

theorem cell23_6311919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 1, 4].length) (baseStart_6311919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311919 prefixEnd_6311919 := by exact prefixLift 6311919
  have htrace : WordTrace (prefixWord ++ tailWord_6311919) baseStart_6311919 baseEnd_6311919 := by
    simpa [prefixWord, tailWord_6311919, baseEnd_6311919] using wordTrace_append hprefix tailTrace_6311919
  have hstable : (prefixWord ++ tailWord_6311919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311919).length < 2 ^ (prefixWord ++ tailWord_6311919).sum := by decide
  have hdescent : baseEnd_6311919 < baseStart_6311919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311925 : List Nat := [1, 3, 5, 14]
def baseStart_6311925 : Nat := 118140960795 + 6311925 * 2 ^ 59
def prefixEnd_6311925 : Nat := 4983230072969 + 3 ^ 40 * 6311925 * 2
def baseEnd_6311925 : Nat := 1481962222281811750393

theorem tailTrace_6311925 : CollatzResearch.WordTrace tailWord_6311925 prefixEnd_6311925 1481962222281811750393 := by
  unfold tailWord_6311925
  simp only [CollatzResearch.WordTrace]
  refine ⟨230214817657981190811865229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153476545105320793874576819 230214817657981190811865229)
  ·
    refine ⟨86330556621742946554449461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230214817657981190811865229 86330556621742946554449461)
    ·
      refine ⟨8093489683288401239479637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86330556621742946554449461 8093489683288401239479637)
      ·
        refine ⟨1481962222281811750393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8093489683288401239479637 1481962222281811750393)
        ·
          rfl

theorem cell23_6311925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 14].length) (baseStart_6311925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311925 prefixEnd_6311925 := by exact prefixLift 6311925
  have htrace : WordTrace (prefixWord ++ tailWord_6311925) baseStart_6311925 baseEnd_6311925 := by
    simpa [prefixWord, tailWord_6311925, baseEnd_6311925] using wordTrace_append hprefix tailTrace_6311925
  have hstable : (prefixWord ++ tailWord_6311925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311925).length < 2 ^ (prefixWord ++ tailWord_6311925).sum := by decide
  have hdescent : baseEnd_6311925 < baseStart_6311925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311929 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_6311929 : Nat := 118140960795 + 6311929 * 2 ^ 59
def prefixEnd_6311929 : Nat := 4983230072969 + 3 ^ 40 * 6311929 * 2
def baseEnd_6311929 : Nat := 1080351144684313427486491

theorem tailTrace_6311929 : CollatzResearch.WordTrace tailWord_6311929 prefixEnd_6311929 1080351144684313427486491 := by
  unfold tailWord_6311929
  simp only [CollatzResearch.WordTrace]
  refine ⟨230214963549966699495010841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153476642366644466330007227 230214963549966699495010841)
  ·
    refine ⟨172661222662475024621258131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230214963549966699495010841 172661222662475024621258131)
    ·
      refine ⟨258991833993712536931887197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172661222662475024621258131 258991833993712536931887197)
      ·
        refine ⟨97121937747642201349457699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258991833993712536931887197 97121937747642201349457699)
        ·
          refine ⟨145682906621463302024186549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97121937747642201349457699 145682906621463302024186549)
          ·
            refine ⟨13657772495762184564767489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145682906621463302024186549 13657772495762184564767489)
            ·
              refine ⟨10243329371821638423575617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13657772495762184564767489 10243329371821638423575617)
              ·
                refine ⟨7682497028866228817681713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243329371821638423575617 7682497028866228817681713)
                ·
                  refine ⟨5761872771649671613261285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682497028866228817681713 5761872771649671613261285)
                  ·
                    refine ⟨1080351144684313427486491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761872771649671613261285 1080351144684313427486491)
                    ·
                      rfl

theorem cell23_6311929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_6311929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311929 prefixEnd_6311929 := by exact prefixLift 6311929
  have htrace : WordTrace (prefixWord ++ tailWord_6311929) baseStart_6311929 baseEnd_6311929 := by
    simpa [prefixWord, tailWord_6311929, baseEnd_6311929] using wordTrace_append hprefix tailTrace_6311929
  have hstable : (prefixWord ++ tailWord_6311929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311929).length < 2 ^ (prefixWord ++ tailWord_6311929).sum := by decide
  have hdescent : baseEnd_6311929 < baseStart_6311929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311959 : List Nat := [1, 1, 3, 5, 2, 1, 3, 7]
def baseStart_6311959 : Nat := 118140960795 + 6311959 * 2 ^ 59
def prefixEnd_6311959 : Nat := 4983230072969 + 3 ^ 40 * 6311959 * 2
def baseEnd_6311959 : Nat := 120039586610095376484605

theorem tailTrace_6311959 : CollatzResearch.WordTrace tailWord_6311959 prefixEnd_6311959 120039586610095376484605 := by
  unfold tailWord_6311959
  simp only [CollatzResearch.WordTrace]
  refine ⟨230216057739858014618602931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153477371826572009745735287 230216057739858014618602931)
  ·
    refine ⟨345324086609787021927904397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230216057739858014618602931 345324086609787021927904397)
    ·
      refine ⟨129496532478670133222964149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345324086609787021927904397 129496532478670133222964149)
      ·
        refine ⟨12140299919875324989652889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129496532478670133222964149 12140299919875324989652889)
        ·
          refine ⟨9105224939906493742239667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140299919875324989652889 9105224939906493742239667)
          ·
            refine ⟨13657837409859740613359501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105224939906493742239667 13657837409859740613359501)
            ·
              refine ⟨5121689028697402730009813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13657837409859740613359501 5121689028697402730009813)
              ·
                refine ⟨120039586610095376484605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5121689028697402730009813 120039586610095376484605)
                ·
                  rfl

theorem cell23_6311959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 7].length) (baseStart_6311959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311959 prefixEnd_6311959 := by exact prefixLift 6311959
  have htrace : WordTrace (prefixWord ++ tailWord_6311959) baseStart_6311959 baseEnd_6311959 := by
    simpa [prefixWord, tailWord_6311959, baseEnd_6311959] using wordTrace_append hprefix tailTrace_6311959
  have hstable : (prefixWord ++ tailWord_6311959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311959).length < 2 ^ (prefixWord ++ tailWord_6311959).sum := by decide
  have hdescent : baseEnd_6311959 < baseStart_6311959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311986 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_6311986 : Nat := 118140960795 + 6311986 * 2 ^ 59
def prefixEnd_6311986 : Nat := 4983230072969 + 3 ^ 40 * 6311986 * 2
def baseEnd_6311986 : Nat := 3241082702450246559446711

theorem tailTrace_6311986 : CollatzResearch.WordTrace tailWord_6311986 prefixEnd_6311986 3241082702450246559446711 := by
  unfold tailWord_6311986
  simp only [CollatzResearch.WordTrace]
  refine ⟨57554260627690049557458953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153478028340506798819890541 57554260627690049557458953)
  ·
    refine ⟨43165695470767537168094215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57554260627690049557458953 43165695470767537168094215)
    ·
      refine ⟨64748543206151305752141323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43165695470767537168094215 64748543206151305752141323)
      ·
        refine ⟨97122814809226958628211985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64748543206151305752141323 97122814809226958628211985)
        ·
          refine ⟨72842111106920218971158989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97122814809226958628211985 72842111106920218971158989)
          ·
            refine ⟨27315791665095082114184621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72842111106920218971158989 27315791665095082114184621)
            ·
              refine ⟨10243421874410655792819233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27315791665095082114184621 10243421874410655792819233)
              ·
                refine ⟨7682566405807991844614425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243421874410655792819233 7682566405807991844614425)
                ·
                  refine ⟨5761924804355993883460819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682566405807991844614425 5761924804355993883460819)
                  ·
                    refine ⟨8642887206533990825191229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761924804355993883460819 8642887206533990825191229)
                    ·
                      refine ⟨3241082702450246559446711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642887206533990825191229 3241082702450246559446711)
                      ·
                        rfl

theorem cell23_6311986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_6311986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311986 prefixEnd_6311986 := by exact prefixLift 6311986
  have htrace : WordTrace (prefixWord ++ tailWord_6311986) baseStart_6311986 baseEnd_6311986 := by
    simpa [prefixWord, tailWord_6311986, baseEnd_6311986] using wordTrace_append hprefix tailTrace_6311986
  have hstable : (prefixWord ++ tailWord_6311986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311986).length < 2 ^ (prefixWord ++ tailWord_6311986).sum := by decide
  have hdescent : baseEnd_6311986 < baseStart_6311986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6311995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_6311995 : Nat := 118140960795 + 6311995 * 2 ^ 59
def prefixEnd_6311995 : Nat := 4983230072969 + 3 ^ 40 * 6311995 * 2
def baseEnd_6311995 : Nat := 3241087323776137024234169

theorem tailTrace_6311995 : CollatzResearch.WordTrace tailWord_6311995 prefixEnd_6311995 3241087323776137024234169 := by
  unfold tailWord_6311995
  simp only [CollatzResearch.WordTrace]
  refine ⟨230217370767727592766913439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153478247178485061844608959 230217370767727592766913439)
  ·
    refine ⟨345326056151591389150370159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230217370767727592766913439 345326056151591389150370159)
    ·
      refine ⟨517989084227387083725555239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345326056151591389150370159 517989084227387083725555239)
      ·
        refine ⟨776983626341080625588332859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517989084227387083725555239 776983626341080625588332859)
        ·
          refine ⟨1165475439511620938382499289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776983626341080625588332859 1165475439511620938382499289)
          ·
            refine ⟨874106579633715703786874467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165475439511620938382499289 874106579633715703786874467)
            ·
              refine ⟨1311159869450573555680311701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874106579633715703786874467 1311159869450573555680311701)
              ·
                refine ⟨61460618880495635422514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1311159869450573555680311701 61460618880495635422514611)
                ·
                  refine ⟨92190928320743453133771917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61460618880495635422514611 92190928320743453133771917)
                  ·
                    refine ⟨34571598120278794925164469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92190928320743453133771917 34571598120278794925164469)
                    ·
                      refine ⟨3241087323776137024234169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34571598120278794925164469 3241087323776137024234169)
                      ·
                        rfl

theorem cell23_6311995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_6311995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6311995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6311995 prefixEnd_6311995 := by exact prefixLift 6311995
  have htrace : WordTrace (prefixWord ++ tailWord_6311995) baseStart_6311995 baseEnd_6311995 := by
    simpa [prefixWord, tailWord_6311995, baseEnd_6311995] using wordTrace_append hprefix tailTrace_6311995
  have hstable : (prefixWord ++ tailWord_6311995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6311995).length < 2 ^ (prefixWord ++ tailWord_6311995).sum := by decide
  have hdescent : baseEnd_6311995 < baseStart_6311995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6311995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312012 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6312012 : Nat := 118140960795 + 6312012 * 2 ^ 59
def prefixEnd_6312012 : Nat := 4983230072969 + 3 ^ 40 * 6312012 * 2
def baseEnd_6312012 : Nat := 3241096052947263457721591

theorem tailTrace_6312012 : CollatzResearch.WordTrace tailWord_6312012 prefixEnd_6312012 3241096052947263457721591 := by
  unfold tailWord_6312012
  simp only [CollatzResearch.WordTrace]
  refine ⟨115108995404333002335141145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153478660539110669780188193 115108995404333002335141145)
  ·
    refine ⟨86331746553249751751355859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115108995404333002335141145 86331746553249751751355859)
    ·
      refine ⟨129497619829874627627033789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86331746553249751751355859 129497619829874627627033789)
      ·
        refine ⟨48561607436202985360137671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129497619829874627627033789 48561607436202985360137671)
        ·
          refine ⟨72842411154304478040206507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48561607436202985360137671 72842411154304478040206507)
          ·
            refine ⟨109263616731456717060309761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72842411154304478040206507 109263616731456717060309761)
            ·
              refine ⟨81947712548592537795232321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109263616731456717060309761 81947712548592537795232321)
              ·
                refine ⟨61460784411444403346424241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81947712548592537795232321 61460784411444403346424241)
                ·
                  refine ⟨46095588308583302509818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61460784411444403346424241 46095588308583302509818181)
                  ·
                    refine ⟨8642922807859369220590909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46095588308583302509818181 8642922807859369220590909)
                    ·
                      refine ⟨3241096052947263457721591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8642922807859369220590909 3241096052947263457721591)
                      ·
                        rfl

theorem cell23_6312012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6312012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312012 prefixEnd_6312012 := by exact prefixLift 6312012
  have htrace : WordTrace (prefixWord ++ tailWord_6312012) baseStart_6312012 baseEnd_6312012 := by
    simpa [prefixWord, tailWord_6312012, baseEnd_6312012] using wordTrace_append hprefix tailTrace_6312012
  have hstable : (prefixWord ++ tailWord_6312012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312012).length < 2 ^ (prefixWord ++ tailWord_6312012).sum := by decide
  have hdescent : baseEnd_6312012 < baseStart_6312012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312013 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6312013 : Nat := 118140960795 + 6312013 * 2 ^ 59
def prefixEnd_6312013 : Nat := 4983230072969 + 3 ^ 40 * 6312013 * 2
def baseEnd_6312013 : Nat := 3241096566427917953809087

theorem tailTrace_6312013 : CollatzResearch.WordTrace tailWord_6312013 prefixEnd_6312013 3241096566427917953809087 := by
  unfold tailWord_6312013
  simp only [CollatzResearch.WordTrace]
  refine ⟨230218027281662381841068693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153478684854441587894045795 230218027281662381841068693)
  ·
    refine ⟨10791470028827924148800095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230218027281662381841068693 10791470028827924148800095)
    ·
      refine ⟨16187205043241886223200143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10791470028827924148800095 16187205043241886223200143)
      ·
        refine ⟨24280807564862829334800215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16187205043241886223200143 24280807564862829334800215)
        ·
          refine ⟨36421211347294244002200323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24280807564862829334800215 36421211347294244002200323)
          ·
            refine ⟨54631817020941366003300485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36421211347294244002200323 54631817020941366003300485)
            ·
              refine ⟨10243465691426506125618841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54631817020941366003300485 10243465691426506125618841)
              ·
                refine ⟨7682599268569879594214131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243465691426506125618841 7682599268569879594214131)
                ·
                  refine ⟨11523898902854819391321197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682599268569879594214131 11523898902854819391321197)
                  ·
                    refine ⟨4321462088570557271745449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11523898902854819391321197 4321462088570557271745449)
                    ·
                      refine ⟨3241096566427917953809087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321462088570557271745449 3241096566427917953809087)
                      ·
                        rfl

theorem cell23_6312013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6312013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312013 prefixEnd_6312013 := by exact prefixLift 6312013
  have htrace : WordTrace (prefixWord ++ tailWord_6312013) baseStart_6312013 baseEnd_6312013 := by
    simpa [prefixWord, tailWord_6312013, baseEnd_6312013] using wordTrace_append hprefix tailTrace_6312013
  have hstable : (prefixWord ++ tailWord_6312013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312013).length < 2 ^ (prefixWord ++ tailWord_6312013).sum := by decide
  have hdescent : baseEnd_6312013 < baseStart_6312013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312029 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6312029 : Nat := 118140960795 + 6312029 * 2 ^ 59
def prefixEnd_6312029 : Nat := 4983230072969 + 3 ^ 40 * 6312029 * 2
def baseEnd_6312029 : Nat := 3241104782118389891209013

theorem tailTrace_6312029 : CollatzResearch.WordTrace tailWord_6312029 prefixEnd_6312029 3241104782118389891209013 := by
  unfold tailWord_6312029
  simp only [CollatzResearch.WordTrace]
  refine ⟨230218610849604416573651141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153479073899736277715767427 230218610849604416573651141)
  ·
    refine ⟨43165989534300828107559589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230218610849604416573651141 43165989534300828107559589)
    ·
      refine ⟨8093623037681405270167423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43165989534300828107559589 8093623037681405270167423)
      ·
        refine ⟨12140434556522107905251135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093623037681405270167423 12140434556522107905251135)
        ·
          refine ⟨18210651834783161857876703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12140434556522107905251135 18210651834783161857876703)
          ·
            refine ⟨27315977752174742786815055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18210651834783161857876703 27315977752174742786815055)
            ·
              refine ⟨40973966628262114180222583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27315977752174742786815055 40973966628262114180222583)
              ·
                refine ⟨61460949942393171270333875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40973966628262114180222583 61460949942393171270333875)
                ·
                  refine ⟨92191424913589756905500813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61460949942393171270333875 92191424913589756905500813)
                  ·
                    refine ⟨34571784342596158839562805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92191424913589756905500813 34571784342596158839562805)
                    ·
                      refine ⟨3241104782118389891209013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34571784342596158839562805 3241104782118389891209013)
                      ·
                        rfl

theorem cell23_6312029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6312029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312029 prefixEnd_6312029 := by exact prefixLift 6312029
  have htrace : WordTrace (prefixWord ++ tailWord_6312029) baseStart_6312029 baseEnd_6312029 := by
    simpa [prefixWord, tailWord_6312029, baseEnd_6312029] using wordTrace_append hprefix tailTrace_6312029
  have hstable : (prefixWord ++ tailWord_6312029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312029).length < 2 ^ (prefixWord ++ tailWord_6312029).sum := by decide
  have hdescent : baseEnd_6312029 < baseStart_6312029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312060 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_6312060 : Nat := 118140960795 + 6312060 * 2 ^ 59
def prefixEnd_6312060 : Nat := 4983230072969 + 3 ^ 40 * 6312060 * 2
def baseEnd_6312060 : Nat := 3241120700018679269921371

theorem tailTrace_6312060 : CollatzResearch.WordTrace tailWord_6312060 prefixEnd_6312060 3241120700018679269921371 := by
  unfold tailWord_6312060
  simp only [CollatzResearch.WordTrace]
  refine ⟨115109870756246054434014817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153479827674994739245353089 115109870756246054434014817)
  ·
    refine ⟨86332403067184540825511113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115109870756246054434014817 86332403067184540825511113)
    ·
      refine ⟨64749302300388405619133335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86332403067184540825511113 64749302300388405619133335)
      ·
        refine ⟨97123953450582608428700003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64749302300388405619133335 97123953450582608428700003)
        ·
          refine ⟨145685930175873912643050005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97123953450582608428700003 145685930175873912643050005)
          ·
            refine ⟨6829027976994089655142969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145685930175873912643050005 6829027976994089655142969)
            ·
              refine ⟨5121770982745567241357227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829027976994089655142969 5121770982745567241357227)
              ·
                refine ⟨7682656474118350862035841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121770982745567241357227 7682656474118350862035841)
                ·
                  refine ⟨5761992355588763146526881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682656474118350862035841 5761992355588763146526881)
                  ·
                    refine ⟨4321494266691572359895161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5761992355588763146526881 4321494266691572359895161)
                    ·
                      refine ⟨3241120700018679269921371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321494266691572359895161 3241120700018679269921371)
                      ·
                        rfl

theorem cell23_6312060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_6312060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312060 prefixEnd_6312060 := by exact prefixLift 6312060
  have htrace : WordTrace (prefixWord ++ tailWord_6312060) baseStart_6312060 baseEnd_6312060 := by
    simpa [prefixWord, tailWord_6312060, baseEnd_6312060] using wordTrace_append hprefix tailTrace_6312060
  have hstable : (prefixWord ++ tailWord_6312060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312060).length < 2 ^ (prefixWord ++ tailWord_6312060).sum := by decide
  have hdescent : baseEnd_6312060 < baseStart_6312060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312100 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 5]
def baseStart_6312100 : Nat := 118140960795 + 6312100 * 2 ^ 59
def prefixEnd_6312100 : Nat := 4983230072969 + 3 ^ 40 * 6312100 * 2
def baseEnd_6312100 : Nat := 360126804360539901491243

theorem tailTrace_6312100 : CollatzResearch.WordTrace tailWord_6312100 prefixEnd_6312100 360126804360539901491243 := by
  unfold tailWord_6312100
  simp only [CollatzResearch.WordTrace]
  refine ⟨115110600216173597849742877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153480800288231463799657169 115110600216173597849742877)
  ·
    refine ⟨43166475081065099193653579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115110600216173597849742877 43166475081065099193653579)
    ·
      refine ⟨64749712621597648790480369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43166475081065099193653579 64749712621597648790480369)
      ·
        refine ⟨48562284466198236592860277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64749712621597648790480369 48562284466198236592860277)
        ·
          refine ⟨4552714168706084680580651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48562284466198236592860277 4552714168706084680580651)
          ·
            refine ⟨6829071253059127020870977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552714168706084680580651 6829071253059127020870977)
            ·
              refine ⟨5121803439794345265653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829071253059127020870977 5121803439794345265653233)
              ·
                refine ⟨3841352579845758949239925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5121803439794345265653233 3841352579845758949239925)
                ·
                  refine ⟨360126804360539901491243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841352579845758949239925 360126804360539901491243)
                  ·
                    rfl

theorem cell23_6312100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_6312100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312100 prefixEnd_6312100 := by exact prefixLift 6312100
  have htrace : WordTrace (prefixWord ++ tailWord_6312100) baseStart_6312100 baseEnd_6312100 := by
    simpa [prefixWord, tailWord_6312100, baseEnd_6312100] using wordTrace_append hprefix tailTrace_6312100
  have hstable : (prefixWord ++ tailWord_6312100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312100).length < 2 ^ (prefixWord ++ tailWord_6312100).sum := by decide
  have hdescent : baseEnd_6312100 < baseStart_6312100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312130 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6312130 : Nat := 118140960795 + 6312130 * 2 ^ 59
def prefixEnd_6312130 : Nat := 4983230072969 + 3 ^ 40 * 6312130 * 2
def baseEnd_6312130 : Nat := 1080385547888164665348683

theorem tailTrace_6312130 : CollatzResearch.WordTrace tailWord_6312130 prefixEnd_6312130 1080385547888164665348683 := by
  unfold tailWord_6312130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57555573655559627705769461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153481529748159007215385229 57555573655559627705769461)
  ·
    refine ⟨5395835030208715097415887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57555573655559627705769461 5395835030208715097415887)
    ·
      refine ⟨8093752545313072646123831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395835030208715097415887 8093752545313072646123831)
      ·
        refine ⟨12140628817969608969185747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093752545313072646123831 12140628817969608969185747)
        ·
          refine ⟨18210943226954413453778621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12140628817969608969185747 18210943226954413453778621)
          ·
            refine ⟨6829103710107905045166983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18210943226954413453778621 6829103710107905045166983)
            ·
              refine ⟨10243655565161857567750475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829103710107905045166983 10243655565161857567750475)
              ·
                refine ⟨15365483347742786351625713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243655565161857567750475 15365483347742786351625713)
                ·
                  refine ⟨11524112510807089763719285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15365483347742786351625713 11524112510807089763719285)
                  ·
                    refine ⟨1080385547888164665348683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11524112510807089763719285 1080385547888164665348683)
                    ·
                      rfl

theorem cell23_6312130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6312130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312130 prefixEnd_6312130 := by exact prefixLift 6312130
  have htrace : WordTrace (prefixWord ++ tailWord_6312130) baseStart_6312130 baseEnd_6312130 := by
    simpa [prefixWord, tailWord_6312130, baseEnd_6312130] using wordTrace_append hprefix tailTrace_6312130
  have hstable : (prefixWord ++ tailWord_6312130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312130).length < 2 ^ (prefixWord ++ tailWord_6312130).sum := by decide
  have hdescent : baseEnd_6312130 < baseStart_6312130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312173 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 6]
def baseStart_6312173 : Nat := 118140960795 + 6312173 * 2 ^ 59
def prefixEnd_6312173 : Nat := 4983230072969 + 3 ^ 40 * 6312173 * 2
def baseEnd_6312173 : Nat := 360130969259181925312039

theorem tailTrace_6312173 : CollatzResearch.WordTrace tailWord_6312173 prefixEnd_6312173 360130969259181925312039 := by
  unfold tailWord_6312173
  simp only [CollatzResearch.WordTrace]
  refine ⟨230223862961082729166893173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153482575307388486111262115 230223862961082729166893173)
  ·
    refine ⟨21583487152601505859396235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230223862961082729166893173 21583487152601505859396235)
    ·
      refine ⟨32375230728902258789094353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583487152601505859396235 32375230728902258789094353)
      ·
        refine ⟨24281423046676694091820765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32375230728902258789094353 24281423046676694091820765)
        ·
          refine ⟨9105533642503760284432787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24281423046676694091820765 9105533642503760284432787)
          ·
            refine ⟨13658300463755640426649181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105533642503760284432787 13658300463755640426649181)
            ·
              refine ⟨5121862673908365159993443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13658300463755640426649181 5121862673908365159993443)
              ·
                refine ⟨7682794010862547739990165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121862673908365159993443 7682794010862547739990165)
                ·
                  refine ⟨360130969259181925312039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7682794010862547739990165 360130969259181925312039)
                  ·
                    rfl

theorem cell23_6312173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_6312173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312173 prefixEnd_6312173 := by exact prefixLift 6312173
  have htrace : WordTrace (prefixWord ++ tailWord_6312173) baseStart_6312173 baseEnd_6312173 := by
    simpa [prefixWord, tailWord_6312173, baseEnd_6312173] using wordTrace_append hprefix tailTrace_6312173
  have hstable : (prefixWord ++ tailWord_6312173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312173).length < 2 ^ (prefixWord ++ tailWord_6312173).sum := by decide
  have hdescent : baseEnd_6312173 < baseStart_6312173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312186 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_6312186 : Nat := 118140960795 + 6312186 * 2 ^ 59
def prefixEnd_6312186 : Nat := 4983230072969 + 3 ^ 40 * 6312186 * 2
def baseEnd_6312186 : Nat := 1080395132860381925648597

theorem tailTrace_6312186 : CollatzResearch.WordTrace tailWord_6312186 prefixEnd_6312186 1080395132860381925648597 := by
  unfold tailWord_6312186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57556084277508908096779103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153482891406690421591410941 57556084277508908096779103)
  ·
    refine ⟨86334126416263362145168655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57556084277508908096779103 86334126416263362145168655)
    ·
      refine ⟨129501189624395043217752983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86334126416263362145168655 129501189624395043217752983)
      ·
        refine ⟨194251784436592564826629475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129501189624395043217752983 194251784436592564826629475)
        ·
          refine ⟨291377676654888847239944213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194251784436592564826629475 291377676654888847239944213)
          ·
            refine ⟨13658328593197914714372385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 291377676654888847239944213 13658328593197914714372385)
            ·
              refine ⟨10243746444898436035779289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13658328593197914714372385 10243746444898436035779289)
              ·
                refine ⟨7682809833673827026834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243746444898436035779289 7682809833673827026834467)
                ·
                  refine ⟨11524214750510740540251701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682809833673827026834467 11524214750510740540251701)
                  ·
                    refine ⟨1080395132860381925648597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11524214750510740540251701 1080395132860381925648597)
                    ·
                      rfl

theorem cell23_6312186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_6312186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312186 prefixEnd_6312186 := by exact prefixLift 6312186
  have htrace : WordTrace (prefixWord ++ tailWord_6312186) baseStart_6312186 baseEnd_6312186 := by
    simpa [prefixWord, tailWord_6312186, baseEnd_6312186] using wordTrace_append hprefix tailTrace_6312186
  have hstable : (prefixWord ++ tailWord_6312186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312186).length < 2 ^ (prefixWord ++ tailWord_6312186).sum := by decide
  have hdescent : baseEnd_6312186 < baseStart_6312186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312189 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_6312189 : Nat := 118140960795 + 6312189 * 2 ^ 59
def prefixEnd_6312189 : Nat := 4983230072969 + 3 ^ 40 * 6312189 * 2
def baseEnd_6312189 : Nat := 3241186939023109265208277

theorem tailTrace_6312189 : CollatzResearch.WordTrace tailWord_6312189 prefixEnd_6312189 3241186939023109265208277 := by
  unfold tailWord_6312189
  simp only [CollatzResearch.WordTrace]
  refine ⟨230224446529024763899475621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153482964352683175932983747 230224446529024763899475621)
  ·
    refine ⟨43167083724192143231151679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230224446529024763899475621 43167083724192143231151679)
    ·
      refine ⟨64750625586288214846727519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43167083724192143231151679 64750625586288214846727519)
      ·
        refine ⟨97125938379432322270091279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64750625586288214846727519 97125938379432322270091279)
        ·
          refine ⟨145688907569148483405136919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97125938379432322270091279 145688907569148483405136919)
          ·
            refine ⟨218533361353722725107705379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145688907569148483405136919 218533361353722725107705379)
            ·
              refine ⟨327800042030584087661558069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218533361353722725107705379 327800042030584087661558069)
              ·
                refine ⟨30731253940367258218271069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327800042030584087661558069 30731253940367258218271069)
                ·
                  refine ⟨11524220227637721831851651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30731253940367258218271069 11524220227637721831851651)
                  ·
                    refine ⟨17286330341456582747777477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11524220227637721831851651 17286330341456582747777477)
                    ·
                      refine ⟨3241186939023109265208277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17286330341456582747777477 3241186939023109265208277)
                      ·
                        rfl

theorem cell23_6312189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_6312189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312189 prefixEnd_6312189 := by exact prefixLift 6312189
  have htrace : WordTrace (prefixWord ++ tailWord_6312189) baseStart_6312189 baseEnd_6312189 := by
    simpa [prefixWord, tailWord_6312189, baseEnd_6312189] using wordTrace_append hprefix tailTrace_6312189
  have hstable : (prefixWord ++ tailWord_6312189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312189).length < 2 ^ (prefixWord ++ tailWord_6312189).sum := by decide
  have hdescent : baseEnd_6312189 < baseStart_6312189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312200 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_6312200 : Nat := 118140960795 + 6312200 * 2 ^ 59
def prefixEnd_6312200 : Nat := 4983230072969 + 3 ^ 40 * 6312200 * 2
def baseEnd_6312200 : Nat := 3241192587310308722170727

theorem tailTrace_6312200 : CollatzResearch.WordTrace tailWord_6312200 prefixEnd_6312200 3241192587310308722170727 := by
  unfold tailWord_6312200
  simp only [CollatzResearch.WordTrace]
  refine ⟨115112423865992456389063027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153483231821323275185417369 115112423865992456389063027)
  ·
    refine ⟨172668635798988684583594541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115112423865992456389063027 172668635798988684583594541)
    ·
      refine ⟨64750738424620756718847953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172668635798988684583594541 64750738424620756718847953)
      ·
        refine ⟨48563053818465567539135965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64750738424620756718847953 48563053818465567539135965)
        ·
          refine ⟨18211145181924587827175987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48563053818465567539135965 18211145181924587827175987)
          ·
            refine ⟨27316717772886881740763981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18211145181924587827175987 27316717772886881740763981)
            ·
              refine ⟨10243769164832580652786493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27316717772886881740763981 10243769164832580652786493)
              ·
                refine ⟨3841413436812217744794935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10243769164832580652786493 3841413436812217744794935)
                ·
                  refine ⟨5762120155218326617192403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841413436812217744794935 5762120155218326617192403)
                  ·
                    refine ⟨8643180232827489925788605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762120155218326617192403 8643180232827489925788605)
                    ·
                      refine ⟨3241192587310308722170727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643180232827489925788605 3241192587310308722170727)
                      ·
                        rfl

theorem cell23_6312200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_6312200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312200 prefixEnd_6312200 := by exact prefixLift 6312200
  have htrace : WordTrace (prefixWord ++ tailWord_6312200) baseStart_6312200 baseEnd_6312200 := by
    simpa [prefixWord, tailWord_6312200, baseEnd_6312200] using wordTrace_append hprefix tailTrace_6312200
  have hstable : (prefixWord ++ tailWord_6312200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312200).length < 2 ^ (prefixWord ++ tailWord_6312200).sum := by decide
  have hdescent : baseEnd_6312200 < baseStart_6312200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312206 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6312206 : Nat := 118140960795 + 6312206 * 2 ^ 59
def prefixEnd_6312206 : Nat := 4983230072969 + 3 ^ 40 * 6312206 * 2
def baseEnd_6312206 : Nat := 3241195668194235698695699

theorem tailTrace_6312206 : CollatzResearch.WordTrace tailWord_6312206 prefixEnd_6312206 3241195668194235698695699 := by
  unfold tailWord_6312206
  simp only [CollatzResearch.WordTrace]
  refine ⟨28778133321245396975355559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153483377713308783868562981 28778133321245396975355559)
  ·
    refine ⟨43167199981868095463033339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28778133321245396975355559 43167199981868095463033339)
    ·
      refine ⟨64750799972802143194550009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43167199981868095463033339 64750799972802143194550009)
      ·
        refine ⟨48563099979601607395912507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64750799972802143194550009 48563099979601607395912507)
        ·
          refine ⟨72844649969402411093868761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48563099979601607395912507 72844649969402411093868761)
          ·
            refine ⟨54633487477051808320401571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72844649969402411093868761 54633487477051808320401571)
            ·
              refine ⟨81950231215577712480602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54633487477051808320401571 81950231215577712480602357)
              ·
                refine ⟨7682834176460410545056471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81950231215577712480602357 7682834176460410545056471)
                ·
                  refine ⟨11524251264690615817584707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682834176460410545056471 11524251264690615817584707)
                  ·
                    refine ⟨17286376897035923726377061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11524251264690615817584707 17286376897035923726377061)
                    ·
                      refine ⟨3241195668194235698695699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17286376897035923726377061 3241195668194235698695699)
                      ·
                        rfl

theorem cell23_6312206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6312206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312206 prefixEnd_6312206 := by exact prefixLift 6312206
  have htrace : WordTrace (prefixWord ++ tailWord_6312206) baseStart_6312206 baseEnd_6312206 := by
    simpa [prefixWord, tailWord_6312206, baseEnd_6312206] using wordTrace_append hprefix tailTrace_6312206
  have hstable : (prefixWord ++ tailWord_6312206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312206).length < 2 ^ (prefixWord ++ tailWord_6312206).sum := by decide
  have hdescent : baseEnd_6312206 < baseStart_6312206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312209 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_6312209 : Nat := 118140960795 + 6312209 * 2 ^ 59
def prefixEnd_6312209 : Nat := 4983230072969 + 3 ^ 40 * 6312209 * 2
def baseEnd_6312209 : Nat := 3241197208636199186958185

theorem tailTrace_6312209 : CollatzResearch.WordTrace tailWord_6312209 prefixEnd_6312209 3241197208636199186958185 := by
  unfold tailWord_6312209
  simp only [CollatzResearch.WordTrace]
  refine ⟨230225175988952307315203681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153483450659301538210135787 230225175988952307315203681)
  ·
    refine ⟨172668881991714230486402761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230225175988952307315203681 172668881991714230486402761)
    ·
      refine ⟨129501661493785672864802071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172668881991714230486402761 129501661493785672864802071)
      ·
        refine ⟨194252492240678509297203107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129501661493785672864802071 194252492240678509297203107)
        ·
          refine ⟨291378738361017763945804661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194252492240678509297203107 291378738361017763945804661)
          ·
            refine ⟨27316756721345415369919187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291378738361017763945804661 27316756721345415369919187)
            ·
              refine ⟨40975135082018123054878781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27316756721345415369919187 40975135082018123054878781)
              ·
                refine ⟨15365675655756796145579543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40975135082018123054878781 15365675655756796145579543)
                ·
                  refine ⟨23048513483635194218369315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15365675655756796145579543 23048513483635194218369315)
                  ·
                    refine ⟨34572770225452791327553973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23048513483635194218369315 34572770225452791327553973)
                    ·
                      refine ⟨3241197208636199186958185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34572770225452791327553973 3241197208636199186958185)
                      ·
                        rfl

theorem cell23_6312209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_6312209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312209 prefixEnd_6312209 := by exact prefixLift 6312209
  have htrace : WordTrace (prefixWord ++ tailWord_6312209) baseStart_6312209 baseEnd_6312209 := by
    simpa [prefixWord, tailWord_6312209, baseEnd_6312209] using wordTrace_append hprefix tailTrace_6312209
  have hstable : (prefixWord ++ tailWord_6312209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312209).length < 2 ^ (prefixWord ++ tailWord_6312209).sum := by decide
  have hdescent : baseEnd_6312209 < baseStart_6312209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312216 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_6312216 : Nat := 118140960795 + 6312216 * 2 ^ 59
def prefixEnd_6312216 : Nat := 4983230072969 + 3 ^ 40 * 6312216 * 2
def baseEnd_6312216 : Nat := 1080400267666926886523551

theorem tailTrace_6312216 : CollatzResearch.WordTrace tailWord_6312216 prefixEnd_6312216 1080400267666926886523551 := by
  unfold tailWord_6312216
  simp only [CollatzResearch.WordTrace]
  refine ⟨115112715649963473755354251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153483620866617965007139001 115112715649963473755354251)
  ·
    refine ⟨172669073474945210633031377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115112715649963473755354251 172669073474945210633031377)
    ·
      refine ⟨129501805106208907974773533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172669073474945210633031377 129501805106208907974773533)
      ·
        refine ⟨48563176914828340490540075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129501805106208907974773533 48563176914828340490540075)
        ·
          refine ⟨72844765372242510735810113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48563176914828340490540075 72844765372242510735810113)
          ·
            refine ⟨54633574029181883051857585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72844765372242510735810113 54633574029181883051857585)
            ·
              refine ⟨40975180521886412288893189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54633574029181883051857585 40975180521886412288893189)
              ·
                refine ⟨7682846347853702304167473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40975180521886412288893189 7682846347853702304167473)
                ·
                  refine ⟨5762134760890276728125605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682846347853702304167473 5762134760890276728125605)
                  ·
                    refine ⟨1080400267666926886523551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762134760890276728125605 1080400267666926886523551)
                    ·
                      rfl

theorem cell23_6312216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_6312216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312216 prefixEnd_6312216 := by exact prefixLift 6312216
  have htrace : WordTrace (prefixWord ++ tailWord_6312216) baseStart_6312216 baseEnd_6312216 := by
    simpa [prefixWord, tailWord_6312216, baseEnd_6312216] using wordTrace_append hprefix tailTrace_6312216
  have hstable : (prefixWord ++ tailWord_6312216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312216).length < 2 ^ (prefixWord ++ tailWord_6312216).sum := by decide
  have hdescent : baseEnd_6312216 < baseStart_6312216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312226 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_6312226 : Nat := 118140960795 + 6312226 * 2 ^ 59
def prefixEnd_6312226 : Nat := 4983230072969 + 3 ^ 40 * 6312226 * 2
def baseEnd_6312226 : Nat := 3241205937807325620445607

theorem tailTrace_6312226 : CollatzResearch.WordTrace tailWord_6312226 prefixEnd_6312226 3241205937807325620445607 := by
  unfold tailWord_6312226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57556449007472679804643133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153483864019927146145715021 57556449007472679804643133)
  ·
    refine ⟨21583668377802254926741175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57556449007472679804643133 21583668377802254926741175)
    ·
      refine ⟨32375502566703382390111763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583668377802254926741175 32375502566703382390111763)
      ·
        refine ⟨48563253850055073585167645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32375502566703382390111763 48563253850055073585167645)
        ·
          refine ⟨18211220193770652594437867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48563253850055073585167645 18211220193770652594437867)
          ·
            refine ⟨27316830290655978891656801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18211220193770652594437867 27316830290655978891656801)
            ·
              refine ⟨20487622717991984168742601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27316830290655978891656801 20487622717991984168742601)
              ·
                refine ⟨15365717038493988126556951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20487622717991984168742601 15365717038493988126556951)
                ·
                  refine ⟨23048575557740982189835427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15365717038493988126556951 23048575557740982189835427)
                  ·
                    refine ⟨34572863336611473284753141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23048575557740982189835427 34572863336611473284753141)
                    ·
                      refine ⟨3241205937807325620445607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34572863336611473284753141 3241205937807325620445607)
                      ·
                        rfl

theorem cell23_6312226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_6312226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312226 prefixEnd_6312226 := by exact prefixLift 6312226
  have htrace : WordTrace (prefixWord ++ tailWord_6312226) baseStart_6312226 baseEnd_6312226 := by
    simpa [prefixWord, tailWord_6312226, baseEnd_6312226] using wordTrace_append hprefix tailTrace_6312226
  have hstable : (prefixWord ++ tailWord_6312226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312226).length < 2 ^ (prefixWord ++ tailWord_6312226).sum := by decide
  have hdescent : baseEnd_6312226 < baseStart_6312226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312237 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6312237 : Nat := 118140960795 + 6312237 * 2 ^ 59
def prefixEnd_6312237 : Nat := 4983230072969 + 3 ^ 40 * 6312237 * 2
def baseEnd_6312237 : Nat := 1080403862031508359136019

theorem tailTrace_6312237 : CollatzResearch.WordTrace tailWord_6312237 prefixEnd_6312237 1080403862031508359136019 := by
  unfold tailWord_6312237
  simp only [CollatzResearch.WordTrace]
  refine ⟨230226197232850868097222965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153484131488567245398148643 230226197232850868097222965)
  ·
    refine ⟨21583705990579768884114653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230226197232850868097222965 21583705990579768884114653)
    ·
      refine ⟨8093889746467413331542995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21583705990579768884114653 8093889746467413331542995)
      ·
        refine ⟨12140834619701119997314493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093889746467413331542995 12140834619701119997314493)
        ·
          refine ⟨4552812982387919998992935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12140834619701119997314493 4552812982387919998992935)
          ·
            refine ⟨6829219473581879998489403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552812982387919998992935 6829219473581879998489403)
            ·
              refine ⟨10243829210372819997734105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829219473581879998489403 10243829210372819997734105)
              ·
                refine ⟨7682871907779614998300579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243829210372819997734105 7682871907779614998300579)
                ·
                  refine ⟨11524307861669422497450869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682871907779614998300579 11524307861669422497450869)
                  ·
                    refine ⟨1080403862031508359136019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11524307861669422497450869 1080403862031508359136019)
                    ·
                      rfl

theorem cell23_6312237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6312237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312237 prefixEnd_6312237 := by exact prefixLift 6312237
  have htrace : WordTrace (prefixWord ++ tailWord_6312237) baseStart_6312237 baseEnd_6312237 := by
    simpa [prefixWord, tailWord_6312237, baseEnd_6312237] using wordTrace_append hprefix tailTrace_6312237
  have hstable : (prefixWord ++ tailWord_6312237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312237).length < 2 ^ (prefixWord ++ tailWord_6312237).sum := by decide
  have hdescent : baseEnd_6312237 < baseStart_6312237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312256 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_6312256 : Nat := 118140960795 + 6312256 * 2 ^ 59
def prefixEnd_6312256 : Nat := 4983230072969 + 3 ^ 40 * 6312256 * 2
def baseEnd_6312256 : Nat := 3241221342226960503070469

theorem tailTrace_6312256 : CollatzResearch.WordTrace tailWord_6312256 prefixEnd_6312256 3241221342226960503070469 := by
  unfold tailWord_6312256
  simp only [CollatzResearch.WordTrace]
  refine ⟨115113445109891017171082311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153484593479854689561443081 115113445109891017171082311)
  ·
    refine ⟨172670167664836525756623467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115113445109891017171082311 172670167664836525756623467)
    ·
      refine ⟨259005251497254788634935201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172670167664836525756623467 259005251497254788634935201)
      ·
        refine ⟨194253938622941091476201401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259005251497254788634935201 194253938622941091476201401)
        ·
          refine ⟨145690453967205818607151051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194253938622941091476201401 145690453967205818607151051)
          ·
            refine ⟨218535680950808727910726577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145690453967205818607151051 218535680950808727910726577)
            ·
              refine ⟨163901760713106545933044933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218535680950808727910726577 163901760713106545933044933)
              ·
                refine ⟨30731580133707477362445925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163901760713106545933044933 30731580133707477362445925)
                ·
                  refine ⟨5762171275070152005458611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30731580133707477362445925 5762171275070152005458611)
                  ·
                    refine ⟨8643256912605228008187917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762171275070152005458611 8643256912605228008187917)
                    ·
                      refine ⟨3241221342226960503070469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643256912605228008187917 3241221342226960503070469)
                      ·
                        rfl

theorem cell23_6312256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_6312256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312256 prefixEnd_6312256 := by exact prefixLift 6312256
  have htrace : WordTrace (prefixWord ++ tailWord_6312256) baseStart_6312256 baseEnd_6312256 := by
    simpa [prefixWord, tailWord_6312256, baseEnd_6312256] using wordTrace_append hprefix tailTrace_6312256
  have hstable : (prefixWord ++ tailWord_6312256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312256).length < 2 ^ (prefixWord ++ tailWord_6312256).sum := by decide
  have hdescent : baseEnd_6312256 < baseStart_6312256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312260 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6312260 : Nat := 118140960795 + 6312260 * 2 ^ 59
def prefixEnd_6312260 : Nat := 4983230072969 + 3 ^ 40 * 6312260 * 2
def baseEnd_6312260 : Nat := 3241223396149578487420451

theorem tailTrace_6312260 : CollatzResearch.WordTrace tailWord_6312260 prefixEnd_6312260 3241223396149578487420451 := by
  unfold tailWord_6312260
  simp only [CollatzResearch.WordTrace]
  refine ⟨115113518055883771512655117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153484690741178362016873489 115113518055883771512655117)
  ·
    refine ⟨43167569270956414317245669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115113518055883771512655117 43167569270956414317245669)
    ·
      refine ⟨8093919238304327684483563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43167569270956414317245669 8093919238304327684483563)
      ·
        refine ⟨12140878857456491526725345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093919238304327684483563 12140878857456491526725345)
        ·
          refine ⟨9105659143092368645044009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140878857456491526725345 9105659143092368645044009)
          ·
            refine ⟨6829244357319276483783007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9105659143092368645044009 6829244357319276483783007)
            ·
              refine ⟨10243866535978914725674511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829244357319276483783007 10243866535978914725674511)
              ·
                refine ⟨15365799803968372088511767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243866535978914725674511 15365799803968372088511767)
                ·
                  refine ⟨23048699705952558132767651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15365799803968372088511767 23048699705952558132767651)
                  ·
                    refine ⟨34573049558928837199151477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23048699705952558132767651 34573049558928837199151477)
                    ·
                      refine ⟨3241223396149578487420451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34573049558928837199151477 3241223396149578487420451)
                      ·
                        rfl

theorem cell23_6312260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6312260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312260 prefixEnd_6312260 := by exact prefixLift 6312260
  have htrace : WordTrace (prefixWord ++ tailWord_6312260) baseStart_6312260 baseEnd_6312260 := by
    simpa [prefixWord, tailWord_6312260, baseEnd_6312260] using wordTrace_append hprefix tailTrace_6312260
  have hstable : (prefixWord ++ tailWord_6312260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312260).length < 2 ^ (prefixWord ++ tailWord_6312260).sum := by decide
  have hdescent : baseEnd_6312260 < baseStart_6312260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312273 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_6312273 : Nat := 118140960795 + 6312273 * 2 ^ 59
def prefixEnd_6312273 : Nat := 4983230072969 + 3 ^ 40 * 6312273 * 2
def baseEnd_6312273 : Nat := 3241230071398086936557891

theorem tailTrace_6312273 : CollatzResearch.WordTrace tailWord_6312273 prefixEnd_6312273 3241230071398086936557891 := by
  unfold tailWord_6312273
  simp only [CollatzResearch.WordTrace]
  refine ⟨230227510260720446245533473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153485006840480297497022315 230227510260720446245533473)
  ·
    refine ⟨172670632695540334684150105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230227510260720446245533473 172670632695540334684150105)
    ·
      refine ⟨129502974521655251013112579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172670632695540334684150105 129502974521655251013112579)
      ·
        refine ⟨194254461782482876519668869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129502974521655251013112579 194254461782482876519668869)
        ·
          refine ⟨36422711584215539347437913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194254461782482876519668869 36422711584215539347437913)
          ·
            refine ⟨27317033688161654510578435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36422711584215539347437913 27317033688161654510578435)
            ·
              refine ⟨40975550532242481765867653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27317033688161654510578435 40975550532242481765867653)
              ·
                refine ⟨7682915724795465331100185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40975550532242481765867653 7682915724795465331100185)
                ·
                  refine ⟨5762186793596598998325139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682915724795465331100185 5762186793596598998325139)
                  ·
                    refine ⟨8643280190394898497487709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762186793596598998325139 8643280190394898497487709)
                    ·
                      refine ⟨3241230071398086936557891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643280190394898497487709 3241230071398086936557891)
                      ·
                        rfl

theorem cell23_6312273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_6312273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312273 prefixEnd_6312273 := by exact prefixLift 6312273
  have htrace : WordTrace (prefixWord ++ tailWord_6312273) baseStart_6312273 baseEnd_6312273 := by
    simpa [prefixWord, tailWord_6312273, baseEnd_6312273] using wordTrace_append hprefix tailTrace_6312273
  have hstable : (prefixWord ++ tailWord_6312273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312273).length < 2 ^ (prefixWord ++ tailWord_6312273).sum := by decide
  have hdescent : baseEnd_6312273 < baseStart_6312273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312279 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_6312279 : Nat := 118140960795 + 6312279 * 2 ^ 59
def prefixEnd_6312279 : Nat := 4983230072969 + 3 ^ 40 * 6312279 * 2
def baseEnd_6312279 : Nat := 3241233152282013913082863

theorem tailTrace_6312279 : CollatzResearch.WordTrace tailWord_6312279 prefixEnd_6312279 3241233152282013913082863 := by
  unfold tailWord_6312279
  simp only [CollatzResearch.WordTrace]
  refine ⟨230227729098698709270251891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153485152732465806180167927 230227729098698709270251891)
  ·
    refine ⟨345341593648048063905377837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230227729098698709270251891 345341593648048063905377837)
    ·
      refine ⟨129503097618018023964516689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345341593648048063905377837 129503097618018023964516689)
      ·
        refine ⟨97127323213513517973387517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129503097618018023964516689 97127323213513517973387517)
        ·
          refine ⟨36422746205067569240020319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97127323213513517973387517 36422746205067569240020319)
          ·
            refine ⟨54634119307601353860030479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36422746205067569240020319 54634119307601353860030479)
            ·
              refine ⟨81951178961402030790045719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54634119307601353860030479 81951178961402030790045719)
              ·
                refine ⟨122926768442103046185068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81951178961402030790045719 122926768442103046185068579)
                ·
                  refine ⟨184390152663154569277602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122926768442103046185068579 184390152663154569277602869)
                  ·
                    refine ⟨17286576812170740869775269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184390152663154569277602869 17286576812170740869775269)
                    ·
                      refine ⟨3241233152282013913082863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17286576812170740869775269 3241233152282013913082863)
                      ·
                        rfl

theorem cell23_6312279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_6312279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312279 prefixEnd_6312279 := by exact prefixLift 6312279
  have htrace : WordTrace (prefixWord ++ tailWord_6312279) baseStart_6312279 baseEnd_6312279 := by
    simpa [prefixWord, tailWord_6312279, baseEnd_6312279] using wordTrace_append hprefix tailTrace_6312279
  have hstable : (prefixWord ++ tailWord_6312279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312279).length < 2 ^ (prefixWord ++ tailWord_6312279).sum := by decide
  have hdescent : baseEnd_6312279 < baseStart_6312279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312290 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6312290 : Nat := 118140960795 + 6312290 * 2 ^ 59
def prefixEnd_6312290 : Nat := 4983230072969 + 3 ^ 40 * 6312290 * 2
def baseEnd_6312290 : Nat := 3241238800569213370045313

theorem tailTrace_6312290 : CollatzResearch.WordTrace tailWord_6312290 prefixEnd_6312290 3241238800569213370045313 := by
  unfold tailWord_6312290
  simp only [CollatzResearch.WordTrace]
  refine ⟨57557032575414714537225581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153485420201105905432601549 57557032575414714537225581)
  ·
    refine ⟨21583887215780517951459593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57557032575414714537225581 21583887215780517951459593)
    ·
      refine ⟨16187915411835388463594695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21583887215780517951459593 16187915411835388463594695)
      ·
        refine ⟨24281873117753082695392043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16187915411835388463594695 24281873117753082695392043)
        ·
          refine ⟨36422809676629624043088065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24281873117753082695392043 36422809676629624043088065)
          ·
            refine ⟨27317107257472218032316049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36422809676629624043088065 27317107257472218032316049)
            ·
              refine ⟨20487830443104163524237037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27317107257472218032316049 20487830443104163524237037)
              ·
                refine ⟨7682936416164061321588889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20487830443104163524237037 7682936416164061321588889)
                ·
                  refine ⟨5762202312123045991191667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682936416164061321588889 5762202312123045991191667)
                  ·
                    refine ⟨8643303468184568986787501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762202312123045991191667 8643303468184568986787501)
                    ·
                      refine ⟨3241238800569213370045313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643303468184568986787501 3241238800569213370045313)
                      ·
                        rfl

theorem cell23_6312290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6312290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312290 prefixEnd_6312290 := by exact prefixLift 6312290
  have htrace : WordTrace (prefixWord ++ tailWord_6312290) baseStart_6312290 baseEnd_6312290 := by
    simpa [prefixWord, tailWord_6312290, baseEnd_6312290] using wordTrace_append hprefix tailTrace_6312290
  have hstable : (prefixWord ++ tailWord_6312290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312290).length < 2 ^ (prefixWord ++ tailWord_6312290).sum := by decide
  have hdescent : baseEnd_6312290 < baseStart_6312290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312313 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 4, 2, 2]
def baseStart_6312313 : Nat := 118140960795 + 6312313 * 2 ^ 59
def prefixEnd_6312313 : Nat := 4983230072969 + 3 ^ 40 * 6312313 * 2
def baseEnd_6312313 : Nat := 3241250610624266780057707

theorem tailTrace_6312313 : CollatzResearch.WordTrace tailWord_6312313 prefixEnd_6312313 3241250610624266780057707 := by
  unfold tailWord_6312313
  simp only [CollatzResearch.WordTrace]
  refine ⟨230228969180575533076989593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153485979453717022051326395 230228969180575533076989593)
  ·
    refine ⟨172671726885431649807742195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230228969180575533076989593 172671726885431649807742195)
    ·
      refine ⟨259007590328147474711613293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172671726885431649807742195 259007590328147474711613293)
      ·
        refine ⟨97127846373055303016854985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259007590328147474711613293 97127846373055303016854985)
        ·
          refine ⟨72845884779791477262641239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97127846373055303016854985 72845884779791477262641239)
          ·
            refine ⟨109268827169687215893961859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72845884779791477262641239 109268827169687215893961859)
            ·
              refine ⟨163903240754530823840942789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109268827169687215893961859 163903240754530823840942789)
              ·
                refine ⟨30731857641474529470176773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163903240754530823840942789 30731857641474529470176773)
                ·
                  refine ⟨5762223307776474275658145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30731857641474529470176773 5762223307776474275658145)
                  ·
                    refine ⟨4321667480832355706743609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762223307776474275658145 4321667480832355706743609)
                    ·
                      refine ⟨3241250610624266780057707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321667480832355706743609 3241250610624266780057707)
                      ·
                        rfl

theorem cell23_6312313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_6312313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312313 prefixEnd_6312313 := by exact prefixLift 6312313
  have htrace : WordTrace (prefixWord ++ tailWord_6312313) baseStart_6312313 baseEnd_6312313 := by
    simpa [prefixWord, tailWord_6312313, baseEnd_6312313] using wordTrace_append hprefix tailTrace_6312313
  have hstable : (prefixWord ++ tailWord_6312313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312313).length < 2 ^ (prefixWord ++ tailWord_6312313).sum := by decide
  have hdescent : baseEnd_6312313 < baseStart_6312313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312317 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_6312317 : Nat := 118140960795 + 6312317 * 2 ^ 59
def prefixEnd_6312317 : Nat := 4983230072969 + 3 ^ 40 * 6312317 * 2
def baseEnd_6312317 : Nat := 3241252664546884764407689

theorem tailTrace_6312317 : CollatzResearch.WordTrace tailWord_6312317 prefixEnd_6312317 3241252664546884764407689 := by
  unfold tailWord_6312317
  simp only [CollatzResearch.WordTrace]
  refine ⟨230229115072561041760135205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153486076715040694506756803 230229115072561041760135205)
  ·
    refine ⟨43167959076105195330025351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230229115072561041760135205 43167959076105195330025351)
    ·
      refine ⟨64751938614157792995038027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43167959076105195330025351 64751938614157792995038027)
      ·
        refine ⟨97127907921236689492557041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64751938614157792995038027 97127907921236689492557041)
        ·
          refine ⟨72845930940927517119417781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97127907921236689492557041 72845930940927517119417781)
          ·
            refine ⟨6829306025711954729945417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72845930940927517119417781 6829306025711954729945417)
            ·
              refine ⟨5121979519283966047459063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829306025711954729945417 5121979519283966047459063)
              ·
                refine ⟨7682969278925949071188595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121979519283966047459063 7682969278925949071188595)
                ·
                  refine ⟨11524453918388923606782893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682969278925949071188595 11524453918388923606782893)
                  ·
                    refine ⟨4321670219395846352543585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11524453918388923606782893 4321670219395846352543585)
                    ·
                      refine ⟨3241252664546884764407689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321670219395846352543585 3241252664546884764407689)
                      ·
                        rfl

theorem cell23_6312317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_6312317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312317 prefixEnd_6312317 := by exact prefixLift 6312317
  have htrace : WordTrace (prefixWord ++ tailWord_6312317) baseStart_6312317 baseEnd_6312317 := by
    simpa [prefixWord, tailWord_6312317, baseEnd_6312317] using wordTrace_append hprefix tailTrace_6312317
  have hstable : (prefixWord ++ tailWord_6312317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312317).length < 2 ^ (prefixWord ++ tailWord_6312317).sum := by decide
  have hdescent : baseEnd_6312317 < baseStart_6312317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312413 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6312413 : Nat := 118140960795 + 6312413 * 2 ^ 59
def prefixEnd_6312413 : Nat := 4983230072969 + 3 ^ 40 * 6312413 * 2
def baseEnd_6312413 : Nat := 1080433986229905462935749

theorem tailTrace_6312413 : CollatzResearch.WordTrace tailWord_6312413 prefixEnd_6312413 1080433986229905462935749 := by
  unfold tailWord_6312413
  simp only [CollatzResearch.WordTrace]
  refine ⟨230232616480213250155629893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153488410986808833437086595 230232616480213250155629893)
  ·
    refine ⟨43168615590039984404180605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230232616480213250155629893 43168615590039984404180605)
    ·
      refine ⟨16188230846264994151567727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43168615590039984404180605 16188230846264994151567727)
      ·
        refine ⟨24282346269397491227351591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188230846264994151567727 24282346269397491227351591)
        ·
          refine ⟨36423519404096236841027387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282346269397491227351591 36423519404096236841027387)
          ·
            refine ⟨54635279106144355261541081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36423519404096236841027387 54635279106144355261541081)
            ·
              refine ⟨40976459329608266446155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54635279106144355261541081 40976459329608266446155811)
              ·
                refine ⟨61464688994412399669233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40976459329608266446155811 61464688994412399669233717)
                ·
                  refine ⟨5762314593226162468990661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61464688994412399669233717 5762314593226162468990661)
                  ·
                    refine ⟨1080433986229905462935749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762314593226162468990661 1080433986229905462935749)
                    ·
                      rfl

theorem cell23_6312413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6312413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312413 prefixEnd_6312413 := by exact prefixLift 6312413
  have htrace : WordTrace (prefixWord ++ tailWord_6312413) baseStart_6312413 baseEnd_6312413 := by
    simpa [prefixWord, tailWord_6312413, baseEnd_6312413] using wordTrace_append hprefix tailTrace_6312413
  have hstable : (prefixWord ++ tailWord_6312413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312413).length < 2 ^ (prefixWord ++ tailWord_6312413).sum := by decide
  have hdescent : baseEnd_6312413 < baseStart_6312413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312454 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6312454 : Nat := 118140960795 + 6312454 * 2 ^ 59
def prefixEnd_6312454 : Nat := 4983230072969 + 3 ^ 40 * 6312454 * 2
def baseEnd_6312454 : Nat := 3241323011396550728394559

theorem tailTrace_6312454 : CollatzResearch.WordTrace tailWord_6312454 prefixEnd_6312454 3241323011396550728394559 := by
  unfold tailWord_6312454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194815996033272317433513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153489407915376476105248277 7194815996033272317433513)
  ·
    refine ⟨5396111997024954238075135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7194815996033272317433513 5396111997024954238075135)
    ·
      refine ⟨8094167995537431357112703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396111997024954238075135 8094167995537431357112703)
      ·
        refine ⟨12141251993306147035669055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094167995537431357112703 12141251993306147035669055)
        ·
          refine ⟨18211877989959220553503583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141251993306147035669055 18211877989959220553503583)
          ·
            refine ⟨27317816984938830830255375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18211877989959220553503583 27317816984938830830255375)
            ·
              refine ⟨40976725477408246245383063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27317816984938830830255375 40976725477408246245383063)
              ·
                refine ⟨61465088216112369368074595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40976725477408246245383063 61465088216112369368074595)
                ·
                  refine ⟨92197632324168554052111893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61465088216112369368074595 92197632324168554052111893)
                  ·
                    refine ⟨4321764015195400971192745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92197632324168554052111893 4321764015195400971192745)
                    ·
                      refine ⟨3241323011396550728394559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321764015195400971192745 3241323011396550728394559)
                      ·
                        rfl

theorem cell23_6312454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6312454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312454 prefixEnd_6312454 := by exact prefixLift 6312454
  have htrace : WordTrace (prefixWord ++ tailWord_6312454) baseStart_6312454 baseEnd_6312454 := by
    simpa [prefixWord, tailWord_6312454, baseEnd_6312454] using wordTrace_append hprefix tailTrace_6312454
  have hstable : (prefixWord ++ tailWord_6312454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312454).length < 2 ^ (prefixWord ++ tailWord_6312454).sum := by decide
  have hdescent : baseEnd_6312454 < baseStart_6312454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 6, 3, 2]
def baseStart_6312463 : Nat := 118140960795 + 6312463 * 2 ^ 59
def prefixEnd_6312463 : Nat := 4983230072969 + 3 ^ 40 * 6312463 * 2
def baseEnd_6312463 : Nat := 3241327632722441193182017

theorem tailTrace_6312463 : CollatzResearch.WordTrace tailWord_6312463 prefixEnd_6312463 3241327632722441193182017 := by
  unfold tailWord_6312463
  simp only [CollatzResearch.WordTrace]
  refine ⟨230234440130032108694950043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153489626753354739129966695 230234440130032108694950043)
  ·
    refine ⟨345351660195048163042425065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230234440130032108694950043 345351660195048163042425065)
    ·
      refine ⟨259013745146286122281818799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345351660195048163042425065 259013745146286122281818799)
      ·
        refine ⟨388520617719429183422728199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259013745146286122281818799 388520617719429183422728199)
        ·
          refine ⟨582780926579143775134092299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388520617719429183422728199 582780926579143775134092299)
          ·
            refine ⟨874171389868715662701138449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582780926579143775134092299 874171389868715662701138449)
            ·
              refine ⟨655628542401536747025853837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874171389868715662701138449 655628542401536747025853837)
              ·
                refine ⟨245860703400576280134695189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655628542401536747025853837 245860703400576280134695189)
                ·
                  refine ⟨11524720471902013131313837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 245860703400576280134695189 11524720471902013131313837)
                  ·
                    refine ⟨4321770176963254924242689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11524720471902013131313837 4321770176963254924242689)
                    ·
                      refine ⟨3241327632722441193182017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321770176963254924242689 3241327632722441193182017)
                      ·
                        rfl

theorem cell23_6312463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3, 2].length) (baseStart_6312463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312463 prefixEnd_6312463 := by exact prefixLift 6312463
  have htrace : WordTrace (prefixWord ++ tailWord_6312463) baseStart_6312463 baseEnd_6312463 := by
    simpa [prefixWord, tailWord_6312463, baseEnd_6312463] using wordTrace_append hprefix tailTrace_6312463
  have hstable : (prefixWord ++ tailWord_6312463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312463).length < 2 ^ (prefixWord ++ tailWord_6312463).sum := by decide
  have hdescent : baseEnd_6312463 < baseStart_6312463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312490 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6312490 : Nat := 118140960795 + 6312490 * 2 ^ 59
def prefixEnd_6312490 : Nat := 4983230072969 + 3 ^ 40 * 6312490 * 2
def baseEnd_6312490 : Nat := 1080447165566704195848131

theorem tailTrace_6312490 : CollatzResearch.WordTrace tailWord_6312490 prefixEnd_6312490 1080447165566704195848131 := by
  unfold tailWord_6312490
  simp only [CollatzResearch.WordTrace]
  refine ⟨57558856225233573076545731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153490283267289528204121949 57558856225233573076545731)
  ·
    refine ⟨86338284337850359614818597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57558856225233573076545731 86338284337850359614818597)
    ·
      refine ⟨16188428313346942427778487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86338284337850359614818597 16188428313346942427778487)
      ·
        refine ⟨24282642470020413641667731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188428313346942427778487 24282642470020413641667731)
        ·
          refine ⟨36423963705030620462501597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282642470020413641667731 36423963705030620462501597)
          ·
            refine ⟨13658986389386482673438099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36423963705030620462501597 13658986389386482673438099)
            ·
              refine ⟨20488479584079724010157149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658986389386482673438099 20488479584079724010157149)
              ·
                refine ⟨7683179844029896503808931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20488479584079724010157149 7683179844029896503808931)
                ·
                  refine ⟨11524769766044844755713397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7683179844029896503808931 11524769766044844755713397)
                  ·
                    refine ⟨1080447165566704195848131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11524769766044844755713397 1080447165566704195848131)
                    ·
                      rfl

theorem cell23_6312490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6312490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312490 prefixEnd_6312490 := by exact prefixLift 6312490
  have htrace : WordTrace (prefixWord ++ tailWord_6312490) baseStart_6312490 baseEnd_6312490 := by
    simpa [prefixWord, tailWord_6312490, baseEnd_6312490] using wordTrace_append hprefix tailTrace_6312490
  have hstable : (prefixWord ++ tailWord_6312490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312490).length < 2 ^ (prefixWord ++ tailWord_6312490).sum := by decide
  have hdescent : baseEnd_6312490 < baseStart_6312490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312503 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 4, 4]
def baseStart_6312503 : Nat := 118140960795 + 6312503 * 2 ^ 59
def prefixEnd_6312503 : Nat := 4983230072969 + 3 ^ 40 * 6312503 * 2
def baseEnd_6312503 : Nat := 1080449390649540345560611

theorem tailTrace_6312503 : CollatzResearch.WordTrace tailWord_6312503 prefixEnd_6312503 1080449390649540345560611 := by
  unfold tailWord_6312503
  simp only [CollatzResearch.WordTrace]
  refine ⟨230235899049887195526406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153490599366591463684270775 230235899049887195526406163)
  ·
    refine ⟨345353848574830793289609245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230235899049887195526406163 345353848574830793289609245)
    ·
      refine ⟨129507693215561547483603467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345353848574830793289609245 129507693215561547483603467)
      ·
        refine ⟨194261539823342321225405201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129507693215561547483603467 194261539823342321225405201)
        ·
          refine ⟨145696154867506740919053901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194261539823342321225405201 145696154867506740919053901)
          ·
            refine ⟨54636058075315027844645213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145696154867506740919053901 54636058075315027844645213)
            ·
              refine ⟨20488521778243135441741955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54636058075315027844645213 20488521778243135441741955)
              ·
                refine ⟨30732782667364703162612933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20488521778243135441741955 30732782667364703162612933)
                ·
                  refine ⟨5762396750130881842989925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30732782667364703162612933 5762396750130881842989925)
                  ·
                    refine ⟨1080449390649540345560611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762396750130881842989925 1080449390649540345560611)
                    ·
                      rfl

theorem cell23_6312503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_6312503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312503 prefixEnd_6312503 := by exact prefixLift 6312503
  have htrace : WordTrace (prefixWord ++ tailWord_6312503) baseStart_6312503 baseEnd_6312503 := by
    simpa [prefixWord, tailWord_6312503, baseEnd_6312503] using wordTrace_append hprefix tailTrace_6312503
  have hstable : (prefixWord ++ tailWord_6312503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312503).length < 2 ^ (prefixWord ++ tailWord_6312503).sum := by decide
  have hdescent : baseEnd_6312503 < baseStart_6312503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312513 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6312513 : Nat := 118140960795 + 6312513 * 2 ^ 59
def prefixEnd_6312513 : Nat := 4983230072969 + 3 ^ 40 * 6312513 * 2
def baseEnd_6312513 : Nat := 3241353306755165997556787

theorem tailTrace_6312513 : CollatzResearch.WordTrace tailWord_6312513 prefixEnd_6312513 3241353306755165997556787 := by
  unfold tailWord_6312513
  simp only [CollatzResearch.WordTrace]
  refine ⟨230236263779850967234270193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153490842519900644822846795 230236263779850967234270193)
  ·
    refine ⟨172677197834888225425702645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230236263779850967234270193 172677197834888225425702645)
    ·
      refine ⟨16188487297020771133659623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172677197834888225425702645 16188487297020771133659623)
      ·
        refine ⟨24282730945531156700489435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188487297020771133659623 24282730945531156700489435)
        ·
          refine ⟨36424096418296735050734153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282730945531156700489435 36424096418296735050734153)
          ·
            refine ⟨27318072313722551288050615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36424096418296735050734153 27318072313722551288050615)
            ·
              refine ⟨40977108470583826932075923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27318072313722551288050615 40977108470583826932075923)
              ·
                refine ⟨61465662705875740398113885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40977108470583826932075923 61465662705875740398113885)
                ·
                  refine ⟨23049623514703402649292707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61465662705875740398113885 23049623514703402649292707)
                  ·
                    refine ⟨34574435272055103973939061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23049623514703402649292707 34574435272055103973939061)
                    ·
                      refine ⟨3241353306755165997556787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34574435272055103973939061 3241353306755165997556787)
                      ·
                        rfl

theorem cell23_6312513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6312513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312513 prefixEnd_6312513 := by exact prefixLift 6312513
  have htrace : WordTrace (prefixWord ++ tailWord_6312513) baseStart_6312513 baseEnd_6312513 := by
    simpa [prefixWord, tailWord_6312513, baseEnd_6312513] using wordTrace_append hprefix tailTrace_6312513
  have hstable : (prefixWord ++ tailWord_6312513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312513).length < 2 ^ (prefixWord ++ tailWord_6312513).sum := by decide
  have hdescent : baseEnd_6312513 < baseStart_6312513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312523 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4]
def baseStart_6312523 : Nat := 118140960795 + 6312523 * 2 ^ 59
def prefixEnd_6312523 : Nat := 4983230072969 + 3 ^ 40 * 6312523 * 2
def baseEnd_6312523 : Nat := 3241358441561710958431741

theorem tailTrace_6312523 : CollatzResearch.WordTrace tailWord_6312523 prefixEnd_6312523 3241358441561710958431741 := by
  unfold tailWord_6312523
  simp only [CollatzResearch.WordTrace]
  refine ⟨230236628509814738942134223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153491085673209825961422815 230236628509814738942134223)
  ·
    refine ⟨345354942764722108413201335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230236628509814738942134223 345354942764722108413201335)
    ·
      refine ⟨518032414147083162619802003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345354942764722108413201335 518032414147083162619802003)
      ·
        refine ⟨777048621220624743929703005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518032414147083162619802003 777048621220624743929703005)
        ·
          refine ⟨291393232957734278973638627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 777048621220624743929703005 291393232957734278973638627)
          ·
            refine ⟨437089849436601418460457941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291393232957734278973638627 437089849436601418460457941)
            ·
              refine ⟨10244293346170345745166983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 437089849436601418460457941 10244293346170345745166983)
              ·
                refine ⟨15366440019255518617750475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244293346170345745166983 15366440019255518617750475)
                ·
                  refine ⟨23049660028883277926625713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15366440019255518617750475 23049660028883277926625713)
                  ·
                    refine ⟨17287245021662458444969285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23049660028883277926625713 17287245021662458444969285)
                    ·
                      refine ⟨3241358441561710958431741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17287245021662458444969285 3241358441561710958431741)
                      ·
                        rfl

theorem cell23_6312523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].length) (baseStart_6312523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312523 prefixEnd_6312523 := by exact prefixLift 6312523
  have htrace : WordTrace (prefixWord ++ tailWord_6312523) baseStart_6312523 baseEnd_6312523 := by
    simpa [prefixWord, tailWord_6312523, baseEnd_6312523] using wordTrace_append hprefix tailTrace_6312523
  have hstable : (prefixWord ++ tailWord_6312523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312523).length < 2 ^ (prefixWord ++ tailWord_6312523).sum := by decide
  have hdescent : baseEnd_6312523 < baseStart_6312523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312533 : List Nat := [1, 3, 2, 2, 1, 1, 6, 7]
def baseStart_6312533 : Nat := 118140960795 + 6312533 * 2 ^ 59
def prefixEnd_6312533 : Nat := 4983230072969 + 3 ^ 40 * 6312533 * 2
def baseEnd_6312533 : Nat := 120050502828453922937285

theorem tailTrace_6312533 : CollatzResearch.WordTrace tailWord_6312533 prefixEnd_6312533 120050502828453922937285 := by
  unfold tailWord_6312533
  simp only [CollatzResearch.WordTrace]
  refine ⟨230236993239778510649998253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153491328826519007099998835 230236993239778510649998253)
  ·
    refine ⟨86338872464916941493749345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230236993239778510649998253 86338872464916941493749345)
    ·
      refine ⟨64754154348687706120312009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86338872464916941493749345 64754154348687706120312009)
      ·
        refine ⟨48565615761515779590234007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64754154348687706120312009 48565615761515779590234007)
        ·
          refine ⟨72848423642273669385351011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48565615761515779590234007 72848423642273669385351011)
          ·
            refine ⟨109272635463410504078026517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72848423642273669385351011 109272635463410504078026517)
            ·
              refine ⟨5122154787347367378657493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109272635463410504078026517 5122154787347367378657493)
              ·
                refine ⟨120050502828453922937285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5122154787347367378657493 120050502828453922937285)
                ·
                  rfl

theorem cell23_6312533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 7].length) (baseStart_6312533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312533 prefixEnd_6312533 := by exact prefixLift 6312533
  have htrace : WordTrace (prefixWord ++ tailWord_6312533) baseStart_6312533 baseEnd_6312533 := by
    simpa [prefixWord, tailWord_6312533, baseEnd_6312533] using wordTrace_append hprefix tailTrace_6312533
  have hstable : (prefixWord ++ tailWord_6312533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312533).length < 2 ^ (prefixWord ++ tailWord_6312533).sum := by decide
  have hdescent : baseEnd_6312533 < baseStart_6312533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312543 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_6312543 : Nat := 118140960795 + 6312543 * 2 ^ 59
def prefixEnd_6312543 : Nat := 4983230072969 + 3 ^ 40 * 6312543 * 2
def baseEnd_6312543 : Nat := 3241368711174800880181649

theorem tailTrace_6312543 : CollatzResearch.WordTrace tailWord_6312543 prefixEnd_6312543 3241368711174800880181649 := by
  unfold tailWord_6312543
  simp only [CollatzResearch.WordTrace]
  refine ⟨230237357969742282357862283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153491571979828188238574855 230237357969742282357862283)
  ·
    refine ⟨345356036954613423536793425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230237357969742282357862283 345356036954613423536793425)
    ·
      refine ⟨259017027715960067652595069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345356036954613423536793425 259017027715960067652595069)
      ·
        refine ⟨97131385393485025369723151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259017027715960067652595069 97131385393485025369723151)
        ·
          refine ⟨145697078090227538054584727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97131385393485025369723151 145697078090227538054584727)
          ·
            refine ⟨218545617135341307081877091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145697078090227538054584727 218545617135341307081877091)
            ·
              refine ⟨327818425703011960622815637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218545617135341307081877091 327818425703011960622815637)
              ·
                refine ⟨15366488704828685654194483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327818425703011960622815637 15366488704828685654194483)
                ·
                  refine ⟨23049733057243028481291725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15366488704828685654194483 23049733057243028481291725)
                  ·
                    refine ⟨8643649896466135680484397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23049733057243028481291725 8643649896466135680484397)
                    ·
                      refine ⟨3241368711174800880181649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643649896466135680484397 3241368711174800880181649)
                      ·
                        rfl

theorem cell23_6312543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_6312543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312543 prefixEnd_6312543 := by exact prefixLift 6312543
  have htrace : WordTrace (prefixWord ++ tailWord_6312543) baseStart_6312543 baseEnd_6312543 := by
    simpa [prefixWord, tailWord_6312543, baseEnd_6312543] using wordTrace_append hprefix tailTrace_6312543
  have hstable : (prefixWord ++ tailWord_6312543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312543).length < 2 ^ (prefixWord ++ tailWord_6312543).sum := by decide
  have hdescent : baseEnd_6312543 < baseStart_6312543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312544 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 1, 2, 2]
def baseStart_6312544 : Nat := 118140960795 + 6312544 * 2 ^ 59
def prefixEnd_6312544 : Nat := 4983230072969 + 3 ^ 40 * 6312544 * 2
def baseEnd_6312544 : Nat := 3241369224655455376269145

theorem tailTrace_6312544 : CollatzResearch.WordTrace tailWord_6312544 prefixEnd_6312544 3241369224655455376269145 := by
  unfold tailWord_6312544
  simp only [CollatzResearch.WordTrace]
  refine ⟨115118697221369329764324343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153491596295159106352432457 115118697221369329764324343)
  ·
    refine ⟨172678045832053994646486515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115118697221369329764324343 172678045832053994646486515)
    ·
      refine ⟨259017068748080991969729773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172678045832053994646486515 259017068748080991969729773)
      ·
        refine ⟨97131400780530371988648665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259017068748080991969729773 97131400780530371988648665)
        ·
          refine ⟨72848550585397778991486499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97131400780530371988648665 72848550585397778991486499)
          ·
            refine ⟨109272825878096668487229749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72848550585397778991486499 109272825878096668487229749)
            ·
              refine ⟨10244327426071562670677789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109272825878096668487229749 10244327426071562670677789)
              ·
                refine ⟨3841622784776836001504171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10244327426071562670677789 3841622784776836001504171)
                ·
                  refine ⟨5762434177165254002256257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841622784776836001504171 5762434177165254002256257)
                  ·
                    refine ⟨4321825632873940501692193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762434177165254002256257 4321825632873940501692193)
                    ·
                      refine ⟨3241369224655455376269145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321825632873940501692193 3241369224655455376269145)
                      ·
                        rfl

theorem cell23_6312544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_6312544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312544 prefixEnd_6312544 := by exact prefixLift 6312544
  have htrace : WordTrace (prefixWord ++ tailWord_6312544) baseStart_6312544 baseEnd_6312544 := by
    simpa [prefixWord, tailWord_6312544, baseEnd_6312544] using wordTrace_append hprefix tailTrace_6312544
  have hstable : (prefixWord ++ tailWord_6312544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312544).length < 2 ^ (prefixWord ++ tailWord_6312544).sum := by decide
  have hdescent : baseEnd_6312544 < baseStart_6312544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312577 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6312577 : Nat := 118140960795 + 6312577 * 2 ^ 59
def prefixEnd_6312577 : Nat := 4983230072969 + 3 ^ 40 * 6312577 * 2
def baseEnd_6312577 : Nat := 3241386169517053747156493

theorem tailTrace_6312577 : CollatzResearch.WordTrace tailWord_6312577 prefixEnd_6312577 3241386169517053747156493 := by
  unfold tailWord_6312577
  simp only [CollatzResearch.WordTrace]
  refine ⟨230238598051619106164599985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153492398701079404109733323 230238598051619106164599985)
  ·
    refine ⟨172678948538714329623449989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230238598051619106164599985 172678948538714329623449989)
    ·
      refine ⟨32377302851008936804396873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172678948538714329623449989 32377302851008936804396873)
      ·
        refine ⟨24282977138256702603297655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32377302851008936804396873 24282977138256702603297655)
        ·
          refine ⟨36424465707385053904946483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282977138256702603297655 36424465707385053904946483)
          ·
            refine ⟨54636698561077580857419725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36424465707385053904946483 54636698561077580857419725)
            ·
              refine ⟨20488761960404092821532397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54636698561077580857419725 20488761960404092821532397)
              ·
                refine ⟨7683285735151534808074649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20488761960404092821532397 7683285735151534808074649)
                ·
                  refine ⟨5762464301363651106055987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683285735151534808074649 5762464301363651106055987)
                  ·
                    refine ⟨8643696452045476659083981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762464301363651106055987 8643696452045476659083981)
                    ·
                      refine ⟨3241386169517053747156493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643696452045476659083981 3241386169517053747156493)
                      ·
                        rfl

theorem cell23_6312577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6312577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312577 prefixEnd_6312577 := by exact prefixLift 6312577
  have htrace : WordTrace (prefixWord ++ tailWord_6312577) baseStart_6312577 baseEnd_6312577 := by
    simpa [prefixWord, tailWord_6312577, baseEnd_6312577] using wordTrace_append hprefix tailTrace_6312577
  have hstable : (prefixWord ++ tailWord_6312577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312577).length < 2 ^ (prefixWord ++ tailWord_6312577).sum := by decide
  have hdescent : baseEnd_6312577 < baseStart_6312577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312578 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6312578 : Nat := 118140960795 + 6312578 * 2 ^ 59
def prefixEnd_6312578 : Nat := 4983230072969 + 3 ^ 40 * 6312578 * 2
def baseEnd_6312578 : Nat := 3241386682997708243243989

theorem tailTrace_6312578 : CollatzResearch.WordTrace tailWord_6312578 prefixEnd_6312578 3241386682997708243243989 := by
  unfold tailWord_6312578
  simp only [CollatzResearch.WordTrace]
  refine ⟨57559658631153870833846597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153492423016410322223590925 57559658631153870833846597)
  ·
    refine ⟨10792435993341350781346237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57559658631153870833846597 10792435993341350781346237)
    ·
      refine ⟨4047163497503006543004839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10792435993341350781346237 4047163497503006543004839)
      ·
        refine ⟨6070745246254509814507259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047163497503006543004839 6070745246254509814507259)
        ·
          refine ⟨9106117869381764721760889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070745246254509814507259 9106117869381764721760889)
          ·
            refine ⟨6829588402036323541320667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9106117869381764721760889 6829588402036323541320667)
            ·
              refine ⟨10244382603054485311981001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829588402036323541320667 10244382603054485311981001)
              ·
                refine ⟨7683286952290863983985751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10244382603054485311981001 7683286952290863983985751)
                ·
                  refine ⟨11524930428436295975978627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7683286952290863983985751 11524930428436295975978627)
                  ·
                    refine ⟨17287395642654443963967941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11524930428436295975978627 17287395642654443963967941)
                    ·
                      refine ⟨3241386682997708243243989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17287395642654443963967941 3241386682997708243243989)
                      ·
                        rfl

theorem cell23_6312578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6312578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312578 prefixEnd_6312578 := by exact prefixLift 6312578
  have htrace : WordTrace (prefixWord ++ tailWord_6312578) baseStart_6312578 baseEnd_6312578 := by
    simpa [prefixWord, tailWord_6312578, baseEnd_6312578] using wordTrace_append hprefix tailTrace_6312578
  have hstable : (prefixWord ++ tailWord_6312578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312578).length < 2 ^ (prefixWord ++ tailWord_6312578).sum := by decide
  have hdescent : baseEnd_6312578 < baseStart_6312578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312613 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_6312613 : Nat := 118140960795 + 6312613 * 2 ^ 59
def prefixEnd_6312613 : Nat := 4983230072969 + 3 ^ 40 * 6312613 * 2
def baseEnd_6312613 : Nat := 3241404654820615606306327

theorem tailTrace_6312613 : CollatzResearch.WordTrace tailWord_6312613 prefixEnd_6312613 3241404654820615606306327 := by
  unfold tailWord_6312613
  simp only [CollatzResearch.WordTrace]
  refine ⟨230239911079488684312910493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153493274052992456208606995 230239911079488684312910493)
  ·
    refine ⟨86339966654808256617341435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230239911079488684312910493 86339966654808256617341435)
    ·
      refine ⟨129509949982212384926012153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86339966654808256617341435 129509949982212384926012153)
      ·
        refine ⟨97132462486659288694509115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129509949982212384926012153 97132462486659288694509115)
        ·
          refine ⟨145698693729988933041763673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97132462486659288694509115 145698693729988933041763673)
          ·
            refine ⟨109274020297491699781322755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145698693729988933041763673 109274020297491699781322755)
            ·
              refine ⟨163911030446237549671984133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109274020297491699781322755 163911030446237549671984133)
              ·
                refine ⟨30733318208669540563497025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163911030446237549671984133 30733318208669540563497025)
                ·
                  refine ⟨23049988656502155422622769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30733318208669540563497025 23049988656502155422622769)
                  ·
                    refine ⟨17287491492376616566967077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23049988656502155422622769 17287491492376616566967077)
                    ·
                      refine ⟨3241404654820615606306327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17287491492376616566967077 3241404654820615606306327)
                      ·
                        rfl

theorem cell23_6312613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_6312613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312613 prefixEnd_6312613 := by exact prefixLift 6312613
  have htrace : WordTrace (prefixWord ++ tailWord_6312613) baseStart_6312613 baseEnd_6312613 := by
    simpa [prefixWord, tailWord_6312613, baseEnd_6312613] using wordTrace_append hprefix tailTrace_6312613
  have hstable : (prefixWord ++ tailWord_6312613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312613).length < 2 ^ (prefixWord ++ tailWord_6312613).sum := by decide
  have hdescent : baseEnd_6312613 < baseStart_6312613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 2, 2, 2]
def baseStart_6312617 : Nat := 118140960795 + 6312617 * 2 ^ 59
def prefixEnd_6312617 : Nat := 4983230072969 + 3 ^ 40 * 6312617 * 2
def baseEnd_6312617 : Nat := 3241406708743233590656309

theorem tailTrace_6312617 : CollatzResearch.WordTrace tailWord_6312617 prefixEnd_6312617 3241406708743233590656309 := by
  unfold tailWord_6312617
  simp only [CollatzResearch.WordTrace]
  refine ⟨230240056971474192996056105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153493371314316128664037403 230240056971474192996056105)
  ·
    refine ⟨172680042728605644747042079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230240056971474192996056105 172680042728605644747042079)
    ·
      refine ⟨259020064092908467120563119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172680042728605644747042079 259020064092908467120563119)
      ·
        refine ⟨388530096139362700680844679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259020064092908467120563119 388530096139362700680844679)
        ·
          refine ⟨582795144209044051021267019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388530096139362700680844679 582795144209044051021267019)
          ·
            refine ⟨874192716313566076531900529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582795144209044051021267019 874192716313566076531900529)
            ·
              refine ⟨655644537235174557398925397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874192716313566076531900529 655644537235174557398925397)
              ·
                refine ⟨7683334420724701844518657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 655644537235174557398925397 7683334420724701844518657)
                ·
                  refine ⟨5762500815543526383388993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683334420724701844518657 5762500815543526383388993)
                  ·
                    refine ⟨4321875611657644787541745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762500815543526383388993 4321875611657644787541745)
                    ·
                      refine ⟨3241406708743233590656309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321875611657644787541745 3241406708743233590656309)
                      ·
                        rfl

theorem cell23_6312617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 2, 2].length) (baseStart_6312617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312617 prefixEnd_6312617 := by exact prefixLift 6312617
  have htrace : WordTrace (prefixWord ++ tailWord_6312617) baseStart_6312617 baseEnd_6312617 := by
    simpa [prefixWord, tailWord_6312617, baseEnd_6312617] using wordTrace_append hprefix tailTrace_6312617
  have hstable : (prefixWord ++ tailWord_6312617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312617).length < 2 ^ (prefixWord ++ tailWord_6312617).sum := by decide
  have hdescent : baseEnd_6312617 < baseStart_6312617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312668 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6312668 : Nat := 118140960795 + 6312668 * 2 ^ 59
def prefixEnd_6312668 : Nat := 4983230072969 + 3 ^ 40 * 6312668 * 2
def baseEnd_6312668 : Nat := 3241432896256612891118575

theorem tailTrace_6312668 : CollatzResearch.WordTrace tailWord_6312668 prefixEnd_6312668 3241432896256612891118575 := by
  unfold tailWord_6312668
  simp only [CollatzResearch.WordTrace]
  refine ⟨115120958547144714353081329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153494611396192952470775105 115120958547144714353081329)
  ·
    refine ⟨86340718910358535764810997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115120958547144714353081329 86340718910358535764810997)
    ·
      refine ⟨8094442397846112727951031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86340718910358535764810997 8094442397846112727951031)
      ·
        refine ⟨12141663596769169091926547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094442397846112727951031 12141663596769169091926547)
        ·
          refine ⟨18212495395153753637889821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141663596769169091926547 18212495395153753637889821)
          ·
            refine ⟨6829685773182657614208683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18212495395153753637889821 6829685773182657614208683)
            ·
              refine ⟨10244528659773986421313025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829685773182657614208683 10244528659773986421313025)
              ·
                refine ⟨7683396494830489815984769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10244528659773986421313025 7683396494830489815984769)
                ·
                  refine ⟨5762547371122867361988577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683396494830489815984769 5762547371122867361988577)
                  ·
                    refine ⟨4321910528342150521491433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762547371122867361988577 4321910528342150521491433)
                    ·
                      refine ⟨3241432896256612891118575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4321910528342150521491433 3241432896256612891118575)
                      ·
                        rfl

theorem cell23_6312668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6312668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312668 prefixEnd_6312668 := by exact prefixLift 6312668
  have htrace : WordTrace (prefixWord ++ tailWord_6312668) baseStart_6312668 baseEnd_6312668 := by
    simpa [prefixWord, tailWord_6312668, baseEnd_6312668] using wordTrace_append hprefix tailTrace_6312668
  have hstable : (prefixWord ++ tailWord_6312668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312668).length < 2 ^ (prefixWord ++ tailWord_6312668).sum := by decide
  have hdescent : baseEnd_6312668 < baseStart_6312668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312690 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6312690 : Nat := 118140960795 + 6312690 * 2 ^ 59
def prefixEnd_6312690 : Nat := 4983230072969 + 3 ^ 40 * 6312690 * 2
def baseEnd_6312690 : Nat := 3241444192831011805043473

theorem tailTrace_6312690 : CollatzResearch.WordTrace tailWord_6312690 prefixEnd_6312690 3241444192831011805043473 := by
  unfold tailWord_6312690
  simp only [CollatzResearch.WordTrace]
  refine ⟨57560679875052431615865881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153495146333473150975642349 57560679875052431615865881)
  ·
    refine ⟨43170509906289323711899411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57560679875052431615865881 43170509906289323711899411)
    ·
      refine ⟨64755764859433985567849117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43170509906289323711899411 64755764859433985567849117)
      ·
        refine ⟨24283411822287744587943419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64755764859433985567849117 24283411822287744587943419)
        ·
          refine ⟨36425117733431616881915129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24283411822287744587943419 36425117733431616881915129)
          ·
            refine ⟨27318838300073712661436347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36425117733431616881915129 27318838300073712661436347)
            ·
              refine ⟨40978257450110568992154521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27318838300073712661436347 40978257450110568992154521)
              ·
                refine ⟨30733693087582926744115891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40978257450110568992154521 30733693087582926744115891)
                ·
                  refine ⟨46100539631374390116173837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30733693087582926744115891 46100539631374390116173837)
                  ·
                    refine ⟨17287702361765396293565189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46100539631374390116173837 17287702361765396293565189)
                    ·
                      refine ⟨3241444192831011805043473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17287702361765396293565189 3241444192831011805043473)
                      ·
                        rfl

theorem cell23_6312690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6312690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312690 prefixEnd_6312690 := by exact prefixLift 6312690
  have htrace : WordTrace (prefixWord ++ tailWord_6312690) baseStart_6312690 baseEnd_6312690 := by
    simpa [prefixWord, tailWord_6312690, baseEnd_6312690] using wordTrace_append hprefix tailTrace_6312690
  have hstable : (prefixWord ++ tailWord_6312690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312690).length < 2 ^ (prefixWord ++ tailWord_6312690).sum := by decide
  have hdescent : baseEnd_6312690 < baseStart_6312690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312703 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_6312703 : Nat := 118140960795 + 6312703 * 2 ^ 59
def prefixEnd_6312703 : Nat := 4983230072969 + 3 ^ 40 * 6312703 * 2
def baseEnd_6312703 : Nat := 3241450868079520254180913

theorem tailTrace_6312703 : CollatzResearch.WordTrace tailWord_6312703 prefixEnd_6312703 3241450868079520254180913 := by
  unfold tailWord_6312703
  simp only [CollatzResearch.WordTrace]
  refine ⟨230243193649162629683686763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153495462432775086455791175 230243193649162629683686763)
  ·
    refine ⟨345364790473743944525530145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230243193649162629683686763 345364790473743944525530145)
    ·
      refine ⟨259023592855307958394147609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345364790473743944525530145 259023592855307958394147609)
      ·
        refine ⟨194267694641480968795610707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259023592855307958394147609 194267694641480968795610707)
        ·
          refine ⟨291401541962221453193416061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194267694641480968795610707 291401541962221453193416061)
          ·
            refine ⟨109275578235833044947531023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291401541962221453193416061 109275578235833044947531023)
            ·
              refine ⟨163913367353749567421296535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109275578235833044947531023 163913367353749567421296535)
              ·
                refine ⟨245870051030624351131944803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163913367353749567421296535 245870051030624351131944803)
                ·
                  refine ⟨368805076545936526697917205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245870051030624351131944803 368805076545936526697917205)
                  ·
                    refine ⟨17287737963090774688964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 368805076545936526697917205 17287737963090774688964869)
                    ·
                      refine ⟨3241450868079520254180913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17287737963090774688964869 3241450868079520254180913)
                      ·
                        rfl

theorem cell23_6312703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_6312703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312703 prefixEnd_6312703 := by exact prefixLift 6312703
  have htrace : WordTrace (prefixWord ++ tailWord_6312703) baseStart_6312703 baseEnd_6312703 := by
    simpa [prefixWord, tailWord_6312703, baseEnd_6312703] using wordTrace_append hprefix tailTrace_6312703
  have hstable : (prefixWord ++ tailWord_6312703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312703).length < 2 ^ (prefixWord ++ tailWord_6312703).sum := by decide
  have hdescent : baseEnd_6312703 < baseStart_6312703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312713 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 8]
def baseStart_6312713 : Nat := 118140960795 + 6312713 * 2 ^ 59
def prefixEnd_6312713 : Nat := 4983230072969 + 3 ^ 40 * 6312713 * 2
def baseEnd_6312713 : Nat := 360161778098451690561763

theorem tailTrace_6312713 : CollatzResearch.WordTrace tailWord_6312713 prefixEnd_6312713 360161778098451690561763 := by
  unfold tailWord_6312713
  simp only [CollatzResearch.WordTrace]
  refine ⟨230243558379126401391550793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153495705586084267594367195 230243558379126401391550793)
  ·
    refine ⟨172682668784344801043663095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230243558379126401391550793 172682668784344801043663095)
    ·
      refine ⟨259024003176517201565494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172682668784344801043663095 259024003176517201565494643)
      ·
        refine ⟨388536004764775802348241965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259024003176517201565494643 388536004764775802348241965)
        ·
          refine ⟨145701001786790925880590737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388536004764775802348241965 145701001786790925880590737)
          ·
            refine ⟨109275751340093194410443053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145701001786790925880590737 109275751340093194410443053)
            ·
              refine ⟨40978406752534947903916145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109275751340093194410443053 40978406752534947903916145)
              ·
                refine ⟨30733805064401210927937109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40978406752534947903916145 30733805064401210927937109)
                ·
                  refine ⟨360161778098451690561763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30733805064401210927937109 360161778098451690561763)
                  ·
                    rfl

theorem cell23_6312713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_6312713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312713 prefixEnd_6312713 := by exact prefixLift 6312713
  have htrace : WordTrace (prefixWord ++ tailWord_6312713) baseStart_6312713 baseEnd_6312713 := by
    simpa [prefixWord, tailWord_6312713, baseEnd_6312713] using wordTrace_append hprefix tailTrace_6312713
  have hstable : (prefixWord ++ tailWord_6312713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312713).length < 2 ^ (prefixWord ++ tailWord_6312713).sum := by decide
  have hdescent : baseEnd_6312713 < baseStart_6312713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312730 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_6312730 : Nat := 118140960795 + 6312730 * 2 ^ 59
def prefixEnd_6312730 : Nat := 4983230072969 + 3 ^ 40 * 6312730 * 2
def baseEnd_6312730 : Nat := 360162748006354627615921

theorem tailTrace_6312730 : CollatzResearch.WordTrace tailWord_6312730 prefixEnd_6312730 360162748006354627615921 := by
  unfold tailWord_6312730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57561044605016203323729911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153496118946709875529946429 57561044605016203323729911)
  ·
    refine ⟨86341566907524304985594867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57561044605016203323729911 86341566907524304985594867)
    ·
      refine ⟨129512350361286457478392301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86341566907524304985594867 129512350361286457478392301)
      ·
        refine ⟨48567131385482421554397113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129512350361286457478392301 48567131385482421554397113)
        ·
          refine ⟨36425348539111816165797835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48567131385482421554397113 36425348539111816165797835)
          ·
            refine ⟨54638022808667724248696753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36425348539111816165797835 54638022808667724248696753)
            ·
              refine ⟨40978517106500793186522565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54638022808667724248696753 40978517106500793186522565)
              ·
                refine ⟨7683471957468898722472981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40978517106500793186522565 7683471957468898722472981)
                ·
                  refine ⟨360162748006354627615921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7683471957468898722472981 360162748006354627615921)
                  ·
                    rfl

theorem cell23_6312730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_6312730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312730 prefixEnd_6312730 := by exact prefixLift 6312730
  have htrace : WordTrace (prefixWord ++ tailWord_6312730) baseStart_6312730 baseEnd_6312730 := by
    simpa [prefixWord, tailWord_6312730, baseEnd_6312730] using wordTrace_append hprefix tailTrace_6312730
  have hstable : (prefixWord ++ tailWord_6312730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312730).length < 2 ^ (prefixWord ++ tailWord_6312730).sum := by decide
  have hdescent : baseEnd_6312730 < baseStart_6312730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312760 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_6312760 : Nat := 118140960795 + 6312760 * 2 ^ 59
def prefixEnd_6312760 : Nat := 4983230072969 + 3 ^ 40 * 6312760 * 2
def baseEnd_6312760 : Nat := 1080493378825608843722717

theorem tailTrace_6312760 : CollatzResearch.WordTrace tailWord_6312760 prefixEnd_6312760 1080493378825608843722717 := by
  unfold tailWord_6312760
  simp only [CollatzResearch.WordTrace]
  refine ⟨115122636304978064209255867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153496848406637418945674489 115122636304978064209255867)
  ·
    refine ⟨172683954457467096313883801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115122636304978064209255867 172683954457467096313883801)
    ·
      refine ⟨129512965843100322235412851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172683954457467096313883801 129512965843100322235412851)
      ·
        refine ⟨194269448764650483353119277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129512965843100322235412851 194269448764650483353119277)
        ·
          refine ⟨72851043286743931257419729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194269448764650483353119277 72851043286743931257419729)
          ·
            refine ⟨54638282465057948443064797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72851043286743931257419729 54638282465057948443064797)
            ·
              refine ⟨20489355924396730666149299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54638282465057948443064797 20489355924396730666149299)
              ·
                refine ⟨30734033886595095999223949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489355924396730666149299 30734033886595095999223949)
                ·
                  refine ⟨11525262707473160999708981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30734033886595095999223949 11525262707473160999708981)
                  ·
                    refine ⟨1080493378825608843722717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11525262707473160999708981 1080493378825608843722717)
                    ·
                      rfl

theorem cell23_6312760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_6312760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312760 prefixEnd_6312760 := by exact prefixLift 6312760
  have htrace : WordTrace (prefixWord ++ tailWord_6312760) baseStart_6312760 baseEnd_6312760 := by
    simpa [prefixWord, tailWord_6312760, baseEnd_6312760] using wordTrace_append hprefix tailTrace_6312760
  have hstable : (prefixWord ++ tailWord_6312760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312760).length < 2 ^ (prefixWord ++ tailWord_6312760).sum := by decide
  have hdescent : baseEnd_6312760 < baseStart_6312760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312791 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_6312791 : Nat := 118140960795 + 6312791 * 2 ^ 59
def prefixEnd_6312791 : Nat := 4983230072969 + 3 ^ 40 * 6312791 * 2
def baseEnd_6312791 : Nat := 3241496054377115909880509

theorem tailTrace_6312791 : CollatzResearch.WordTrace tailWord_6312791 prefixEnd_6312791 3241496054377115909880509 := by
  unfold tailWord_6312791
  simp only [CollatzResearch.WordTrace]
  refine ⟨230246403272843820712890227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153497602181895880475260151 230246403272843820712890227)
  ·
    refine ⟨345369604909265731069335341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230246403272843820712890227 345369604909265731069335341)
    ·
      refine ⟨129513601840974649151000753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345369604909265731069335341 129513601840974649151000753)
      ·
        refine ⟨97135201380730986863250565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129513601840974649151000753 97135201380730986863250565)
        ·
          refine ⟨18212850258887060036859481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97135201380730986863250565 18212850258887060036859481)
          ·
            refine ⟨13659637694165295027644611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18212850258887060036859481 13659637694165295027644611)
            ·
              refine ⟨20489456541247942541466917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13659637694165295027644611 20489456541247942541466917)
              ·
                refine ⟨3841773101483989226525047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20489456541247942541466917 3841773101483989226525047)
                ·
                  refine ⟨5762659652225983839787571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841773101483989226525047 5762659652225983839787571)
                  ·
                    refine ⟨8643989478338975759681357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762659652225983839787571 8643989478338975759681357)
                    ·
                      refine ⟨3241496054377115909880509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8643989478338975759681357 3241496054377115909880509)
                      ·
                        rfl

theorem cell23_6312791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_6312791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312791 prefixEnd_6312791 := by exact prefixLift 6312791
  have htrace : WordTrace (prefixWord ++ tailWord_6312791) baseStart_6312791 baseEnd_6312791 := by
    simpa [prefixWord, tailWord_6312791, baseEnd_6312791] using wordTrace_append hprefix tailTrace_6312791
  have hstable : (prefixWord ++ tailWord_6312791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312791).length < 2 ^ (prefixWord ++ tailWord_6312791).sum := by decide
  have hdescent : baseEnd_6312791 < baseStart_6312791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312800 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6312800 : Nat := 118140960795 + 6312800 * 2 ^ 59
def prefixEnd_6312800 : Nat := 4983230072969 + 3 ^ 40 * 6312800 * 2
def baseEnd_6312800 : Nat := 3241500675703006374667967

theorem tailTrace_6312800 : CollatzResearch.WordTrace tailWord_6312800 prefixEnd_6312800 3241500675703006374667967 := by
  unfold tailWord_6312800
  simp only [CollatzResearch.WordTrace]
  refine ⟨115123365764905607624983927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153497821019874143499978569 115123365764905607624983927)
  ·
    refine ⟨172685048647358411437475891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115123365764905607624983927 172685048647358411437475891)
    ·
      refine ⟨259027572971037617156213837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172685048647358411437475891 259027572971037617156213837)
      ·
        refine ⟨97135339864139106433580189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259027572971037617156213837 97135339864139106433580189)
        ·
          refine ⟨36425752449052164912592571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97135339864139106433580189 36425752449052164912592571)
          ·
            refine ⟨54638628673578247368888857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36425752449052164912592571 54638628673578247368888857)
            ·
              refine ⟨40978971505183685526666643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54638628673578247368888857 40978971505183685526666643)
              ·
                refine ⟨61468457257775528289999965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40978971505183685526666643 61468457257775528289999965)
                ·
                  refine ⟨23050671471665823108749987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61468457257775528289999965 23050671471665823108749987)
                  ·
                    refine ⟨34576007207498734663124981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23050671471665823108749987 34576007207498734663124981)
                    ·
                      refine ⟨3241500675703006374667967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34576007207498734663124981 3241500675703006374667967)
                      ·
                        rfl

theorem cell23_6312800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6312800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312800 prefixEnd_6312800 := by exact prefixLift 6312800
  have htrace : WordTrace (prefixWord ++ tailWord_6312800) baseStart_6312800 baseEnd_6312800 := by
    simpa [prefixWord, tailWord_6312800, baseEnd_6312800] using wordTrace_append hprefix tailTrace_6312800
  have hstable : (prefixWord ++ tailWord_6312800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312800).length < 2 ^ (prefixWord ++ tailWord_6312800).sum := by decide
  have hdescent : baseEnd_6312800 < baseStart_6312800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312807 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 6]
def baseStart_6312807 : Nat := 118140960795 + 6312807 * 2 ^ 59
def prefixEnd_6312807 : Nat := 4983230072969 + 3 ^ 40 * 6312807 * 2
def baseEnd_6312807 : Nat := 1080501423355862615760145

theorem tailTrace_6312807 : CollatzResearch.WordTrace tailWord_6312807 prefixEnd_6312807 1080501423355862615760145 := by
  unfold tailWord_6312807
  simp only [CollatzResearch.WordTrace]
  refine ⟨230246986840785855445472675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153497991227190570296981783 230246986840785855445472675)
  ·
    refine ⟨345370480261178783168209013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230246986840785855445472675 345370480261178783168209013)
    ·
      refine ⟨32378482524485510922019595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345370480261178783168209013 32378482524485510922019595)
      ·
        refine ⟨48567723786728266383029393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32378482524485510922019595 48567723786728266383029393)
        ·
          refine ⟨36425792840046199787272045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48567723786728266383029393 36425792840046199787272045)
          ·
            refine ⟨13659672315017324920227017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36425792840046199787272045 13659672315017324920227017)
            ·
              refine ⟨10244754236262993690170263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13659672315017324920227017 10244754236262993690170263)
              ·
                refine ⟨15367131354394490535255395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244754236262993690170263 15367131354394490535255395)
                ·
                  refine ⟨23050697031591735802883093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15367131354394490535255395 23050697031591735802883093)
                  ·
                    refine ⟨1080501423355862615760145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23050697031591735802883093 1080501423355862615760145)
                    ·
                      rfl

theorem cell23_6312807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_6312807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312807 prefixEnd_6312807 := by exact prefixLift 6312807
  have htrace : WordTrace (prefixWord ++ tailWord_6312807) baseStart_6312807 baseEnd_6312807 := by
    simpa [prefixWord, tailWord_6312807, baseEnd_6312807] using wordTrace_append hprefix tailTrace_6312807
  have hstable : (prefixWord ++ tailWord_6312807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312807).length < 2 ^ (prefixWord ++ tailWord_6312807).sum := by decide
  have hdescent : baseEnd_6312807 < baseStart_6312807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312817 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_6312817 : Nat := 118140960795 + 6312817 * 2 ^ 59
def prefixEnd_6312817 : Nat := 4983230072969 + 3 ^ 40 * 6312817 * 2
def baseEnd_6312817 : Nat := 3241509404874132808155389

theorem tailTrace_6312817 : CollatzResearch.WordTrace tailWord_6312817 prefixEnd_6312817 3241509404874132808155389 := by
  unfold tailWord_6312817
  simp only [CollatzResearch.WordTrace]
  refine ⟨230247351570749627153336705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153498234380499751435557803 230247351570749627153336705)
  ·
    refine ⟨172685513678062220365002529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230247351570749627153336705 172685513678062220365002529)
    ·
      refine ⟨129514135258546665273751897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172685513678062220365002529 129514135258546665273751897)
      ·
        refine ⟨97135601443909998955313923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129514135258546665273751897 97135601443909998955313923)
        ·
          refine ⟨145703402165864998432970885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97135601443909998955313923 145703402165864998432970885)
          ·
            refine ⟨27319387906099687206182041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145703402165864998432970885 27319387906099687206182041)
            ·
              refine ⟨20489540929574765404636531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27319387906099687206182041 20489540929574765404636531)
              ·
                refine ⟨30734311394362148106954797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489540929574765404636531 30734311394362148106954797)
                ·
                  refine ⟨11525366772885805540108049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30734311394362148106954797 11525366772885805540108049)
                  ·
                    refine ⟨8644025079664354155081037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11525366772885805540108049 8644025079664354155081037)
                    ·
                      refine ⟨3241509404874132808155389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644025079664354155081037 3241509404874132808155389)
                      ·
                        rfl

theorem cell23_6312817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_6312817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312817 prefixEnd_6312817 := by exact prefixLift 6312817
  have htrace : WordTrace (prefixWord ++ tailWord_6312817) baseStart_6312817 baseEnd_6312817 := by
    simpa [prefixWord, tailWord_6312817, baseEnd_6312817] using wordTrace_append hprefix tailTrace_6312817
  have hstable : (prefixWord ++ tailWord_6312817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312817).length < 2 ^ (prefixWord ++ tailWord_6312817).sum := by decide
  have hdescent : baseEnd_6312817 < baseStart_6312817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312831 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 1, 2, 2]
def baseStart_6312831 : Nat := 118140960795 + 6312831 * 2 ^ 59
def prefixEnd_6312831 : Nat := 4983230072969 + 3 ^ 40 * 6312831 * 2
def baseEnd_6312831 : Nat := 3241516593603295753380325

theorem tailTrace_6312831 : CollatzResearch.WordTrace tailWord_6312831 prefixEnd_6312831 3241516593603295753380325 := by
  unfold tailWord_6312831
  simp only [CollatzResearch.WordTrace]
  refine ⟨230247862192698907544346347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153498574795132605029564231 230247862192698907544346347)
  ·
    refine ⟨345371793289048361316519521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230247862192698907544346347 345371793289048361316519521)
    ·
      refine ⟨259028844966786270987389641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345371793289048361316519521 259028844966786270987389641)
      ·
        refine ⟨194271633725089703240542231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259028844966786270987389641 194271633725089703240542231)
        ·
          refine ⟨291407450587634554860813347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194271633725089703240542231 291407450587634554860813347)
          ·
            refine ⟨437111175881451832291220021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291407450587634554860813347 437111175881451832291220021)
            ·
              refine ⟨40979172738886109277301877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437111175881451832291220021 40979172738886109277301877)
              ·
                refine ⟨3841797444270572744747051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40979172738886109277301877 3841797444270572744747051)
                ·
                  refine ⟨5762696166405859117120577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841797444270572744747051 5762696166405859117120577)
                  ·
                    refine ⟨4322022124804394337840433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762696166405859117120577 4322022124804394337840433)
                    ·
                      refine ⟨3241516593603295753380325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322022124804394337840433 3241516593603295753380325)
                      ·
                        rfl

theorem cell23_6312831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_6312831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312831 prefixEnd_6312831 := by exact prefixLift 6312831
  have htrace : WordTrace (prefixWord ++ tailWord_6312831) baseStart_6312831 baseEnd_6312831 := by
    simpa [prefixWord, tailWord_6312831, baseEnd_6312831] using wordTrace_append hprefix tailTrace_6312831
  have hstable : (prefixWord ++ tailWord_6312831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312831).length < 2 ^ (prefixWord ++ tailWord_6312831).sum := by decide
  have hdescent : baseEnd_6312831 < baseStart_6312831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312864 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_6312864 : Nat := 118140960795 + 6312864 * 2 ^ 59
def prefixEnd_6312864 : Nat := 4983230072969 + 3 ^ 40 * 6312864 * 2
def baseEnd_6312864 : Nat := 3241533538464894124267673

theorem tailTrace_6312864 : CollatzResearch.WordTrace tailWord_6312864 prefixEnd_6312864 3241533538464894124267673 := by
  unfold tailWord_6312864
  simp only [CollatzResearch.WordTrace]
  refine ⟨115124532900789677090148823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153499377201052902786865097 115124532900789677090148823)
  ·
    refine ⟨172686799351184515635223235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115124532900789677090148823 172686799351184515635223235)
    ·
      refine ⟨259030199026776773452834853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172686799351184515635223235 259030199026776773452834853)
      ·
        refine ⟨48568162317520645022406535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259030199026776773452834853 48568162317520645022406535)
        ·
          refine ⟨72852243476280967533609803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48568162317520645022406535 72852243476280967533609803)
          ·
            refine ⟨109278365214421451300414705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72852243476280967533609803 109278365214421451300414705)
            ·
              refine ⟨81958773910816088475311029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109278365214421451300414705 81958773910816088475311029)
              ·
                refine ⟨7683635054139008294560409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81958773910816088475311029 7683635054139008294560409)
                ·
                  refine ⟨5762726290604256220920307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683635054139008294560409 5762726290604256220920307)
                  ·
                    refine ⟨8644089435906384331380461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5762726290604256220920307 8644089435906384331380461)
                    ·
                      refine ⟨3241533538464894124267673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644089435906384331380461 3241533538464894124267673)
                      ·
                        rfl

theorem cell23_6312864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_6312864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312864 prefixEnd_6312864 := by exact prefixLift 6312864
  have htrace : WordTrace (prefixWord ++ tailWord_6312864) baseStart_6312864 baseEnd_6312864 := by
    simpa [prefixWord, tailWord_6312864, baseEnd_6312864] using wordTrace_append hprefix tailTrace_6312864
  have hstable : (prefixWord ++ tailWord_6312864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312864).length < 2 ^ (prefixWord ++ tailWord_6312864).sum := by decide
  have hdescent : baseEnd_6312864 < baseStart_6312864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312871 : List Nat := [1, 1, 6, 1, 4, 1, 2, 7]
def baseStart_6312871 : Nat := 118140960795 + 6312871 * 2 ^ 59
def prefixEnd_6312871 : Nat := 4983230072969 + 3 ^ 40 * 6312871 * 2
def baseEnd_6312871 : Nat := 120056930845536133217783

theorem tailTrace_6312871 : CollatzResearch.WordTrace tailWord_6312871 prefixEnd_6312871 120056930845536133217783 := by
  unfold tailWord_6312871
  simp only [CollatzResearch.WordTrace]
  refine ⟨230249321112553994375802467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153499547408369329583868311 230249321112553994375802467)
  ·
    refine ⟨345373981668830991563703701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230249321112553994375802467 345373981668830991563703701)
    ·
      refine ⟨16189405390726452729548611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 345373981668830991563703701 16189405390726452729548611)
      ·
        refine ⟨24284108086089679094322917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16189405390726452729548611 24284108086089679094322917)
        ·
          refine ⟨4553270266141814830185547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24284108086089679094322917 4553270266141814830185547)
          ·
            refine ⟨6829905399212722245278321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553270266141814830185547 6829905399212722245278321)
            ·
              refine ⟨5122429049409541683958741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829905399212722245278321 5122429049409541683958741)
              ·
                refine ⟨120056930845536133217783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5122429049409541683958741 120056930845536133217783)
                ·
                  rfl

theorem cell23_6312871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 7].length) (baseStart_6312871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312871 prefixEnd_6312871 := by exact prefixLift 6312871
  have htrace : WordTrace (prefixWord ++ tailWord_6312871) baseStart_6312871 baseEnd_6312871 := by
    simpa [prefixWord, tailWord_6312871, baseEnd_6312871] using wordTrace_append hprefix tailTrace_6312871
  have hstable : (prefixWord ++ tailWord_6312871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312871).length < 2 ^ (prefixWord ++ tailWord_6312871).sum := by decide
  have hdescent : baseEnd_6312871 < baseStart_6312871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312909 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6312909 : Nat := 118140960795 + 6312909 * 2 ^ 59
def prefixEnd_6312909 : Nat := 4983230072969 + 3 ^ 40 * 6312909 * 2
def baseEnd_6312909 : Nat := 1080518881698115482734989

theorem tailTrace_6312909 : CollatzResearch.WordTrace tailWord_6312909 prefixEnd_6312909 1080518881698115482734989 := by
  unfold tailWord_6312909
  simp only [CollatzResearch.WordTrace]
  refine ⟨230250707086416326865685781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153500471390944217910457187 230250707086416326865685781)
  ·
    refine ⟨10793001894675765321829021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230250707086416326865685781 10793001894675765321829021)
    ·
      refine ⟨4047375710503411995685883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10793001894675765321829021 4047375710503411995685883)
      ·
        refine ⟨6071063565755117993528825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047375710503411995685883 6071063565755117993528825)
        ·
          refine ⟨4553297674316338495146619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6071063565755117993528825 4553297674316338495146619)
          ·
            refine ⟨6829946511474507742719929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553297674316338495146619 6829946511474507742719929)
            ·
              refine ⟨5122459883605880807039947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829946511474507742719929 5122459883605880807039947)
              ·
                refine ⟨7683689825408821210559921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122459883605880807039947 7683689825408821210559921)
                ·
                  refine ⟨5762767369056615907919941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683689825408821210559921 5762767369056615907919941)
                  ·
                    refine ⟨1080518881698115482734989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762767369056615907919941 1080518881698115482734989)
                    ·
                      rfl

theorem cell23_6312909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6312909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312909 prefixEnd_6312909 := by exact prefixLift 6312909
  have htrace : WordTrace (prefixWord ++ tailWord_6312909) baseStart_6312909 baseEnd_6312909 := by
    simpa [prefixWord, tailWord_6312909, baseEnd_6312909] using wordTrace_append hprefix tailTrace_6312909
  have hstable : (prefixWord ++ tailWord_6312909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312909).length < 2 ^ (prefixWord ++ tailWord_6312909).sum := by decide
  have hdescent : baseEnd_6312909 < baseStart_6312909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312961 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 5]
def baseStart_6312961 : Nat := 118140960795 + 6312961 * 2 ^ 59
def prefixEnd_6312961 : Nat := 4983230072969 + 3 ^ 40 * 6312961 * 2
def baseEnd_6312961 : Nat := 360175927343153360528303

theorem tailTrace_6312961 : CollatzResearch.WordTrace tailWord_6312961 prefixEnd_6312961 360175927343153360528303 := by
  unfold tailWord_6312961
  simp only [CollatzResearch.WordTrace]
  refine ⟨230252603682227939746578737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153501735788151959831052491 230252603682227939746578737)
  ·
    refine ⟨172689452761670954809934053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230252603682227939746578737 172689452761670954809934053)
    ·
      refine ⟨32379272392813304026862635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172689452761670954809934053 32379272392813304026862635)
      ·
        refine ⟨48568908589219956040293953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32379272392813304026862635 48568908589219956040293953)
        ·
          refine ⟨36426681441914967030220465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48568908589219956040293953 36426681441914967030220465)
          ·
            refine ⟨27320011081436225272665349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36426681441914967030220465 27320011081436225272665349)
            ·
              refine ⟨5122502077769292238624753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27320011081436225272665349 5122502077769292238624753)
              ·
                refine ⟨3841876558326969178968565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122502077769292238624753 3841876558326969178968565)
                ·
                  refine ⟨360175927343153360528303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841876558326969178968565 360175927343153360528303)
                  ·
                    rfl

theorem cell23_6312961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 5].length) (baseStart_6312961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312961 prefixEnd_6312961 := by exact prefixLift 6312961
  have htrace : WordTrace (prefixWord ++ tailWord_6312961) baseStart_6312961 baseEnd_6312961 := by
    simpa [prefixWord, tailWord_6312961, baseEnd_6312961] using wordTrace_append hprefix tailTrace_6312961
  have hstable : (prefixWord ++ tailWord_6312961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312961).length < 2 ^ (prefixWord ++ tailWord_6312961).sum := by decide
  have hdescent : baseEnd_6312961 < baseStart_6312961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312967 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6312967 : Nat := 118140960795 + 6312967 * 2 ^ 59
def prefixEnd_6312967 : Nat := 4983230072969 + 3 ^ 40 * 6312967 * 2
def baseEnd_6312967 : Nat := 3241586426972307221279699

theorem tailTrace_6312967 : CollatzResearch.WordTrace tailWord_6312967 prefixEnd_6312967 3241586426972307221279699 := by
  unfold tailWord_6312967
  simp only [CollatzResearch.WordTrace]
  refine ⟨230252822520206202771297155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153501881680137468514198103 230252822520206202771297155)
  ·
    refine ⟨345379233780309304156945733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230252822520206202771297155 345379233780309304156945733)
    ·
      refine ⟨64758606333807994529427325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345379233780309304156945733 64758606333807994529427325)
      ·
        refine ⟨24284477375177997948535247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64758606333807994529427325 24284477375177997948535247)
        ·
          refine ⟨36426716062766996922802871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24284477375177997948535247 36426716062766996922802871)
          ·
            refine ⟨54640074094150495384204307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36426716062766996922802871 54640074094150495384204307)
            ·
              refine ⟨81960111141225743076306461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54640074094150495384204307 81960111141225743076306461)
              ·
                refine ⟨30735041677959653653614923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81960111141225743076306461 30735041677959653653614923)
                ·
                  refine ⟨46102562516939480480422385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30735041677959653653614923 46102562516939480480422385)
                  ·
                    refine ⟨34576921887704610360316789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46102562516939480480422385 34576921887704610360316789)
                    ·
                      refine ⟨3241586426972307221279699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34576921887704610360316789 3241586426972307221279699)
                      ·
                        rfl

theorem cell23_6312967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6312967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312967 prefixEnd_6312967 := by exact prefixLift 6312967
  have htrace : WordTrace (prefixWord ++ tailWord_6312967) baseStart_6312967 baseEnd_6312967 := by
    simpa [prefixWord, tailWord_6312967, baseEnd_6312967] using wordTrace_append hprefix tailTrace_6312967
  have hstable : (prefixWord ++ tailWord_6312967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312967).length < 2 ^ (prefixWord ++ tailWord_6312967).sum := by decide
  have hdescent : baseEnd_6312967 < baseStart_6312967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312977 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_6312977 : Nat := 118140960795 + 6312977 * 2 ^ 59
def prefixEnd_6312977 : Nat := 4983230072969 + 3 ^ 40 * 6312977 * 2
def baseEnd_6312977 : Nat := 3241591561778852182154653

theorem tailTrace_6312977 : CollatzResearch.WordTrace tailWord_6312977 prefixEnd_6312977 3241591561778852182154653 := by
  unfold tailWord_6312977
  simp only [CollatzResearch.WordTrace]
  refine ⟨230253187250169974479161185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153502124833446649652774123 230253187250169974479161185)
  ·
    refine ⟨172689890437627480859370889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230253187250169974479161185 172689890437627480859370889)
    ·
      refine ⟨129517417828220610644528167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172689890437627480859370889 129517417828220610644528167)
      ·
        refine ⟨194276126742330915966792251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129517417828220610644528167 194276126742330915966792251)
        ·
          refine ⟨291414190113496373950188377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194276126742330915966792251 291414190113496373950188377)
          ·
            refine ⟨218560642585122280462641283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291414190113496373950188377 218560642585122280462641283)
            ·
              refine ⟨327840963877683420693961925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218560642585122280462641283 327840963877683420693961925)
              ·
                refine ⟨61470180727065641380117861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327840963877683420693961925 61470180727065641380117861)
                ·
                  refine ⟨11525658886324807758772099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61470180727065641380117861 11525658886324807758772099)
                  ·
                    refine ⟨17288488329487211638158149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11525658886324807758772099 17288488329487211638158149)
                    ·
                      refine ⟨3241591561778852182154653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17288488329487211638158149 3241591561778852182154653)
                      ·
                        rfl

theorem cell23_6312977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_6312977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312977 prefixEnd_6312977 := by exact prefixLift 6312977
  have htrace : WordTrace (prefixWord ++ tailWord_6312977) baseStart_6312977 baseEnd_6312977 := by
    simpa [prefixWord, tailWord_6312977, baseEnd_6312977] using wordTrace_append hprefix tailTrace_6312977
  have hstable : (prefixWord ++ tailWord_6312977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312977).length < 2 ^ (prefixWord ++ tailWord_6312977).sum := by decide
  have hdescent : baseEnd_6312977 < baseStart_6312977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312978 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_6312978 : Nat := 118140960795 + 6312978 * 2 ^ 59
def prefixEnd_6312978 : Nat := 4983230072969 + 3 ^ 40 * 6312978 * 2
def baseEnd_6312978 : Nat := 360176897251056297582461

theorem tailTrace_6312978 : CollatzResearch.WordTrace tailWord_6312978 prefixEnd_6312978 360176897251056297582461 := by
  unfold tailWord_6312978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57563305930791587912486897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153502149148777567766631725 57563305930791587912486897)
  ·
    refine ⟨43172479448093690934365173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57563305930791587912486897 43172479448093690934365173)
    ·
      refine ⟨4047419948258783525096735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43172479448093690934365173 4047419948258783525096735)
      ·
        refine ⟨6071129922388175287645103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047419948258783525096735 6071129922388175287645103)
        ·
          refine ⟨9106694883582262931467655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071129922388175287645103 9106694883582262931467655)
          ·
            refine ⟨13660042325373394397201483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9106694883582262931467655 13660042325373394397201483)
            ·
              refine ⟨20490063488060091595802225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13660042325373394397201483 20490063488060091595802225)
              ·
                refine ⟨15367547616045068696851669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20490063488060091595802225 15367547616045068696851669)
                ·
                  refine ⟨360176897251056297582461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15367547616045068696851669 360176897251056297582461)
                  ·
                    rfl

theorem cell23_6312978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_6312978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312978 prefixEnd_6312978 := by exact prefixLift 6312978
  have htrace : WordTrace (prefixWord ++ tailWord_6312978) baseStart_6312978 baseEnd_6312978 := by
    simpa [prefixWord, tailWord_6312978, baseEnd_6312978] using wordTrace_append hprefix tailTrace_6312978
  have hstable : (prefixWord ++ tailWord_6312978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312978).length < 2 ^ (prefixWord ++ tailWord_6312978).sum := by decide
  have hdescent : baseEnd_6312978 < baseStart_6312978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6312994 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_6312994 : Nat := 118140960795 + 6312994 * 2 ^ 59
def prefixEnd_6312994 : Nat := 4983230072969 + 3 ^ 40 * 6312994 * 2
def baseEnd_6312994 : Nat := 3241600290949978615642075

theorem tailTrace_6312994 : CollatzResearch.WordTrace tailWord_6312994 prefixEnd_6312994 3241600290949978615642075 := by
  unfold tailWord_6312994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57563451822777096595632509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153502538194072257588353357 57563451822777096595632509)
  ·
    refine ⟨21586294433541411223362191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57563451822777096595632509 21586294433541411223362191)
    ·
      refine ⟨32379441650312116835043287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21586294433541411223362191 32379441650312116835043287)
      ·
        refine ⟨48569162475468175252564931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32379441650312116835043287 48569162475468175252564931)
        ·
          refine ⟨72853743713202262878847397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48569162475468175252564931 72853743713202262878847397)
          ·
            refine ⟨13660076946225424289783887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72853743713202262878847397 13660076946225424289783887)
            ·
              refine ⟨20490115419338136434675831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13660076946225424289783887 20490115419338136434675831)
              ·
                refine ⟨30735173129007204652013747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20490115419338136434675831 30735173129007204652013747)
                ·
                  refine ⟨46102759693510806978020621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30735173129007204652013747 46102759693510806978020621)
                  ·
                    refine ⟨17288534885066552616757733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46102759693510806978020621 17288534885066552616757733)
                    ·
                      refine ⟨3241600290949978615642075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17288534885066552616757733 3241600290949978615642075)
                      ·
                        rfl

theorem cell23_6312994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_6312994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6312994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6312994 prefixEnd_6312994 := by exact prefixLift 6312994
  have htrace : WordTrace (prefixWord ++ tailWord_6312994) baseStart_6312994 baseEnd_6312994 := by
    simpa [prefixWord, tailWord_6312994, baseEnd_6312994] using wordTrace_append hprefix tailTrace_6312994
  have hstable : (prefixWord ++ tailWord_6312994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6312994).length < 2 ^ (prefixWord ++ tailWord_6312994).sum := by decide
  have hdescent : baseEnd_6312994 < baseStart_6312994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6312994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313021 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_6313021 : Nat := 118140960795 + 6313021 * 2 ^ 59
def prefixEnd_6313021 : Nat := 4983230072969 + 3 ^ 40 * 6313021 * 2
def baseEnd_6313021 : Nat := 1080538051642550003334817

theorem tailTrace_6313021 : CollatzResearch.WordTrace tailWord_6313021 prefixEnd_6313021 1080538051642550003334817 := by
  unfold tailWord_6313021
  simp only [CollatzResearch.WordTrace]
  refine ⟨230254792062010569993762917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153503194708007046662508611 230254792062010569993762917)
  ·
    refine ⟨43172773511626981873830547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230254792062010569993762917 43172773511626981873830547)
    ·
      refine ⟨64759160267440472810745821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43172773511626981873830547 64759160267440472810745821)
      ·
        refine ⟨24284685100290177304029683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64759160267440472810745821 24284685100290177304029683)
        ·
          refine ⟨36427027650435265956044525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24284685100290177304029683 36427027650435265956044525)
          ·
            refine ⟨13660135368913224733516697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36427027650435265956044525 13660135368913224733516697)
            ·
              refine ⟨10245101526684918550137523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13660135368913224733516697 10245101526684918550137523)
              ·
                refine ⟨15367652290027377825206285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10245101526684918550137523 15367652290027377825206285)
                ·
                  refine ⟨5762869608760266684452357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15367652290027377825206285 5762869608760266684452357)
                  ·
                    refine ⟨1080538051642550003334817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762869608760266684452357 1080538051642550003334817)
                    ·
                      rfl

theorem cell23_6313021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_6313021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313021 prefixEnd_6313021 := by exact prefixLift 6313021
  have htrace : WordTrace (prefixWord ++ tailWord_6313021) baseStart_6313021 baseEnd_6313021 := by
    simpa [prefixWord, tailWord_6313021, baseEnd_6313021] using wordTrace_append hprefix tailTrace_6313021
  have hstable : (prefixWord ++ tailWord_6313021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313021).length < 2 ^ (prefixWord ++ tailWord_6313021).sum := by decide
  have hdescent : baseEnd_6313021 < baseStart_6313021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313071 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 2, 3, 2]
def baseStart_6313071 : Nat := 118140960795 + 6313071 * 2 ^ 59
def prefixEnd_6313071 : Nat := 4983230072969 + 3 ^ 40 * 6313071 * 2
def baseEnd_6313071 : Nat := 3241639828960374814379221

theorem tailTrace_6313071 : CollatzResearch.WordTrace tailWord_6313071 prefixEnd_6313071 3241639828960374814379221 := by
  unfold tailWord_6313071
  simp only [CollatzResearch.WordTrace]
  refine ⟨230256615711829428533083067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153504410474552952355388711 230256615711829428533083067)
  ·
    refine ⟨345384923567744142799624601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230256615711829428533083067 345384923567744142799624601)
    ·
      refine ⟨259038692675808107099718451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345384923567744142799624601 259038692675808107099718451)
      ·
        refine ⟨388558039013712160649577677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259038692675808107099718451 388558039013712160649577677)
        ·
          refine ⟨145709264630142060243591629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388558039013712160649577677 145709264630142060243591629)
          ·
            refine ⟨54640974236303272591346861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145709264630142060243591629 54640974236303272591346861)
            ·
              refine ⟨20490365338613727221755073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54640974236303272591346861 20490365338613727221755073)
              ·
                refine ⟨15367774003960295416316305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20490365338613727221755073 15367774003960295416316305)
                ·
                  refine ⟨11525830502970221562237229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15367774003960295416316305 11525830502970221562237229)
                  ·
                    refine ⟨4322186438613833085838961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11525830502970221562237229 4322186438613833085838961)
                    ·
                      refine ⟨3241639828960374814379221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322186438613833085838961 3241639828960374814379221)
                      ·
                        rfl

theorem cell23_6313071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3, 2].length) (baseStart_6313071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313071 prefixEnd_6313071 := by exact prefixLift 6313071
  have htrace : WordTrace (prefixWord ++ tailWord_6313071) baseStart_6313071 baseEnd_6313071 := by
    simpa [prefixWord, tailWord_6313071, baseEnd_6313071] using wordTrace_append hprefix tailTrace_6313071
  have hstable : (prefixWord ++ tailWord_6313071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313071).length < 2 ^ (prefixWord ++ tailWord_6313071).sum := by decide
  have hdescent : baseEnd_6313071 < baseStart_6313071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313084 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6313084 : Nat := 118140960795 + 6313084 * 2 ^ 59
def prefixEnd_6313084 : Nat := 4983230072969 + 3 ^ 40 * 6313084 * 2
def baseEnd_6313084 : Nat := 3241646504208883263516661

theorem tailTrace_6313084 : CollatzResearch.WordTrace tailWord_6313084 prefixEnd_6313084 3241646504208883263516661 := by
  unfold tailWord_6313084
  simp only [CollatzResearch.WordTrace]
  refine ⟨115128544930391165876653153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153504726573854887835537537 115128544930391165876653153)
  ·
    refine ⟨86346408697793374407489865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115128544930391165876653153 86346408697793374407489865)
    ·
      refine ⟨64759806523345030805617399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86346408697793374407489865 64759806523345030805617399)
      ·
        refine ⟨97139709785017546208426099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64759806523345030805617399 97139709785017546208426099)
        ·
          refine ⟨145709564677526319312639149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97139709785017546208426099 145709564677526319312639149)
          ·
            refine ⟨54641086754072369742239681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145709564677526319312639149 54641086754072369742239681)
            ·
              refine ⟨40980815065554277306679761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54641086754072369742239681 40980815065554277306679761)
              ·
                refine ⟨30735611299165707980009821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40980815065554277306679761 30735611299165707980009821)
                ·
                  refine ⟨11525854237187140492503683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30735611299165707980009821 11525854237187140492503683)
                  ·
                    refine ⟨17288781355780710738755525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11525854237187140492503683 17288781355780710738755525)
                    ·
                      refine ⟨3241646504208883263516661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17288781355780710738755525 3241646504208883263516661)
                      ·
                        rfl

theorem cell23_6313084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6313084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313084 prefixEnd_6313084 := by exact prefixLift 6313084
  have htrace : WordTrace (prefixWord ++ tailWord_6313084) baseStart_6313084 baseEnd_6313084 := by
    simpa [prefixWord, tailWord_6313084, baseEnd_6313084] using wordTrace_append hprefix tailTrace_6313084
  have hstable : (prefixWord ++ tailWord_6313084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313084).length < 2 ^ (prefixWord ++ tailWord_6313084).sum := by decide
  have hdescent : baseEnd_6313084 < baseStart_6313084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313107 : List Nat := [1, 1, 1, 2, 1, 2, 6, 9]
def baseStart_6313107 : Nat := 118140960795 + 6313107 * 2 ^ 59
def prefixEnd_6313107 : Nat := 4983230072969 + 3 ^ 40 * 6313107 * 2
def baseEnd_6313107 : Nat := 120061419046812469389965

theorem tailTrace_6313107 : CollatzResearch.WordTrace tailWord_6313107 prefixEnd_6313107 120061419046812469389965 := by
  unfold tailWord_6313107
  simp only [CollatzResearch.WordTrace]
  refine ⟨230257928739699006681393575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153505285826466004454262383 230257928739699006681393575)
  ·
    refine ⟨345386893109548510022090363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230257928739699006681393575 345386893109548510022090363)
    ·
      refine ⟨518080339664322765033135545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345386893109548510022090363 518080339664322765033135545)
      ·
        refine ⟨388560254748242073774851659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518080339664322765033135545 388560254748242073774851659)
        ·
          refine ⟨582840382122363110662277489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388560254748242073774851659 582840382122363110662277489)
          ·
            refine ⟨437130286591772332996708117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582840382122363110662277489 437130286591772332996708117)
            ·
              refine ⟨20490482183989328109220693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 437130286591772332996708117 20490482183989328109220693)
              ·
                refine ⟨120061419046812469389965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20490482183989328109220693 120061419046812469389965)
                ·
                  rfl

theorem cell23_6313107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 9].length) (baseStart_6313107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313107 prefixEnd_6313107 := by exact prefixLift 6313107
  have htrace : WordTrace (prefixWord ++ tailWord_6313107) baseStart_6313107 baseEnd_6313107 := by
    simpa [prefixWord, tailWord_6313107, baseEnd_6313107] using wordTrace_append hprefix tailTrace_6313107
  have hstable : (prefixWord ++ tailWord_6313107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313107).length < 2 ^ (prefixWord ++ tailWord_6313107).sum := by decide
  have hdescent : baseEnd_6313107 < baseStart_6313107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313184 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_6313184 : Nat := 118140960795 + 6313184 * 2 ^ 59
def prefixEnd_6313184 : Nat := 4983230072969 + 3 ^ 40 * 6313184 * 2
def baseEnd_6313184 : Nat := 1080565950758110957422067

theorem tailTrace_6313184 : CollatzResearch.WordTrace tailWord_6313184 prefixEnd_6313184 1080565950758110957422067 := by
  unfold tailWord_6313184
  simp only [CollatzResearch.WordTrace]
  refine ⟨115130368580210024415973303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153507158106946699221297737 115130368580210024415973303)
  ·
    refine ⟨172695552870315036623959955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115130368580210024415973303 172695552870315036623959955)
    ·
      refine ⟨259043329305472554935939933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172695552870315036623959955 259043329305472554935939933)
      ·
        refine ⟨97141248489552208100977475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259043329305472554935939933 97141248489552208100977475)
        ·
          refine ⟨145711872734328312151466213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97141248489552208100977475 145711872734328312151466213)
          ·
            refine ⟨27320976137686558528399915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145711872734328312151466213 27320976137686558528399915)
            ·
              refine ⟨40981464206529837792599873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27320976137686558528399915 40981464206529837792599873)
              ·
                refine ⟨30736098154897378344449905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40981464206529837792599873 30736098154897378344449905)
                ·
                  refine ⟨23052073616173033758337429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30736098154897378344449905 23052073616173033758337429)
                  ·
                    refine ⟨1080565950758110957422067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23052073616173033758337429 1080565950758110957422067)
                    ·
                      rfl

theorem cell23_6313184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_6313184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313184 prefixEnd_6313184 := by exact prefixLift 6313184
  have htrace : WordTrace (prefixWord ++ tailWord_6313184) baseStart_6313184 baseEnd_6313184 := by
    simpa [prefixWord, tailWord_6313184, baseEnd_6313184] using wordTrace_append hprefix tailTrace_6313184
  have hstable : (prefixWord ++ tailWord_6313184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313184).length < 2 ^ (prefixWord ++ tailWord_6313184).sum := by decide
  have hdescent : baseEnd_6313184 < baseStart_6313184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313185 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_6313185 : Nat := 118140960795 + 6313185 * 2 ^ 59
def prefixEnd_6313185 : Nat := 4983230072969 + 3 ^ 40 * 6313185 * 2
def baseEnd_6313185 : Nat := 3241698365754987368353697

theorem tailTrace_6313185 : CollatzResearch.WordTrace tailWord_6313185 prefixEnd_6313185 3241698365754987368353697 := by
  unfold tailWord_6313185
  simp only [CollatzResearch.WordTrace]
  refine ⟨230260773633416426002733009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153507182422277617335155339 230260773633416426002733009)
  ·
    refine ⟨172695580225062319502049757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230260773633416426002733009 172695580225062319502049757)
    ·
      refine ⟨64760842584398369813268659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172695580225062319502049757 64760842584398369813268659)
      ·
        refine ⟨97141263876597554719902989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64760842584398369813268659 97141263876597554719902989)
        ·
          refine ⟨36427973953724083019963621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97141263876597554719902989 36427973953724083019963621)
          ·
            refine ⟨6830245116323265566243179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36427973953724083019963621 6830245116323265566243179)
            ·
              refine ⟨10245367674484898349364769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830245116323265566243179 10245367674484898349364769)
              ·
                refine ⟨7684025755863673762023577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10245367674484898349364769 7684025755863673762023577)
                ·
                  refine ⟨5763019316897755321517683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7684025755863673762023577 5763019316897755321517683)
                  ·
                    refine ⟨8644528975346632982276525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763019316897755321517683 8644528975346632982276525)
                    ·
                      refine ⟨3241698365754987368353697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644528975346632982276525 3241698365754987368353697)
                      ·
                        rfl

theorem cell23_6313185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_6313185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313185 prefixEnd_6313185 := by exact prefixLift 6313185
  have htrace : WordTrace (prefixWord ++ tailWord_6313185) baseStart_6313185 baseEnd_6313185 := by
    simpa [prefixWord, tailWord_6313185, baseEnd_6313185] using wordTrace_append hprefix tailTrace_6313185
  have hstable : (prefixWord ++ tailWord_6313185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313185).length < 2 ^ (prefixWord ++ tailWord_6313185).sum := by decide
  have hdescent : baseEnd_6313185 < baseStart_6313185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313202 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6313202 : Nat := 118140960795 + 6313202 * 2 ^ 59
def prefixEnd_6313202 : Nat := 4983230072969 + 3 ^ 40 * 6313202 * 2
def baseEnd_6313202 : Nat := 3241707094926113801841119

theorem tailTrace_6313202 : CollatzResearch.WordTrace tailWord_6313202 prefixEnd_6313202 3241707094926113801841119 := by
  unfold tailWord_6313202
  simp only [CollatzResearch.WordTrace]
  refine ⟨57565348418588709476525465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153507595782903225270734573 57565348418588709476525465)
  ·
    refine ⟨43174011313941532107394099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57565348418588709476525465 43174011313941532107394099)
    ·
      refine ⟨64761016970912298161091149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43174011313941532107394099 64761016970912298161091149)
      ·
        refine ⟨24285381364092111810409181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64761016970912298161091149 24285381364092111810409181)
        ·
          refine ⟨9107018011534541928903443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24285381364092111810409181 9107018011534541928903443)
          ·
            refine ⟨13660527017301812893355165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107018011534541928903443 13660527017301812893355165)
            ·
              refine ⟨5122697631488179835008187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13660527017301812893355165 5122697631488179835008187)
              ·
                refine ⟨7684046447232269752512281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122697631488179835008187 7684046447232269752512281)
                ·
                  refine ⟨5763034835424202314384211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7684046447232269752512281 5763034835424202314384211)
                  ·
                    refine ⟨8644552253136303471576317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763034835424202314384211 8644552253136303471576317)
                    ·
                      refine ⟨3241707094926113801841119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644552253136303471576317 3241707094926113801841119)
                      ·
                        rfl

theorem cell23_6313202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6313202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313202 prefixEnd_6313202 := by exact prefixLift 6313202
  have htrace : WordTrace (prefixWord ++ tailWord_6313202) baseStart_6313202 baseEnd_6313202 := by
    simpa [prefixWord, tailWord_6313202, baseEnd_6313202] using wordTrace_append hprefix tailTrace_6313202
  have hstable : (prefixWord ++ tailWord_6313202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313202).length < 2 ^ (prefixWord ++ tailWord_6313202).sum := by decide
  have hdescent : baseEnd_6313202 < baseStart_6313202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313248 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 7]
def baseStart_6313248 : Nat := 118140960795 + 6313248 * 2 ^ 59
def prefixEnd_6313248 : Nat := 4983230072969 + 3 ^ 40 * 6313248 * 2
def baseEnd_6313248 : Nat := 360192301670691180207323

theorem tailTrace_6313248 : CollatzResearch.WordTrace tailWord_6313248 prefixEnd_6313248 360192301670691180207323 := by
  unfold tailWord_6313248
  simp only [CollatzResearch.WordTrace]
  refine ⟨115131535716094093881138199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153508714288125458508184265 115131535716094093881138199)
  ·
    refine ⟨172697303574141140821707299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115131535716094093881138199 172697303574141140821707299)
    ·
      refine ⟨259045955361211711232560949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172697303574141140821707299 259045955361211711232560949)
      ·
        refine ⟨24285558315113597928052589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259045955361211711232560949 24285558315113597928052589)
        ·
          refine ⟨9107084368167599223019721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24285558315113597928052589 9107084368167599223019721)
          ·
            refine ⟨6830313276125699417264791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9107084368167599223019721 6830313276125699417264791)
            ·
              refine ⟨10245469914188549125897187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830313276125699417264791 10245469914188549125897187)
              ·
                refine ⟨15368204871282823688845781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10245469914188549125897187 15368204871282823688845781)
                ·
                  refine ⟨360192301670691180207323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15368204871282823688845781 360192301670691180207323)
                  ·
                    rfl

theorem cell23_6313248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_6313248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313248 prefixEnd_6313248 := by exact prefixLift 6313248
  have htrace : WordTrace (prefixWord ++ tailWord_6313248) baseStart_6313248 baseEnd_6313248 := by
    simpa [prefixWord, tailWord_6313248, baseEnd_6313248] using wordTrace_append hprefix tailTrace_6313248
  have hstable : (prefixWord ++ tailWord_6313248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313248).length < 2 ^ (prefixWord ++ tailWord_6313248).sum := by decide
  have hdescent : baseEnd_6313248 < baseStart_6313248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313278 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_6313278 : Nat := 118140960795 + 6313278 * 2 ^ 59
def prefixEnd_6313278 : Nat := 4983230072969 + 3 ^ 40 * 6313278 * 2
def baseEnd_6313278 : Nat := 1080582039818618501496923

theorem tailTrace_6313278 : CollatzResearch.WordTrace tailWord_6313278 prefixEnd_6313278 1080582039818618501496923 := by
  unfold tailWord_6313278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28783020702759937860733561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153509443748053001923912325 28783020702759937860733561)
  ·
    refine ⟨21587265527069953395550171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28783020702759937860733561 21587265527069953395550171)
    ·
      refine ⟨32380898290604930093325257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21587265527069953395550171 32380898290604930093325257)
      ·
        refine ⟨24285673717953697569993943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32380898290604930093325257 24285673717953697569993943)
        ·
          refine ⟨36428510576930546354990915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24285673717953697569993943 36428510576930546354990915)
          ·
            refine ⟨54642765865395819532486373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36428510576930546354990915 54642765865395819532486373)
            ·
              refine ⟨10245518599761716162341195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54642765865395819532486373 10245518599761716162341195)
              ·
                refine ⟨15368277899642574243511793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10245518599761716162341195 15368277899642574243511793)
                ·
                  refine ⟨11526208424731930682633845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15368277899642574243511793 11526208424731930682633845)
                  ·
                    refine ⟨1080582039818618501496923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11526208424731930682633845 1080582039818618501496923)
                    ·
                      rfl

theorem cell23_6313278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_6313278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313278 prefixEnd_6313278 := by exact prefixLift 6313278
  have htrace : WordTrace (prefixWord ++ tailWord_6313278) baseStart_6313278 baseEnd_6313278 := by
    simpa [prefixWord, tailWord_6313278, baseEnd_6313278] using wordTrace_append hprefix tailTrace_6313278
  have hstable : (prefixWord ++ tailWord_6313278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313278).length < 2 ^ (prefixWord ++ tailWord_6313278).sum := by decide
  have hdescent : baseEnd_6313278 < baseStart_6313278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313298 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_6313298 : Nat := 118140960795 + 6313298 * 2 ^ 59
def prefixEnd_6313298 : Nat := 4983230072969 + 3 ^ 40 * 6313298 * 2
def baseEnd_6313298 : Nat := 3241756389068945426240677

theorem tailTrace_6313298 : CollatzResearch.WordTrace tailWord_6313298 prefixEnd_6313298 3241756389068945426240677 := by
  unfold tailWord_6313298
  simp only [CollatzResearch.WordTrace]
  refine ⟨57566223770501761575399137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153509930054671364201064365 57566223770501761575399137)
  ·
    refine ⟨43174667827876321181549353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57566223770501761575399137 43174667827876321181549353)
    ·
      refine ⟨32381000870907240886162015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43174667827876321181549353 32381000870907240886162015)
      ·
        refine ⟨48571501306360861329243023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32381000870907240886162015 48571501306360861329243023)
        ·
          refine ⟨72857251959541291993864535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48571501306360861329243023 72857251959541291993864535)
          ·
            refine ⟨109285877939311937990796803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72857251959541291993864535 109285877939311937990796803)
            ·
              refine ⟨163928816908967906986195205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109285877939311937990796803 163928816908967906986195205)
              ·
                refine ⟨30736653170431482559911601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163928816908967906986195205 30736653170431482559911601)
                ·
                  refine ⟨23052489877823611919933701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30736653170431482559911601 23052489877823611919933701)
                  ·
                    refine ⟨4322341852091927234987569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23052489877823611919933701 4322341852091927234987569)
                    ·
                      refine ⟨3241756389068945426240677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322341852091927234987569 3241756389068945426240677)
                      ·
                        rfl

theorem cell23_6313298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_6313298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313298 prefixEnd_6313298 := by exact prefixLift 6313298
  have htrace : WordTrace (prefixWord ++ tailWord_6313298) baseStart_6313298 baseEnd_6313298 := by
    simpa [prefixWord, tailWord_6313298, baseEnd_6313298] using wordTrace_append hprefix tailTrace_6313298
  have hstable : (prefixWord ++ tailWord_6313298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313298).length < 2 ^ (prefixWord ++ tailWord_6313298).sum := by decide
  have hdescent : baseEnd_6313298 < baseStart_6313298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313372 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 6]
def baseStart_6313372 : Nat := 118140960795 + 6313372 * 2 ^ 59
def prefixEnd_6313372 : Nat := 4983230072969 + 3 ^ 40 * 6313372 * 2
def baseEnd_6313372 : Nat := 360199376293042015190593

theorem tailTrace_6313372 : CollatzResearch.WordTrace tailWord_6313372 prefixEnd_6313372 360199376293042015190593 := by
  unfold tailWord_6313372
  simp only [CollatzResearch.WordTrace]
  refine ⟨115133797041869478469895185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153511729389159304626526913 115133797041869478469895185)
  ·
    refine ⟨86350347781402108852421389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115133797041869478469895185 86350347781402108852421389)
    ·
      refine ⟨32381380418025790819658021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86350347781402108852421389 32381380418025790819658021)
      ·
        refine ⟨6071508828379835778685879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32381380418025790819658021 6071508828379835778685879)
        ·
          refine ⟨9107263242569753668028819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071508828379835778685879 9107263242569753668028819)
          ·
            refine ⟨13660894863854630502043229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107263242569753668028819 13660894863854630502043229)
            ·
              refine ⟨5122835573945486438266211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13660894863854630502043229 5122835573945486438266211)
              ·
                refine ⟨7684253360918229657399317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122835573945486438266211 7684253360918229657399317)
                ·
                  refine ⟨360199376293042015190593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7684253360918229657399317 360199376293042015190593)
                  ·
                    rfl

theorem cell23_6313372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_6313372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313372 prefixEnd_6313372 := by exact prefixLift 6313372
  have htrace : WordTrace (prefixWord ++ tailWord_6313372) baseStart_6313372 baseEnd_6313372 := by
    simpa [prefixWord, tailWord_6313372, baseEnd_6313372] using wordTrace_append hprefix tailTrace_6313372
  have hstable : (prefixWord ++ tailWord_6313372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313372).length < 2 ^ (prefixWord ++ tailWord_6313372).sum := by decide
  have hdescent : baseEnd_6313372 < baseStart_6313372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313381 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_6313381 : Nat := 118140960795 + 6313381 * 2 ^ 59
def prefixEnd_6313381 : Nat := 4983230072969 + 3 ^ 40 * 6313381 * 2
def baseEnd_6313381 : Nat := 1080599669321089533834265

theorem tailTrace_6313381 : CollatzResearch.WordTrace tailWord_6313381 prefixEnd_6313381 1080599669321089533834265 := by
  unfold tailWord_6313381
  simp only [CollatzResearch.WordTrace]
  refine ⟨230267922340706351476867997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153511948227137567651245331 230267922340706351476867997)
  ·
    refine ⟨86350470877764881803825499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230267922340706351476867997 86350470877764881803825499)
    ·
      refine ⟨129525706316647322705738249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86350470877764881803825499 129525706316647322705738249)
      ·
        refine ⟨97144279737485492029303687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129525706316647322705738249 97144279737485492029303687)
        ·
          refine ⟨145716419606228238043955531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97144279737485492029303687 145716419606228238043955531)
          ·
            refine ⟨218574629409342357065933297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145716419606228238043955531 218574629409342357065933297)
            ·
              refine ⟨163930972057006767799449973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218574629409342357065933297 163930972057006767799449973)
              ·
                refine ⟨15368528630344384481198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163930972057006767799449973 15368528630344384481198435)
                ·
                  refine ⟨23052792945516576721797653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15368528630344384481198435 23052792945516576721797653)
                  ·
                    refine ⟨1080599669321089533834265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23052792945516576721797653 1080599669321089533834265)
                    ·
                      rfl

theorem cell23_6313381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_6313381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313381 prefixEnd_6313381 := by exact prefixLift 6313381
  have htrace : WordTrace (prefixWord ++ tailWord_6313381) baseStart_6313381 baseEnd_6313381 := by
    simpa [prefixWord, tailWord_6313381, baseEnd_6313381] using wordTrace_append hprefix tailTrace_6313381
  have hstable : (prefixWord ++ tailWord_6313381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313381).length < 2 ^ (prefixWord ++ tailWord_6313381).sum := by decide
  have hdescent : baseEnd_6313381 < baseStart_6313381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313388 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_6313388 : Nat := 118140960795 + 6313388 * 2 ^ 59
def prefixEnd_6313388 : Nat := 4983230072969 + 3 ^ 40 * 6313388 * 2
def baseEnd_6313388 : Nat := 3241802602327850074115263

theorem tailTrace_6313388 : CollatzResearch.WordTrace tailWord_6313388 prefixEnd_6313388 3241802602327850074115263 := by
  unfold tailWord_6313388
  simp only [CollatzResearch.WordTrace]
  refine ⟨115134088825840495836186409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153512118434453994448248545 115134088825840495836186409)
  ·
    refine ⟨86350566619380371877139807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115134088825840495836186409 86350566619380371877139807)
    ·
      refine ⟨129525849929070557815709711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86350566619380371877139807 129525849929070557815709711)
      ·
        refine ⟨194288774893605836723564567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129525849929070557815709711 194288774893605836723564567)
        ·
          refine ⟨291433162340408755085346851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194288774893605836723564567 291433162340408755085346851)
          ·
            refine ⟨437149743510613132628020277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291433162340408755085346851 437149743510613132628020277)
            ·
              refine ⟨40982788454119981183876901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437149743510613132628020277 40982788454119981183876901)
              ·
                refine ⟨7684272835147496471976919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40982788454119981183876901 7684272835147496471976919)
                ·
                  refine ⟨11526409252721244707965379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684272835147496471976919 11526409252721244707965379)
                  ·
                    refine ⟨17289613879081867061948069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11526409252721244707965379 17289613879081867061948069)
                    ·
                      refine ⟨3241802602327850074115263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17289613879081867061948069 3241802602327850074115263)
                      ·
                        rfl

theorem cell23_6313388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_6313388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313388 prefixEnd_6313388 := by exact prefixLift 6313388
  have htrace : WordTrace (prefixWord ++ tailWord_6313388) baseStart_6313388 baseEnd_6313388 := by
    simpa [prefixWord, tailWord_6313388, baseEnd_6313388] using wordTrace_append hprefix tailTrace_6313388
  have hstable : (prefixWord ++ tailWord_6313388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313388).length < 2 ^ (prefixWord ++ tailWord_6313388).sum := by decide
  have hdescent : baseEnd_6313388 < baseStart_6313388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313391 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_6313391 : Nat := 118140960795 + 6313391 * 2 ^ 59
def prefixEnd_6313391 : Nat := 4983230072969 + 3 ^ 40 * 6313391 * 2
def baseEnd_6313391 : Nat := 3241804142769813562377749

theorem tailTrace_6313391 : CollatzResearch.WordTrace tailWord_6313391 prefixEnd_6313391 3241804142769813562377749 := by
  unfold tailWord_6313391
  simp only [CollatzResearch.WordTrace]
  refine ⟨230268287070670123184732027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153512191380446748789821351 230268287070670123184732027)
  ·
    refine ⟨345402430606005184777098041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230268287070670123184732027 345402430606005184777098041)
    ·
      refine ⟨259051822954503888582823531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345402430606005184777098041 259051822954503888582823531)
      ·
        refine ⟨388577734431755832874235297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259051822954503888582823531 388577734431755832874235297)
        ·
          refine ⟨291433300823816874655676473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388577734431755832874235297 291433300823816874655676473)
          ·
            refine ⟨218574975617862655991757355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291433300823816874655676473 218574975617862655991757355)
            ·
              refine ⟨327862463426793983987636033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218574975617862655991757355 327862463426793983987636033)
              ·
                refine ⟨245896847570095487990727025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327862463426793983987636033 245896847570095487990727025)
                ·
                  refine ⟨184422635677571615993045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245896847570095487990727025 184422635677571615993045269)
                  ·
                    refine ⟨8644811047386169499673997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184422635677571615993045269 8644811047386169499673997)
                    ·
                      refine ⟨3241804142769813562377749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644811047386169499673997 3241804142769813562377749)
                      ·
                        rfl

theorem cell23_6313391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_6313391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313391 prefixEnd_6313391 := by exact prefixLift 6313391
  have htrace : WordTrace (prefixWord ++ tailWord_6313391) baseStart_6313391 baseEnd_6313391 := by
    simpa [prefixWord, tailWord_6313391, baseEnd_6313391] using wordTrace_append hprefix tailTrace_6313391
  have hstable : (prefixWord ++ tailWord_6313391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313391).length < 2 ^ (prefixWord ++ tailWord_6313391).sum := by decide
  have hdescent : baseEnd_6313391 < baseStart_6313391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313410 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6313410 : Nat := 118140960795 + 6313410 * 2 ^ 59
def prefixEnd_6313410 : Nat := 4983230072969 + 3 ^ 40 * 6313410 * 2
def baseEnd_6313410 : Nat := 1080604632967416329346721

theorem tailTrace_6313410 : CollatzResearch.WordTrace tailWord_6313410 prefixEnd_6313410 1080604632967416329346721 := by
  unfold tailWord_6313410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567245014400322357418421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153512653371734192953115789 57567245014400322357418421)
  ·
    refine ⟨5396929220100030221007977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57567245014400322357418421 5396929220100030221007977)
    ·
      refine ⟨4047696915075022665755983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5396929220100030221007977 4047696915075022665755983)
      ·
        refine ⟨6071545372612533998633975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047696915075022665755983 6071545372612533998633975)
        ·
          refine ⟨9107318058918800997950963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071545372612533998633975 9107318058918800997950963)
          ·
            refine ⟨13660977088378201496926445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107318058918800997950963 13660977088378201496926445)
            ·
              refine ⟨5122866408141825561347417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13660977088378201496926445 5122866408141825561347417)
              ·
                refine ⟨3842149806106369171010563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122866408141825561347417 3842149806106369171010563)
                ·
                  refine ⟨5763224709159553756515845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842149806106369171010563 5763224709159553756515845)
                  ·
                    refine ⟨1080604632967416329346721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763224709159553756515845 1080604632967416329346721)
                    ·
                      rfl

theorem cell23_6313410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6313410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313410 prefixEnd_6313410 := by exact prefixLift 6313410
  have htrace : WordTrace (prefixWord ++ tailWord_6313410) baseStart_6313410 baseEnd_6313410 := by
    simpa [prefixWord, tailWord_6313410, baseEnd_6313410] using wordTrace_append hprefix tailTrace_6313410
  have hstable : (prefixWord ++ tailWord_6313410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313410).length < 2 ^ (prefixWord ++ tailWord_6313410).sum := by decide
  have hdescent : baseEnd_6313410 < baseStart_6313410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313422 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_6313422 : Nat := 118140960795 + 6313422 * 2 ^ 59
def prefixEnd_6313422 : Nat := 4983230072969 + 3 ^ 40 * 6313422 * 2
def baseEnd_6313422 : Nat := 3241820060670102941090107

theorem tailTrace_6313422 : CollatzResearch.WordTrace tailWord_6313422 prefixEnd_6313422 3241820060670102941090107 := by
  unfold tailWord_6313422
  simp only [CollatzResearch.WordTrace]
  refine ⟨28783677216694726934888815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153512945155705210319407013 28783677216694726934888815)
  ·
    refine ⟨43175515825042090402333223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28783677216694726934888815 43175515825042090402333223)
    ·
      refine ⟨64763273737563135603499835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43175515825042090402333223 64763273737563135603499835)
      ·
        refine ⟨97144910606344703405249753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64763273737563135603499835 97144910606344703405249753)
        ·
          refine ⟨72858682954758527553937315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97144910606344703405249753 72858682954758527553937315)
          ·
            refine ⟨109288024432137791330905973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72858682954758527553937315 109288024432137791330905973)
            ·
              refine ⟨10245752290512917937272435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109288024432137791330905973 10245752290512917937272435)
              ·
                refine ⟨15368628435769376905908653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10245752290512917937272435 15368628435769376905908653)
                ·
                  refine ⟨5763235663413516339715745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15368628435769376905908653 5763235663413516339715745)
                  ·
                    refine ⟨4322426747560137254786809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763235663413516339715745 4322426747560137254786809)
                    ·
                      refine ⟨3241820060670102941090107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322426747560137254786809 3241820060670102941090107)
                      ·
                        rfl

theorem cell23_6313422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_6313422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313422 prefixEnd_6313422 := by exact prefixLift 6313422
  have htrace : WordTrace (prefixWord ++ tailWord_6313422) baseStart_6313422 baseEnd_6313422 := by
    simpa [prefixWord, tailWord_6313422, baseEnd_6313422] using wordTrace_append hprefix tailTrace_6313422
  have hstable : (prefixWord ++ tailWord_6313422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313422).length < 2 ^ (prefixWord ++ tailWord_6313422).sum := by decide
  have hdescent : baseEnd_6313422 < baseStart_6313422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313451 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_6313451 : Nat := 118140960795 + 6313451 * 2 ^ 59
def prefixEnd_6313451 : Nat := 4983230072969 + 3 ^ 40 * 6313451 * 2
def baseEnd_6313451 : Nat := 3241834951609083327627473

theorem tailTrace_6313451 : CollatzResearch.WordTrace tailWord_6313451 prefixEnd_6313451 3241834951609083327627473 := by
  unfold tailWord_6313451
  simp only [CollatzResearch.WordTrace]
  refine ⟨230270475450452753431916207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153513650300301835621277471 230270475450452753431916207)
  ·
    refine ⟨345405713175679130147874311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230270475450452753431916207 345405713175679130147874311)
    ·
      refine ⟨518108569763518695221811467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345405713175679130147874311 518108569763518695221811467)
      ·
        refine ⟨777162854645278042832717201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518108569763518695221811467 777162854645278042832717201)
        ·
          refine ⟨582872140983958532124537901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777162854645278042832717201 582872140983958532124537901)
          ·
            refine ⟨218577052868984449546701713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 582872140983958532124537901 218577052868984449546701713)
            ·
              refine ⟨163932789651738337160026285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218577052868984449546701713 163932789651738337160026285)
              ·
                refine ⟨61474796119401876435009857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163932789651738337160026285 61474796119401876435009857)
                ·
                  refine ⟨46106097089551407326257393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61474796119401876435009857 46106097089551407326257393)
                  ·
                    refine ⟨34579572817163555494693045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46106097089551407326257393 34579572817163555494693045)
                    ·
                      refine ⟨3241834951609083327627473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34579572817163555494693045 3241834951609083327627473)
                      ·
                        rfl

theorem cell23_6313451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_6313451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313451 prefixEnd_6313451 := by exact prefixLift 6313451
  have htrace : WordTrace (prefixWord ++ tailWord_6313451) baseStart_6313451 baseEnd_6313451 := by
    simpa [prefixWord, tailWord_6313451, baseEnd_6313451] using wordTrace_append hprefix tailTrace_6313451
  have hstable : (prefixWord ++ tailWord_6313451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313451).length < 2 ^ (prefixWord ++ tailWord_6313451).sum := by decide
  have hdescent : baseEnd_6313451 < baseStart_6313451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313473 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6313473 : Nat := 118140960795 + 6313473 * 2 ^ 59
def prefixEnd_6313473 : Nat := 4983230072969 + 3 ^ 40 * 6313473 * 2
def baseEnd_6313473 : Nat := 3241846248183482241552373

theorem tailTrace_6313473 : CollatzResearch.WordTrace tailWord_6313473 prefixEnd_6313473 3241846248183482241552373 := by
  unfold tailWord_6313473
  simp only [CollatzResearch.WordTrace]
  refine ⟨230271277856373051189217073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153514185237582034126144715 230271277856373051189217073)
  ·
    refine ⟨172703458392279788391912805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230271277856373051189217073 172703458392279788391912805)
    ·
      refine ⟨32381898448552460323483651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172703458392279788391912805 32381898448552460323483651)
      ·
        refine ⟨48572847672828690485225477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32381898448552460323483651 48572847672828690485225477)
        ·
          refine ⟨9107408938655379465979777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48572847672828690485225477 9107408938655379465979777)
          ·
            refine ⟨6830556703991534599484833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9107408938655379465979777 6830556703991534599484833)
            ·
              refine ⟨5122917527993650949613625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830556703991534599484833 5122917527993650949613625)
              ·
                refine ⟨3842188145995238212210219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122917527993650949613625 3842188145995238212210219)
                ·
                  refine ⟨5763282218992857318315329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842188145995238212210219 5763282218992857318315329)
                  ·
                    refine ⟨4322461664244642988736497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763282218992857318315329 4322461664244642988736497)
                    ·
                      refine ⟨3241846248183482241552373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322461664244642988736497 3241846248183482241552373)
                      ·
                        rfl

theorem cell23_6313473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6313473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313473 prefixEnd_6313473 := by exact prefixLift 6313473
  have htrace : WordTrace (prefixWord ++ tailWord_6313473) baseStart_6313473 baseEnd_6313473 := by
    simpa [prefixWord, tailWord_6313473, baseEnd_6313473] using wordTrace_append hprefix tailTrace_6313473
  have hstable : (prefixWord ++ tailWord_6313473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313473).length < 2 ^ (prefixWord ++ tailWord_6313473).sum := by decide
  have hdescent : baseEnd_6313473 < baseStart_6313473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313498 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_6313498 : Nat := 118140960795 + 6313498 * 2 ^ 59
def prefixEnd_6313498 : Nat := 4983230072969 + 3 ^ 40 * 6313498 * 2
def baseEnd_6313498 : Nat := 3241859085199844643739757

theorem tailTrace_6313498 : CollatzResearch.WordTrace tailWord_6313498 prefixEnd_6313498 3241859085199844643739757 := by
  unfold tailWord_6313498
  simp only [CollatzResearch.WordTrace]
  refine ⟨57568047420320620114719287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153514793120854986972584765 57568047420320620114719287)
  ·
    refine ⟨86352071130480930172078931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57568047420320620114719287 86352071130480930172078931)
    ·
      refine ⟨129528106695721395258118397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86352071130480930172078931 129528106695721395258118397)
      ·
        refine ⟨48573040010895523221794399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129528106695721395258118397 48573040010895523221794399)
        ·
          refine ⟨72859560016343284832691599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48573040010895523221794399 72859560016343284832691599)
          ·
            refine ⟨109289340024514927249037399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72859560016343284832691599 109289340024514927249037399)
            ·
              refine ⟨163934010036772390873556099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109289340024514927249037399 163934010036772390873556099)
              ·
                refine ⟨245901015055158586310334149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163934010036772390873556099 245901015055158586310334149)
                ·
                  refine ⟨46106440322842234933187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245901015055158586310334149 46106440322842234933187653)
                  ·
                    refine ⟨8644957560532919049972685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46106440322842234933187653 8644957560532919049972685)
                    ·
                      refine ⟨3241859085199844643739757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8644957560532919049972685 3241859085199844643739757)
                      ·
                        rfl

theorem cell23_6313498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_6313498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313498 prefixEnd_6313498 := by exact prefixLift 6313498
  have htrace : WordTrace (prefixWord ++ tailWord_6313498) baseStart_6313498 baseEnd_6313498 := by
    simpa [prefixWord, tailWord_6313498, baseEnd_6313498] using wordTrace_append hprefix tailTrace_6313498
  have hstable : (prefixWord ++ tailWord_6313498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313498).length < 2 ^ (prefixWord ++ tailWord_6313498).sum := by decide
  have hdescent : baseEnd_6313498 < baseStart_6313498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313529 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6313529 : Nat := 118140960795 + 6313529 * 2 ^ 59
def prefixEnd_6313529 : Nat := 4983230072969 + 3 ^ 40 * 6313529 * 2
def baseEnd_6313529 : Nat := 3241875003100134022452115

theorem tailTrace_6313529 : CollatzResearch.WordTrace tailWord_6313529 prefixEnd_6313529 3241875003100134022452115 := by
  unfold tailWord_6313529
  simp only [CollatzResearch.WordTrace]
  refine ⟨230273320344170172753255641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153515546896113448502170427 230273320344170172753255641)
  ·
    refine ⟨172704990258127629564941731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230273320344170172753255641 172704990258127629564941731)
    ·
      refine ⟨259057485387191444347412597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172704990258127629564941731 259057485387191444347412597)
      ·
        refine ⟨24286639255049197907569931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259057485387191444347412597 24286639255049197907569931)
        ·
          refine ⟨36429958882573796861354897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24286639255049197907569931 36429958882573796861354897)
          ·
            refine ⟨27322469161930347646016173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36429958882573796861354897 27322469161930347646016173)
            ·
              refine ⟨10245925935723880367256065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27322469161930347646016173 10245925935723880367256065)
              ·
                refine ⟨7684444451792910275442049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10245925935723880367256065 7684444451792910275442049)
                ·
                  refine ⟨5763333338844682706581537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7684444451792910275442049 5763333338844682706581537)
                  ·
                    refine ⟨4322500004133512029936153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763333338844682706581537 4322500004133512029936153)
                    ·
                      refine ⟨3241875003100134022452115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322500004133512029936153 3241875003100134022452115)
                      ·
                        rfl

theorem cell23_6313529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6313529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313529 prefixEnd_6313529 := by exact prefixLift 6313529
  have htrace : WordTrace (prefixWord ++ tailWord_6313529) baseStart_6313529 baseEnd_6313529 := by
    simpa [prefixWord, tailWord_6313529, baseEnd_6313529] using wordTrace_append hprefix tailTrace_6313529
  have hstable : (prefixWord ++ tailWord_6313529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313529).length < 2 ^ (prefixWord ++ tailWord_6313529).sum := by decide
  have hdescent : baseEnd_6313529 < baseStart_6313529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313535 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 5]
def baseStart_6313535 : Nat := 118140960795 + 6313535 * 2 ^ 59
def prefixEnd_6313535 : Nat := 4983230072969 + 3 ^ 40 * 6313535 * 2
def baseEnd_6313535 : Nat := 360208675998228999886343

theorem tailTrace_6313535 : CollatzResearch.WordTrace tailWord_6313535 prefixEnd_6313535 360208675998228999886343 := by
  unfold tailWord_6313535
  simp only [CollatzResearch.WordTrace]
  refine ⟨230273539182148435777974059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153515692788098957185316039 230273539182148435777974059)
  ·
    refine ⟨345410308773222653666961089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230273539182148435777974059 345410308773222653666961089)
    ·
      refine ⟨259057731579916990250220817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345410308773222653666961089 259057731579916990250220817)
      ·
        refine ⟨194293298684937742687665613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259057731579916990250220817 194293298684937742687665613)
        ·
          refine ⟨72859987006851653507874605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194293298684937742687665613 72859987006851653507874605)
          ·
            refine ⟨27322495127569370065452977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72859987006851653507874605 27322495127569370065452977)
            ·
              refine ⟨20491871345677027549089733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27322495127569370065452977 20491871345677027549089733)
              ·
                refine ⟨3842225877314442665454325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20491871345677027549089733 3842225877314442665454325)
                ·
                  refine ⟨360208675998228999886343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842225877314442665454325 360208675998228999886343)
                  ·
                    rfl

theorem cell23_6313535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 5].length) (baseStart_6313535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313535 prefixEnd_6313535 := by exact prefixLift 6313535
  have htrace : WordTrace (prefixWord ++ tailWord_6313535) baseStart_6313535 baseEnd_6313535 := by
    simpa [prefixWord, tailWord_6313535, baseEnd_6313535] using wordTrace_append hprefix tailTrace_6313535
  have hstable : (prefixWord ++ tailWord_6313535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313535).length < 2 ^ (prefixWord ++ tailWord_6313535).sum := by decide
  have hdescent : baseEnd_6313535 < baseStart_6313535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313548 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_6313548 : Nat := 118140960795 + 6313548 * 2 ^ 59
def prefixEnd_6313548 : Nat := 4983230072969 + 3 ^ 40 * 6313548 * 2
def baseEnd_6313548 : Nat := 1080628253077523149371509

theorem tailTrace_6313548 : CollatzResearch.WordTrace tailWord_6313548 prefixEnd_6313548 1080628253077523149371509 := by
  unfold tailWord_6313548
  simp only [CollatzResearch.WordTrace]
  refine ⟨115137006665550669499098649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153516008887400892665464865 115137006665550669499098649)
  ·
    refine ⟨86352754999163002124323987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115137006665550669499098649 86352754999163002124323987)
    ·
      refine ⟨129529132498744503186485981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86352754999163002124323987 129529132498744503186485981)
      ·
        refine ⟨48573424687029188694932243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129529132498744503186485981 48573424687029188694932243)
        ·
          refine ⟨72860137030543783042398365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48573424687029188694932243 72860137030543783042398365)
          ·
            refine ⟨27322551386453918640899387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72860137030543783042398365 27322551386453918640899387)
            ·
              refine ⟨40983827079680877961349081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27322551386453918640899387 40983827079680877961349081)
              ·
                refine ⟨30737870309760658471011811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40983827079680877961349081 30737870309760658471011811)
                ·
                  refine ⟨46106805464640987706517717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30737870309760658471011811 46106805464640987706517717)
                  ·
                    refine ⟨1080628253077523149371509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46106805464640987706517717 1080628253077523149371509)
                    ·
                      rfl

theorem cell23_6313548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_6313548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313548 prefixEnd_6313548 := by exact prefixLift 6313548
  have htrace : WordTrace (prefixWord ++ tailWord_6313548) baseStart_6313548 baseEnd_6313548 := by
    simpa [prefixWord, tailWord_6313548, baseEnd_6313548] using wordTrace_append hprefix tailTrace_6313548
  have hstable : (prefixWord ++ tailWord_6313548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313548).length < 2 ^ (prefixWord ++ tailWord_6313548).sum := by decide
  have hdescent : baseEnd_6313548 < baseStart_6313548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313582 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6313582 : Nat := 118140960795 + 6313582 * 2 ^ 59
def prefixEnd_6313582 : Nat := 4983230072969 + 3 ^ 40 * 6313582 * 2
def baseEnd_6313582 : Nat := 1080634072524940771696457

theorem tailTrace_6313582 : CollatzResearch.WordTrace tailWord_6313582 prefixEnd_6313582 1080634072524940771696457 := by
  unfold tailWord_6313582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28784406676622270350616875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153516835608652108536623333 28784406676622270350616875)
  ·
    refine ⟨43176610014933405525925313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28784406676622270350616875 43176610014933405525925313)
    ·
      refine ⟨32382457511200054144443985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43176610014933405525925313 32382457511200054144443985)
      ·
        refine ⟨24286843133400040608332989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32382457511200054144443985 24286843133400040608332989)
        ·
          refine ⟨9107566175025015228124871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24286843133400040608332989 9107566175025015228124871)
          ·
            refine ⟨13661349262537522842187307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107566175025015228124871 13661349262537522842187307)
            ·
              refine ⟨20492023893806284263280961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13661349262537522842187307 20492023893806284263280961)
              ·
                refine ⟨15369017920354713197460721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20492023893806284263280961 15369017920354713197460721)
                ·
                  refine ⟨11526763440266034898095541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15369017920354713197460721 11526763440266034898095541)
                  ·
                    refine ⟨1080634072524940771696457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11526763440266034898095541 1080634072524940771696457)
                    ·
                      rfl

theorem cell23_6313582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6313582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313582 prefixEnd_6313582 := by exact prefixLift 6313582
  have htrace : WordTrace (prefixWord ++ tailWord_6313582) baseStart_6313582 baseEnd_6313582 := by
    simpa [prefixWord, tailWord_6313582, baseEnd_6313582] using wordTrace_append hprefix tailTrace_6313582
  have hstable : (prefixWord ++ tailWord_6313582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313582).length < 2 ^ (prefixWord ++ tailWord_6313582).sum := by decide
  have hdescent : baseEnd_6313582 < baseStart_6313582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_6313585 : Nat := 118140960795 + 6313585 * 2 ^ 59
def prefixEnd_6313585 : Nat := 4983230072969 + 3 ^ 40 * 6313585 * 2
def baseEnd_6313585 : Nat := 3241903758016785803351857

theorem tailTrace_6313585 : CollatzResearch.WordTrace tailWord_6313585 prefixEnd_6313585 3241903758016785803351857 := by
  unfold tailWord_6313585
  simp only [CollatzResearch.WordTrace]
  refine ⟨230275362831967294317294209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153516908554644862878196139 230275362831967294317294209)
  ·
    refine ⟨172706522123975470737970657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230275362831967294317294209 172706522123975470737970657)
    ·
      refine ⟨129529891592981603053477993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172706522123975470737970657 129529891592981603053477993)
      ·
        refine ⟨97147418694736202290108495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129529891592981603053477993 97147418694736202290108495)
        ·
          refine ⟨145721128042104303435162743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97147418694736202290108495 145721128042104303435162743)
          ·
            refine ⟨218581692063156455152744115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145721128042104303435162743 218581692063156455152744115)
            ·
              refine ⟨327872538094734682729116173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218581692063156455152744115 327872538094734682729116173)
              ·
                refine ⟨122952201785525506023418565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327872538094734682729116173 122952201785525506023418565)
                ·
                  refine ⟨23053537834786032379390981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122952201785525506023418565 23053537834786032379390981)
                  ·
                    refine ⟨4322538344022381071135809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23053537834786032379390981 4322538344022381071135809)
                    ·
                      refine ⟨3241903758016785803351857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322538344022381071135809 3241903758016785803351857)
                      ·
                        rfl

theorem cell23_6313585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_6313585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313585 prefixEnd_6313585 := by exact prefixLift 6313585
  have htrace : WordTrace (prefixWord ++ tailWord_6313585) baseStart_6313585 baseEnd_6313585 := by
    simpa [prefixWord, tailWord_6313585, baseEnd_6313585] using wordTrace_append hprefix tailTrace_6313585
  have hstable : (prefixWord ++ tailWord_6313585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313585).length < 2 ^ (prefixWord ++ tailWord_6313585).sum := by decide
  have hdescent : baseEnd_6313585 < baseStart_6313585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313605 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_6313605 : Nat := 118140960795 + 6313605 * 2 ^ 59
def prefixEnd_6313605 : Nat := 4983230072969 + 3 ^ 40 * 6313605 * 2
def baseEnd_6313605 : Nat := 3241914027629875725101765

theorem tailTrace_6313605 : CollatzResearch.WordTrace tailWord_6313605 prefixEnd_6313605 3241914027629875725101765 := by
  unfold tailWord_6313605
  simp only [CollatzResearch.WordTrace]
  refine ⟨230276092291894837733022269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153517394861263225155348179 230276092291894837733022269)
  ·
    refine ⟨86353534609460564149883351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230276092291894837733022269 86353534609460564149883351)
    ·
      refine ⟨129530301914190846224825027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86353534609460564149883351 129530301914190846224825027)
      ·
        refine ⟨194295452871286269337237541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129530301914190846224825027 194295452871286269337237541)
        ·
          refine ⟨36430397413366175500732039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194295452871286269337237541 36430397413366175500732039)
          ·
            refine ⟨54645596120049263251098059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36430397413366175500732039 54645596120049263251098059)
            ·
              refine ⟨81968394180073894876647089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54645596120049263251098059 81968394180073894876647089)
              ·
                refine ⟨61476295635055421157485317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81968394180073894876647089 61476295635055421157485317)
                ·
                  refine ⟨11526805431572891467028497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61476295635055421157485317 11526805431572891467028497)
                  ·
                    refine ⟨8645104073679668600271373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11526805431572891467028497 8645104073679668600271373)
                    ·
                      refine ⟨3241914027629875725101765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645104073679668600271373 3241914027629875725101765)
                      ·
                        rfl

theorem cell23_6313605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_6313605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313605 prefixEnd_6313605 := by exact prefixLift 6313605
  have htrace : WordTrace (prefixWord ++ tailWord_6313605) baseStart_6313605 baseEnd_6313605 := by
    simpa [prefixWord, tailWord_6313605, baseEnd_6313605] using wordTrace_append hprefix tailTrace_6313605
  have hstable : (prefixWord ++ tailWord_6313605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313605).length < 2 ^ (prefixWord ++ tailWord_6313605).sum := by decide
  have hdescent : baseEnd_6313605 < baseStart_6313605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313645 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6313645 : Nat := 118140960795 + 6313645 * 2 ^ 59
def prefixEnd_6313645 : Nat := 4983230072969 + 3 ^ 40 * 6313645 * 2
def baseEnd_6313645 : Nat := 3241934566856055568601581

theorem tailTrace_6313645 : CollatzResearch.WordTrace tailWord_6313645 prefixEnd_6313645 3241934566856055568601581 := by
  unfold tailWord_6313645
  simp only [CollatzResearch.WordTrace]
  refine ⟨230277551211749924564478389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153518367474499949709652259 230277551211749924564478389)
  ·
    refine ⟨21588520426101555427919849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230277551211749924564478389 21588520426101555427919849)
    ·
      refine ⟨16191390319576166570939887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21588520426101555427919849 16191390319576166570939887)
      ·
        refine ⟨24287085479364249856409831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16191390319576166570939887 24287085479364249856409831)
        ·
          refine ⟨36430628219046374784614747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24287085479364249856409831 36430628219046374784614747)
          ·
            refine ⟨54645942328569562176922121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36430628219046374784614747 54645942328569562176922121)
            ·
              refine ⟨40984456746427171632691591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54645942328569562176922121 40984456746427171632691591)
              ·
                refine ⟨61476685119640757449037387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40984456746427171632691591 61476685119640757449037387)
                ·
                  refine ⟨92215027679461136173556081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61476685119640757449037387 92215027679461136173556081)
                  ·
                    refine ⟨69161270759595852130167061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92215027679461136173556081 69161270759595852130167061)
                    ·
                      refine ⟨3241934566856055568601581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69161270759595852130167061 3241934566856055568601581)
                      ·
                        rfl

theorem cell23_6313645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6313645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313645 prefixEnd_6313645 := by exact prefixLift 6313645
  have htrace : WordTrace (prefixWord ++ tailWord_6313645) baseStart_6313645 baseEnd_6313645 := by
    simpa [prefixWord, tailWord_6313645, baseEnd_6313645] using wordTrace_append hprefix tailTrace_6313645
  have hstable : (prefixWord ++ tailWord_6313645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313645).length < 2 ^ (prefixWord ++ tailWord_6313645).sum := by decide
  have hdescent : baseEnd_6313645 < baseStart_6313645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313655 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 3, 5]
def baseStart_6313655 : Nat := 118140960795 + 6313655 * 2 ^ 59
def prefixEnd_6313655 : Nat := 4983230072969 + 3 ^ 40 * 6313655 * 2
def baseEnd_6313655 : Nat := 1080646567220866843158845

theorem tailTrace_6313655 : CollatzResearch.WordTrace tailWord_6313655 prefixEnd_6313655 1080646567220866843158845 := by
  unfold tailWord_6313655
  simp only [CollatzResearch.WordTrace]
  refine ⟨230277915941713696272342419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153518610627809130848228279 230277915941713696272342419)
  ·
    refine ⟨345416873912570544408513629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230277915941713696272342419 345416873912570544408513629)
    ·
      refine ⟨129531327717213954153192611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345416873912570544408513629 129531327717213954153192611)
      ·
        refine ⟨194296991575820931229788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129531327717213954153192611 194296991575820931229788917)
        ·
          refine ⟨18215342960233212302792711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194296991575820931229788917 18215342960233212302792711)
          ·
            refine ⟨27323014440349818454189067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18215342960233212302792711 27323014440349818454189067)
            ·
              refine ⟨40984521660524727681283601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27323014440349818454189067 40984521660524727681283601)
              ·
                refine ⟨30738391245393545760962701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40984521660524727681283601 30738391245393545760962701)
                ·
                  refine ⟨11526896717022579660361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30738391245393545760962701 11526896717022579660361013)
                  ·
                    refine ⟨1080646567220866843158845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11526896717022579660361013 1080646567220866843158845)
                    ·
                      rfl

theorem cell23_6313655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_6313655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313655 prefixEnd_6313655 := by exact prefixLift 6313655
  have htrace : WordTrace (prefixWord ++ tailWord_6313655) baseStart_6313655 baseEnd_6313655 := by
    simpa [prefixWord, tailWord_6313655, baseEnd_6313655] using wordTrace_append hprefix tailTrace_6313655
  have hstable : (prefixWord ++ tailWord_6313655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313655).length < 2 ^ (prefixWord ++ tailWord_6313655).sum := by decide
  have hdescent : baseEnd_6313655 < baseStart_6313655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313689 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_6313689 : Nat := 118140960795 + 6313689 * 2 ^ 59
def prefixEnd_6313689 : Nat := 4983230072969 + 3 ^ 40 * 6313689 * 2
def baseEnd_6313689 : Nat := 1080652386668284465483793

theorem tailTrace_6313689 : CollatzResearch.WordTrace tailWord_6313689 prefixEnd_6313689 1080652386668284465483793 := by
  unfold tailWord_6313689
  simp only [CollatzResearch.WordTrace]
  refine ⟨230279156023590520079080121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153519437349060346719386747 230279156023590520079080121)
  ·
    refine ⟨172709367017692890059310091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230279156023590520079080121 172709367017692890059310091)
    ·
      refine ⟨259064050526539335088965137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172709367017692890059310091 259064050526539335088965137)
      ·
        refine ⟨194298037894904501316723853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259064050526539335088965137 194298037894904501316723853)
        ·
          refine ⟨72861764210589187993771445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194298037894904501316723853 72861764210589187993771445)
          ·
            refine ⟨6830790394742736374416073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72861764210589187993771445 6830790394742736374416073)
            ·
              refine ⟨5123092796057052280812055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830790394742736374416073 5123092796057052280812055)
              ·
                refine ⟨7684639194085578421218083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123092796057052280812055 7684639194085578421218083)
                ·
                  refine ⟨11526958791128367631827125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684639194085578421218083 11526958791128367631827125)
                  ·
                    refine ⟨1080652386668284465483793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11526958791128367631827125 1080652386668284465483793)
                    ·
                      rfl

theorem cell23_6313689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_6313689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313689 prefixEnd_6313689 := by exact prefixLift 6313689
  have htrace : WordTrace (prefixWord ++ tailWord_6313689) baseStart_6313689 baseEnd_6313689 := by
    simpa [prefixWord, tailWord_6313689, baseEnd_6313689] using wordTrace_append hprefix tailTrace_6313689
  have hstable : (prefixWord ++ tailWord_6313689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313689).length < 2 ^ (prefixWord ++ tailWord_6313689).sum := by decide
  have hdescent : baseEnd_6313689 < baseStart_6313689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313695 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_6313695 : Nat := 118140960795 + 6313695 * 2 ^ 59
def prefixEnd_6313695 : Nat := 4983230072969 + 3 ^ 40 * 6313695 * 2
def baseEnd_6313695 : Nat := 3241960240888780372976351

theorem tailTrace_6313695 : CollatzResearch.WordTrace tailWord_6313695 prefixEnd_6313695 3241960240888780372976351 := by
  unfold tailWord_6313695
  simp only [CollatzResearch.WordTrace]
  refine ⟨230279374861568783103798539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153519583241045855402532359 230279374861568783103798539)
  ·
    refine ⟨345419062292353174655697809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230279374861568783103798539 345419062292353174655697809)
    ·
      refine ⟨259064296719264880991773357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345419062292353174655697809 259064296719264880991773357)
      ·
        refine ⟨97149111269724330371915009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259064296719264880991773357 97149111269724330371915009)
        ·
          refine ⟨72861833452293247778936257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97149111269724330371915009 72861833452293247778936257)
          ·
            refine ⟨54646375089219935834202193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72861833452293247778936257 54646375089219935834202193)
            ·
              refine ⟨40984781316914951875651645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54646375089219935834202193 40984781316914951875651645)
              ·
                refine ⟨15369292993843106953369367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40984781316914951875651645 15369292993843106953369367)
                ·
                  refine ⟨23053939490764660430054051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15369292993843106953369367 23053939490764660430054051)
                  ·
                    refine ⟨34580909236146990645081077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23053939490764660430054051 34580909236146990645081077)
                    ·
                      refine ⟨3241960240888780372976351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34580909236146990645081077 3241960240888780372976351)
                      ·
                        rfl

theorem cell23_6313695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_6313695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313695 prefixEnd_6313695 := by exact prefixLift 6313695
  have htrace : WordTrace (prefixWord ++ tailWord_6313695) baseStart_6313695 baseEnd_6313695 := by
    simpa [prefixWord, tailWord_6313695, baseEnd_6313695] using wordTrace_append hprefix tailTrace_6313695
  have hstable : (prefixWord ++ tailWord_6313695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313695).length < 2 ^ (prefixWord ++ tailWord_6313695).sum := by decide
  have hdescent : baseEnd_6313695 < baseStart_6313695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313726 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_6313726 : Nat := 118140960795 + 6313726 * 2 ^ 59
def prefixEnd_6313726 : Nat := 4983230072969 + 3 ^ 40 * 6313726 * 2
def baseEnd_6313726 : Nat := 3241976158789069751688709

theorem tailTrace_6313726 : CollatzResearch.WordTrace tailWord_6313726 prefixEnd_6313726 3241976158789069751688709 := by
  unfold tailWord_6313726
  simp only [CollatzResearch.WordTrace]
  refine ⟨28785063190557059424772129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153520337016304316932118021 28785063190557059424772129)
  ·
    refine ⟨21588797392917794568579097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28785063190557059424772129 21588797392917794568579097)
    ·
      refine ⟨16191598044688345926434323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21588797392917794568579097 16191598044688345926434323)
      ·
        refine ⟨24287397067032518889651485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16191598044688345926434323 24287397067032518889651485)
        ·
          refine ⟨9107773900137194583619307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24287397067032518889651485 9107773900137194583619307)
          ·
            refine ⟨13661660850205791875428961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107773900137194583619307 13661660850205791875428961)
            ·
              refine ⟨10246245637654343906571721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13661660850205791875428961 10246245637654343906571721)
              ·
                refine ⟨7684684228240757929928791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246245637654343906571721 7684684228240757929928791)
                ·
                  refine ⟨11527026342361136894893187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684684228240757929928791 11527026342361136894893187)
                  ·
                    refine ⟨17290539513541705342339781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11527026342361136894893187 17290539513541705342339781)
                    ·
                      refine ⟨3241976158789069751688709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17290539513541705342339781 3241976158789069751688709)
                      ·
                        rfl

theorem cell23_6313726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_6313726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313726 prefixEnd_6313726 := by exact prefixLift 6313726
  have htrace : WordTrace (prefixWord ++ tailWord_6313726) baseStart_6313726 baseEnd_6313726 := by
    simpa [prefixWord, tailWord_6313726, baseEnd_6313726] using wordTrace_append hprefix tailTrace_6313726
  have hstable : (prefixWord ++ tailWord_6313726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313726).length < 2 ^ (prefixWord ++ tailWord_6313726).sum := by decide
  have hdescent : baseEnd_6313726 < baseStart_6313726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313732 : List Nat := [2, 3, 2, 2, 1, 2, 4, 7]
def baseStart_6313732 : Nat := 118140960795 + 6313732 * 2 ^ 59
def prefixEnd_6313732 : Nat := 4983230072969 + 3 ^ 40 * 6313732 * 2
def baseEnd_6313732 : Nat := 120073305173073952896803

theorem tailTrace_6313732 : CollatzResearch.WordTrace tailWord_6313732 prefixEnd_6313732 120073305173073952896803 := by
  unfold tailWord_6313732
  simp only [CollatzResearch.WordTrace]
  refine ⟨115140362181217369211447725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153520482908289825615263633 115140362181217369211447725)
  ·
    refine ⟨43177635817956513454292897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115140362181217369211447725 43177635817956513454292897)
    ·
      refine ⟨32383226863467385090719673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43177635817956513454292897 32383226863467385090719673)
      ·
        refine ⟨24287420147600538818039755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32383226863467385090719673 24287420147600538818039755)
        ·
          refine ⟨36431130221400808227059633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24287420147600538818039755 36431130221400808227059633)
          ·
            refine ⟨27323347666050606170294725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36431130221400808227059633 27323347666050606170294725)
            ·
              refine ⟨5123127687384488656930261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27323347666050606170294725 5123127687384488656930261)
              ·
                refine ⟨120073305173073952896803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5123127687384488656930261 120073305173073952896803)
                ·
                  rfl

theorem cell23_6313732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 7].length) (baseStart_6313732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313732 prefixEnd_6313732 := by exact prefixLift 6313732
  have htrace : WordTrace (prefixWord ++ tailWord_6313732) baseStart_6313732 baseEnd_6313732 := by
    simpa [prefixWord, tailWord_6313732, baseEnd_6313732] using wordTrace_append hprefix tailTrace_6313732
  have hstable : (prefixWord ++ tailWord_6313732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313732).length < 2 ^ (prefixWord ++ tailWord_6313732).sum := by decide
  have hdescent : baseEnd_6313732 < baseStart_6313732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313742 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6313742 : Nat := 118140960795 + 6313742 * 2 ^ 59
def prefixEnd_6313742 : Nat := 4983230072969 + 3 ^ 40 * 6313742 * 2
def baseEnd_6313742 : Nat := 3241984374479541689088635

theorem tailTrace_6313742 : CollatzResearch.WordTrace tailWord_6313742 prefixEnd_6313742 3241984374479541689088635 := by
  unfold tailWord_6313742
  simp only [CollatzResearch.WordTrace]
  refine ⟨28785136136549813766344935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153520726061599006753839653 28785136136549813766344935)
  ·
    refine ⟨43177704204824720649517403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28785136136549813766344935 43177704204824720649517403)
    ·
      refine ⟨64766556307237080974276105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43177704204824720649517403 64766556307237080974276105)
      ·
        refine ⟨48574917230427810730707079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64766556307237080974276105 48574917230427810730707079)
        ·
          refine ⟨72862375845641716096060619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48574917230427810730707079 72862375845641716096060619)
          ·
            refine ⟨109293563768462574144090929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72862375845641716096060619 109293563768462574144090929)
            ·
              refine ⟨81970172826346930608068197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109293563768462574144090929 81970172826346930608068197)
              ·
                refine ⟨15369407404940049489012787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81970172826346930608068197 15369407404940049489012787)
                ·
                  refine ⟨23054111107410074233519181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15369407404940049489012787 23054111107410074233519181)
                  ·
                    refine ⟨8645291665278777837569693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23054111107410074233519181 8645291665278777837569693)
                    ·
                      refine ⟨3241984374479541689088635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645291665278777837569693 3241984374479541689088635)
                      ·
                        rfl

theorem cell23_6313742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6313742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313742 prefixEnd_6313742 := by exact prefixLift 6313742
  have htrace : WordTrace (prefixWord ++ tailWord_6313742) baseStart_6313742 baseEnd_6313742 := by
    simpa [prefixWord, tailWord_6313742, baseEnd_6313742] using wordTrace_append hprefix tailTrace_6313742
  have hstable : (prefixWord ++ tailWord_6313742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313742).length < 2 ^ (prefixWord ++ tailWord_6313742).sum := by decide
  have hdescent : baseEnd_6313742 < baseStart_6313742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313746 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6313746 : Nat := 118140960795 + 6313746 * 2 ^ 59
def prefixEnd_6313746 : Nat := 4983230072969 + 3 ^ 40 * 6313746 * 2
def baseEnd_6313746 : Nat := 3241986428402159673438617

theorem tailTrace_6313746 : CollatzResearch.WordTrace tailWord_6313746 prefixEnd_6313746 3241986428402159673438617 := by
  unfold tailWord_6313746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57570308746096004703476273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153520823322922679209270061 57570308746096004703476273)
  ·
    refine ⟨43177731559572003527607205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57570308746096004703476273 43177731559572003527607205)
    ·
      refine ⟨8095824667419750661426351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43177731559572003527607205 8095824667419750661426351)
      ·
        refine ⟨12143737001129625992139527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095824667419750661426351 12143737001129625992139527)
        ·
          refine ⟨18215605501694438988209291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12143737001129625992139527 18215605501694438988209291)
          ·
            refine ⟨27323408252541658482313937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18215605501694438988209291 27323408252541658482313937)
            ·
              refine ⟨20492556189406243861735453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27323408252541658482313937 20492556189406243861735453)
              ·
                refine ⟨7684708571027341448150795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20492556189406243861735453 7684708571027341448150795)
                ·
                  refine ⟨11527062856541012172226193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684708571027341448150795 11527062856541012172226193)
                  ·
                    refine ⟨8645297142405759129169645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11527062856541012172226193 8645297142405759129169645)
                    ·
                      refine ⟨3241986428402159673438617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645297142405759129169645 3241986428402159673438617)
                      ·
                        rfl

theorem cell23_6313746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6313746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313746 prefixEnd_6313746 := by exact prefixLift 6313746
  have htrace : WordTrace (prefixWord ++ tailWord_6313746) baseStart_6313746 baseEnd_6313746 := by
    simpa [prefixWord, tailWord_6313746, baseEnd_6313746] using wordTrace_append hprefix tailTrace_6313746
  have hstable : (prefixWord ++ tailWord_6313746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313746).length < 2 ^ (prefixWord ++ tailWord_6313746).sum := by decide
  have hdescent : baseEnd_6313746 < baseStart_6313746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313759 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_6313759 : Nat := 118140960795 + 6313759 * 2 ^ 59
def prefixEnd_6313759 : Nat := 4983230072969 + 3 ^ 40 * 6313759 * 2
def baseEnd_6313759 : Nat := 3241993103650668122576057

theorem tailTrace_6313759 : CollatzResearch.WordTrace tailWord_6313759 prefixEnd_6313759 3241993103650668122576057 := by
  unfold tailWord_6313759
  simp only [CollatzResearch.WordTrace]
  refine ⟨230281709133336922034128331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153521139422224614689418887 230281709133336922034128331)
  ·
    refine ⟨345422563700005383051192497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230281709133336922034128331 345422563700005383051192497)
    ·
      refine ⟨259066922775004037288394373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345422563700005383051192497 259066922775004037288394373)
      ·
        refine ⟨48575048020313256991573945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259066922775004037288394373 48575048020313256991573945)
        ·
          refine ⟨36431286015234942743680459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48575048020313256991573945 36431286015234942743680459)
          ·
            refine ⟨54646929022852414115520689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36431286015234942743680459 54646929022852414115520689)
            ·
              refine ⟨40985196767139310586640517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54646929022852414115520689 40985196767139310586640517)
              ·
                refine ⟨7684724393838620734995097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40985196767139310586640517 7684724393838620734995097)
                ·
                  refine ⟨5763543295378965551246323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7684724393838620734995097 5763543295378965551246323)
                  ·
                    refine ⟨8645314943068448326869485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763543295378965551246323 8645314943068448326869485)
                    ·
                      refine ⟨3241993103650668122576057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645314943068448326869485 3241993103650668122576057)
                      ·
                        rfl

theorem cell23_6313759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_6313759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313759 prefixEnd_6313759 := by exact prefixLift 6313759
  have htrace : WordTrace (prefixWord ++ tailWord_6313759) baseStart_6313759 baseEnd_6313759 := by
    simpa [prefixWord, tailWord_6313759, baseEnd_6313759] using wordTrace_append hprefix tailTrace_6313759
  have hstable : (prefixWord ++ tailWord_6313759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313759).length < 2 ^ (prefixWord ++ tailWord_6313759).sum := by decide
  have hdescent : baseEnd_6313759 < baseStart_6313759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313786 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_6313786 : Nat := 118140960795 + 6313786 * 2 ^ 59
def prefixEnd_6313786 : Nat := 4983230072969 + 3 ^ 40 * 6313786 * 2
def baseEnd_6313786 : Nat := 3242006967628339516938433

theorem tailTrace_6313786 : CollatzResearch.WordTrace tailWord_6313786 prefixEnd_6313786 3242006967628339516938433 := by
  unfold tailWord_6313786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57570673476059776411340303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153521795936159403763574141 57570673476059776411340303)
  ·
    refine ⟨86356010214089664617010455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57570673476059776411340303 86356010214089664617010455)
    ·
      refine ⟨129534015321134496925515683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86356010214089664617010455 129534015321134496925515683)
      ·
        refine ⟨194301022981701745388273525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129534015321134496925515683 194301022981701745388273525)
        ·
          refine ⟨18215720904534538630150643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194301022981701745388273525 18215720904534538630150643)
          ·
            refine ⟨27323581356801807945225965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18215720904534538630150643 27323581356801807945225965)
            ·
              refine ⟨10246343008800677979459737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27323581356801807945225965 10246343008800677979459737)
              ·
                refine ⟨7684757256600508484594803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246343008800677979459737 7684757256600508484594803)
                ·
                  refine ⟨11527135884900762726892205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684757256600508484594803 11527135884900762726892205)
                  ·
                    refine ⟨4322675956837786022584577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11527135884900762726892205 4322675956837786022584577)
                    ·
                      refine ⟨3242006967628339516938433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322675956837786022584577 3242006967628339516938433)
                      ·
                        rfl

theorem cell23_6313786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_6313786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313786 prefixEnd_6313786 := by exact prefixLift 6313786
  have htrace : WordTrace (prefixWord ++ tailWord_6313786) baseStart_6313786 baseEnd_6313786 := by
    simpa [prefixWord, tailWord_6313786, baseEnd_6313786] using wordTrace_append hprefix tailTrace_6313786
  have hstable : (prefixWord ++ tailWord_6313786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313786).length < 2 ^ (prefixWord ++ tailWord_6313786).sum := by decide
  have hdescent : baseEnd_6313786 < baseStart_6313786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313799 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_6313799 : Nat := 118140960795 + 6313799 * 2 ^ 59
def prefixEnd_6313799 : Nat := 4983230072969 + 3 ^ 40 * 6313799 * 2
def baseEnd_6313799 : Nat := 3242013642876847966075873

theorem tailTrace_6313799 : CollatzResearch.WordTrace tailWord_6313799 prefixEnd_6313799 3242013642876847966075873 := by
  unfold tailWord_6313799
  simp only [CollatzResearch.WordTrace]
  refine ⟨230283168053192008865584451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153522112035461339243722967 230283168053192008865584451)
  ·
    refine ⟨345424752079788013298376677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230283168053192008865584451 345424752079788013298376677)
    ·
      refine ⟨64767141014960252493445627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345424752079788013298376677 64767141014960252493445627)
      ·
        refine ⟨97150711522440378740168441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64767141014960252493445627 97150711522440378740168441)
        ·
          refine ⟨72863033641830284055126331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97150711522440378740168441 72863033641830284055126331)
          ·
            refine ⟨109294550462745426082689497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72863033641830284055126331 109294550462745426082689497)
            ·
              refine ⟨81970912847059069562017123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109294550462745426082689497 81970912847059069562017123)
              ·
                refine ⟨122956369270588604343025685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81970912847059069562017123 122956369270588604343025685)
                ·
                  refine ⟨5763579809558840828579329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122956369270588604343025685 5763579809558840828579329)
                  ·
                    refine ⟨4322684857169130621434497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763579809558840828579329 4322684857169130621434497)
                    ·
                      refine ⟨3242013642876847966075873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322684857169130621434497 3242013642876847966075873)
                      ·
                        rfl

theorem cell23_6313799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_6313799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313799 prefixEnd_6313799 := by exact prefixLift 6313799
  have htrace : WordTrace (prefixWord ++ tailWord_6313799) baseStart_6313799 baseEnd_6313799 := by
    simpa [prefixWord, tailWord_6313799, baseEnd_6313799] using wordTrace_append hprefix tailTrace_6313799
  have hstable : (prefixWord ++ tailWord_6313799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313799).length < 2 ^ (prefixWord ++ tailWord_6313799).sum := by decide
  have hdescent : baseEnd_6313799 < baseStart_6313799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313835 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 7]
def baseStart_6313835 : Nat := 118140960795 + 6313835 * 2 ^ 59
def prefixEnd_6313835 : Nat := 4983230072969 + 3 ^ 40 * 6313835 * 2
def baseEnd_6313835 : Nat := 1080677376060136608408569

theorem tailTrace_6313835 : CollatzResearch.WordTrace tailWord_6313835 prefixEnd_6313835 1080677376060136608408569 := by
  unfold tailWord_6313835
  simp only [CollatzResearch.WordTrace]
  refine ⟨230284481081061587013894959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153522987387374391342596639 230284481081061587013894959)
  ·
    refine ⟨345426721621592380520842439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230284481081061587013894959 345426721621592380520842439)
    ·
      refine ⟨518140082432388570781263659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345426721621592380520842439 518140082432388570781263659)
      ·
        refine ⟨777210123648582856171895489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518140082432388570781263659 777210123648582856171895489)
        ·
          refine ⟨582907592736437142128921617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777210123648582856171895489 582907592736437142128921617)
          ·
            refine ⟨437180694552327856596691213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582907592736437142128921617 437180694552327856596691213)
            ·
              refine ⟨163942760457122946223759205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437180694552327856596691213 163942760457122946223759205)
              ·
                refine ⟨30739267585710552416954851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163942760457122946223759205 30739267585710552416954851)
                ·
                  refine ⟨46108901378565828625432277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30739267585710552416954851 46108901378565828625432277)
                  ·
                    refine ⟨1080677376060136608408569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46108901378565828625432277 1080677376060136608408569)
                    ·
                      rfl

theorem cell23_6313835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_6313835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313835 prefixEnd_6313835 := by exact prefixLift 6313835
  have htrace : WordTrace (prefixWord ++ tailWord_6313835) baseStart_6313835 baseEnd_6313835 := by
    simpa [prefixWord, tailWord_6313835, baseEnd_6313835] using wordTrace_append hprefix tailTrace_6313835
  have hstable : (prefixWord ++ tailWord_6313835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313835).length < 2 ^ (prefixWord ++ tailWord_6313835).sum := by decide
  have hdescent : baseEnd_6313835 < baseStart_6313835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313909 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6313909 : Nat := 118140960795 + 6313909 * 2 ^ 59
def prefixEnd_6313909 : Nat := 4983230072969 + 3 ^ 40 * 6313909 * 2
def baseEnd_6313909 : Nat := 3242070125748842535700367

theorem tailTrace_6313909 : CollatzResearch.WordTrace tailWord_6313909 prefixEnd_6313909 3242070125748842535700367 := by
  unfold tailWord_6313909
  simp only [CollatzResearch.WordTrace]
  refine ⟨230287180082793497652088781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153524786721862331768059187 230287180082793497652088781)
  ·
    refine ⟨86357692531047561619533293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230287180082793497652088781 86357692531047561619533293)
    ·
      refine ⟨32384134699142835607324985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86357692531047561619533293 32384134699142835607324985)
      ·
        refine ⟨24288101024357126705493739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32384134699142835607324985 24288101024357126705493739)
        ·
          refine ⟨36432151536535690058240609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24288101024357126705493739 36432151536535690058240609)
          ·
            refine ⟨27324113652401767543680457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36432151536535690058240609 27324113652401767543680457)
            ·
              refine ⟨20493085239301325657760343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27324113652401767543680457 20493085239301325657760343)
              ·
                refine ⟨30739627858951988486640515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20493085239301325657760343 30739627858951988486640515)
                ·
                  refine ⟨46109441788427982729960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30739627858951988486640515 46109441788427982729960773)
                  ·
                    refine ⟨8645520335330246761867645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46109441788427982729960773 8645520335330246761867645)
                    ·
                      refine ⟨3242070125748842535700367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645520335330246761867645 3242070125748842535700367)
                      ·
                        rfl

theorem cell23_6313909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6313909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313909 prefixEnd_6313909 := by exact prefixLift 6313909
  have htrace : WordTrace (prefixWord ++ tailWord_6313909) baseStart_6313909 baseEnd_6313909 := by
    simpa [prefixWord, tailWord_6313909, baseEnd_6313909] using wordTrace_append hprefix tailTrace_6313909
  have hstable : (prefixWord ++ tailWord_6313909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313909).length < 2 ^ (prefixWord ++ tailWord_6313909).sum := by decide
  have hdescent : baseEnd_6313909 < baseStart_6313909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6313979 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 4]
def baseStart_6313979 : Nat := 118140960795 + 6313979 * 2 ^ 59
def prefixEnd_6313979 : Nat := 4983230072969 + 3 ^ 40 * 6313979 * 2
def baseEnd_6313979 : Nat := 3242106069394657261825045

theorem tailTrace_6313979 : CollatzResearch.WordTrace tailWord_6313979 prefixEnd_6313979 3242106069394657261825045 := by
  unfold tailWord_6313979
  simp only [CollatzResearch.WordTrace]
  refine ⟨230289733192539899607136991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153526488795026599738091327 230289733192539899607136991)
  ·
    refine ⟨345434599788809849410705487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230289733192539899607136991 345434599788809849410705487)
    ·
      refine ⟨518151899683214774116058231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345434599788809849410705487 518151899683214774116058231)
      ·
        refine ⟨777227849524822161174087347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518151899683214774116058231 777227849524822161174087347)
        ·
          refine ⟨1165841774287233241761131021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777227849524822161174087347 1165841774287233241761131021)
          ·
            refine ⟨437190665357712465660424133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1165841774287233241761131021 437190665357712465660424133)
            ·
              refine ⟨81973249754571087311329525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437190665357712465660424133 81973249754571087311329525)
              ·
                refine ⟨7684992164491039435437143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81973249754571087311329525 7684992164491039435437143)
                ·
                  refine ⟨11527488246736559153155715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684992164491039435437143 11527488246736559153155715)
                  ·
                    refine ⟨17291232370104838729733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11527488246736559153155715 17291232370104838729733573)
                    ·
                      refine ⟨3242106069394657261825045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17291232370104838729733573 3242106069394657261825045)
                      ·
                        rfl

theorem cell23_6313979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 4].length) (baseStart_6313979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6313979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6313979 prefixEnd_6313979 := by exact prefixLift 6313979
  have htrace : WordTrace (prefixWord ++ tailWord_6313979) baseStart_6313979 baseEnd_6313979 := by
    simpa [prefixWord, tailWord_6313979, baseEnd_6313979] using wordTrace_append hprefix tailTrace_6313979
  have hstable : (prefixWord ++ tailWord_6313979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6313979).length < 2 ^ (prefixWord ++ tailWord_6313979).sum := by decide
  have hdescent : baseEnd_6313979 < baseStart_6313979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6313979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314013 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_6314013 : Nat := 118140960795 + 6314013 * 2 ^ 59
def prefixEnd_6314013 : Nat := 4983230072969 + 3 ^ 40 * 6314013 * 2
def baseEnd_6314013 : Nat := 3242123527736910128799889

theorem tailTrace_6314013 : CollatzResearch.WordTrace tailWord_6314013 prefixEnd_6314013 3242123527736910128799889 := by
  unfold tailWord_6314013
  simp only [CollatzResearch.WordTrace]
  refine ⟨230290973274416723413874693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153527315516277815609249795 230290973274416723413874693)
  ·
    refine ⟨43179557488953135640101505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230290973274416723413874693 43179557488953135640101505)
    ·
      refine ⟨32384668116714851730076129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43179557488953135640101505 32384668116714851730076129)
      ·
        refine ⟨24288501087536138797557097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32384668116714851730076129 24288501087536138797557097)
        ·
          refine ⟨18216375815652104098167823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24288501087536138797557097 18216375815652104098167823)
          ·
            refine ⟨27324563723478156147251735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18216375815652104098167823 27324563723478156147251735)
            ·
              refine ⟨40986845585217234220877603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27324563723478156147251735 40986845585217234220877603)
              ·
                refine ⟨61480268377825851331316405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40986845585217234220877603 61480268377825851331316405)
                ·
                  refine ⟨5763775160421173562310913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61480268377825851331316405 5763775160421173562310913)
                  ·
                    refine ⟨4322831370315880171733185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763775160421173562310913 4322831370315880171733185)
                    ·
                      refine ⟨3242123527736910128799889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322831370315880171733185 3242123527736910128799889)
                      ·
                        rfl

theorem cell23_6314013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_6314013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314013 prefixEnd_6314013 := by exact prefixLift 6314013
  have htrace : WordTrace (prefixWord ++ tailWord_6314013) baseStart_6314013 baseEnd_6314013 := by
    simpa [prefixWord, tailWord_6314013, baseEnd_6314013] using wordTrace_append hprefix tailTrace_6314013
  have hstable : (prefixWord ++ tailWord_6314013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314013).length < 2 ^ (prefixWord ++ tailWord_6314013).sum := by decide
  have hdescent : baseEnd_6314013 < baseStart_6314013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314019 : List Nat := [1, 1, 1, 4, 3, 1, 5, 7]
def baseStart_6314019 : Nat := 118140960795 + 6314019 * 2 ^ 59
def prefixEnd_6314019 : Nat := 4983230072969 + 3 ^ 40 * 6314019 * 2
def baseEnd_6314019 : Nat := 120078763282253226123143

theorem tailTrace_6314019 : CollatzResearch.WordTrace tailWord_6314019 prefixEnd_6314019 120078763282253226123143 := by
  unfold tailWord_6314019
  simp only [CollatzResearch.WordTrace]
  refine ⟨230291192112394986438593111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153527461408263324292395407 230291192112394986438593111)
  ·
    refine ⟨345436788168592479657889667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230291192112394986438593111 345436788168592479657889667)
    ·
      refine ⟨518155182252888719486834501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345436788168592479657889667 518155182252888719486834501)
      ·
        refine ⟨97154096672416634903781469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518155182252888719486834501 97154096672416634903781469)
        ·
          refine ⟨36432786252156238088918051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97154096672416634903781469 36432786252156238088918051)
          ·
            refine ⟨54649179378234357133377077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36432786252156238088918051 54649179378234357133377077)
            ·
              refine ⟨5123360566709470981254101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54649179378234357133377077 5123360566709470981254101)
              ·
                refine ⟨120078763282253226123143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5123360566709470981254101 120078763282253226123143)
                ·
                  rfl

theorem cell23_6314019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 7].length) (baseStart_6314019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314019 prefixEnd_6314019 := by exact prefixLift 6314019
  have htrace : WordTrace (prefixWord ++ tailWord_6314019) baseStart_6314019 baseEnd_6314019 := by
    simpa [prefixWord, tailWord_6314019, baseEnd_6314019] using wordTrace_append hprefix tailTrace_6314019
  have hstable : (prefixWord ++ tailWord_6314019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314019).length < 2 ^ (prefixWord ++ tailWord_6314019).sum := by decide
  have hdescent : baseEnd_6314019 < baseStart_6314019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314026 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6314026 : Nat := 118140960795 + 6314026 * 2 ^ 59
def prefixEnd_6314026 : Nat := 4983230072969 + 3 ^ 40 * 6314026 * 2
def baseEnd_6314026 : Nat := 3242130202985418577937329

theorem tailTrace_6314026 : CollatzResearch.WordTrace tailWord_6314026 prefixEnd_6314026 3242130202985418577937329 := by
  unfold tailWord_6314026
  simp only [CollatzResearch.WordTrace]
  refine ⟨57572861855842406658524483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153527631615579751089398621 57572861855842406658524483)
  ·
    refine ⟨86359292783763609987786725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57572861855842406658524483 86359292783763609987786725)
    ·
      refine ⟨16192367396955676872710011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86359292783763609987786725 16192367396955676872710011)
      ·
        refine ⟨24288551095433515309065017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16192367396955676872710011 24288551095433515309065017)
        ·
          refine ⟨18216413321575136481798763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24288551095433515309065017 18216413321575136481798763)
          ·
            refine ⟨27324619982362704722698145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18216413321575136481798763 27324619982362704722698145)
            ·
              refine ⟨20493464986772028542023609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27324619982362704722698145 20493464986772028542023609)
              ·
                refine ⟨15370098740079021406517707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20493464986772028542023609 15370098740079021406517707)
                ·
                  refine ⟨23055148110118532109776561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15370098740079021406517707 23055148110118532109776561)
                  ·
                    refine ⟨17291361082588899082332421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23055148110118532109776561 17291361082588899082332421)
                    ·
                      refine ⟨3242130202985418577937329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17291361082588899082332421 3242130202985418577937329)
                      ·
                        rfl

theorem cell23_6314026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6314026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314026 prefixEnd_6314026 := by exact prefixLift 6314026
  have htrace : WordTrace (prefixWord ++ tailWord_6314026) baseStart_6314026 baseEnd_6314026 := by
    simpa [prefixWord, tailWord_6314026, baseEnd_6314026] using wordTrace_append hprefix tailTrace_6314026
  have hstable : (prefixWord ++ tailWord_6314026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314026).length < 2 ^ (prefixWord ++ tailWord_6314026).sum := by decide
  have hdescent : baseEnd_6314026 < baseStart_6314026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314030 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6314030 : Nat := 118140960795 + 6314030 * 2 ^ 59
def prefixEnd_6314030 : Nat := 4983230072969 + 3 ^ 40 * 6314030 * 2
def baseEnd_6314030 : Nat := 3242132256908036562287311

theorem tailTrace_6314030 : CollatzResearch.WordTrace tailWord_6314030 prefixEnd_6314030 3242132256908036562287311 := by
  unfold tailWord_6314030
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786449164419391914655443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153527728876903423544829029 28786449164419391914655443)
  ·
    refine ⟨43179673746629087871983165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786449164419391914655443 43179673746629087871983165)
    ·
      refine ⟨16192377654985907951993687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43179673746629087871983165 16192377654985907951993687)
      ·
        refine ⟨24288566482478861927990531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16192377654985907951993687 24288566482478861927990531)
        ·
          refine ⟨36432849723718292891985797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24288566482478861927990531 36432849723718292891985797)
          ·
            refine ⟨6831159323197179917247337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36432849723718292891985797 6831159323197179917247337)
            ·
              refine ⟨5123369492397884937935503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831159323197179917247337 5123369492397884937935503)
              ·
                refine ⟨7685054238596827406903255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123369492397884937935503 7685054238596827406903255)
                ·
                  refine ⟨11527581357895241110354883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685054238596827406903255 11527581357895241110354883)
                  ·
                    refine ⟨17291372036842861665532325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11527581357895241110354883 17291372036842861665532325)
                    ·
                      refine ⟨3242132256908036562287311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17291372036842861665532325 3242132256908036562287311)
                      ·
                        rfl

theorem cell23_6314030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6314030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314030 prefixEnd_6314030 := by exact prefixLift 6314030
  have htrace : WordTrace (prefixWord ++ tailWord_6314030) baseStart_6314030 baseEnd_6314030 := by
    simpa [prefixWord, tailWord_6314030, baseEnd_6314030] using wordTrace_append hprefix tailTrace_6314030
  have hstable : (prefixWord ++ tailWord_6314030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314030).length < 2 ^ (prefixWord ++ tailWord_6314030).sum := by decide
  have hdescent : baseEnd_6314030 < baseStart_6314030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314033 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_6314033 : Nat := 118140960795 + 6314033 * 2 ^ 59
def prefixEnd_6314033 : Nat := 4983230072969 + 3 ^ 40 * 6314033 * 2
def baseEnd_6314033 : Nat := 3242133797350000050549797

theorem tailTrace_6314033 : CollatzResearch.WordTrace tailWord_6314033 prefixEnd_6314033 3242133797350000050549797 := by
  unfold tailWord_6314033
  simp only [CollatzResearch.WordTrace]
  refine ⟨230291702734344266829602753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153527801822896177886401835 230291702734344266829602753)
  ·
    refine ⟨172718777050758200122202065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230291702734344266829602753 172718777050758200122202065)
    ·
      refine ⟨129539082788068650091651549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172718777050758200122202065 129539082788068650091651549)
      ·
        refine ⟨48577156045525743784369331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129539082788068650091651549 48577156045525743784369331)
        ·
          refine ⟨72865734068288615676553997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48577156045525743784369331 72865734068288615676553997)
          ·
            refine ⟨27324650275608230878707749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72865734068288615676553997 27324650275608230878707749)
            ·
              refine ⟨5123371926676543289757703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27324650275608230878707749 5123371926676543289757703)
              ·
                refine ⟨7685057890014814934636555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123371926676543289757703 7685057890014814934636555)
                ·
                  refine ⟨11527586835022222401954833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685057890014814934636555 11527586835022222401954833)
                  ·
                    refine ⟨8645690126266666801466125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11527586835022222401954833 8645690126266666801466125)
                    ·
                      refine ⟨3242133797350000050549797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645690126266666801466125 3242133797350000050549797)
                      ·
                        rfl

theorem cell23_6314033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_6314033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314033 prefixEnd_6314033 := by exact prefixLift 6314033
  have htrace : WordTrace (prefixWord ++ tailWord_6314033) baseStart_6314033 baseEnd_6314033 := by
    simpa [prefixWord, tailWord_6314033, baseEnd_6314033] using wordTrace_append hprefix tailTrace_6314033
  have hstable : (prefixWord ++ tailWord_6314033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314033).length < 2 ^ (prefixWord ++ tailWord_6314033).sum := by decide
  have hdescent : baseEnd_6314033 < baseStart_6314033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314036 : List Nat := [2, 5, 1, 2, 2, 1, 10]
def baseStart_6314036 : Nat := 118140960795 + 6314036 * 2 ^ 59
def prefixEnd_6314036 : Nat := 4983230072969 + 3 ^ 40 * 6314036 * 2
def baseEnd_6314036 : Nat := 40026362194962512824843

theorem tailTrace_6314036 : CollatzResearch.WordTrace tailWord_6314036 prefixEnd_6314036 40026362194962512824843 := by
  unfold tailWord_6314036
  simp only [CollatzResearch.WordTrace]
  refine ⟨115145906076666699170980981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153527874768888932227974641 115145906076666699170980981)
  ·
    refine ⟨10794928694687503047279467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115145906076666699170980981 10794928694687503047279467)
    ·
      refine ⟨16192393042031254570919201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10794928694687503047279467 16192393042031254570919201)
      ·
        refine ⟨12144294781523440928189401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16192393042031254570919201 12144294781523440928189401)
        ·
          refine ⟨9108221086142580696142051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12144294781523440928189401 9108221086142580696142051)
          ·
            refine ⟨13662331629213871044213077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108221086142580696142051 13662331629213871044213077)
            ·
              refine ⟨40026362194962512824843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13662331629213871044213077 40026362194962512824843)
              ·
                rfl

theorem cell23_6314036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 10].length) (baseStart_6314036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314036 prefixEnd_6314036 := by exact prefixLift 6314036
  have htrace : WordTrace (prefixWord ++ tailWord_6314036) baseStart_6314036 baseEnd_6314036 := by
    simpa [prefixWord, tailWord_6314036, baseEnd_6314036] using wordTrace_append hprefix tailTrace_6314036
  have hstable : (prefixWord ++ tailWord_6314036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314036).length < 2 ^ (prefixWord ++ tailWord_6314036).sum := by decide
  have hdescent : baseEnd_6314036 < baseStart_6314036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314040 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_6314040 : Nat := 118140960795 + 6314040 * 2 ^ 59
def prefixEnd_6314040 : Nat := 4983230072969 + 3 ^ 40 * 6314040 * 2
def baseEnd_6314040 : Nat := 1080712463904860507720755

theorem tailTrace_6314040 : CollatzResearch.WordTrace tailWord_6314040 prefixEnd_6314040 1080712463904860507720755 := by
  unfold tailWord_6314040
  simp only [CollatzResearch.WordTrace]
  refine ⟨115145979022659453512553787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153527972030212604683405049 115145979022659453512553787)
  ·
    refine ⟨172718968533989180268830681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115145979022659453512553787 172718968533989180268830681)
    ·
      refine ⟨129539226400491885201623011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172718968533989180268830681 129539226400491885201623011)
      ·
        refine ⟨194308839600737827802434517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129539226400491885201623011 194308839600737827802434517)
        ·
          refine ⟨4554113428142292839119559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194308839600737827802434517 4554113428142292839119559)
          ·
            refine ⟨6831170142213439258679339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554113428142292839119559 6831170142213439258679339)
            ·
              refine ⟨10246755213320158888019009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831170142213439258679339 10246755213320158888019009)
              ·
                refine ⟨7685066409990119166014257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246755213320158888019009 7685066409990119166014257)
                ·
                  refine ⟨5763799807492589374510693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685066409990119166014257 5763799807492589374510693)
                  ·
                    refine ⟨1080712463904860507720755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763799807492589374510693 1080712463904860507720755)
                    ·
                      rfl

theorem cell23_6314040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_6314040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314040 prefixEnd_6314040 := by exact prefixLift 6314040
  have htrace : WordTrace (prefixWord ++ tailWord_6314040) baseStart_6314040 baseEnd_6314040 := by
    simpa [prefixWord, tailWord_6314040, baseEnd_6314040] using wordTrace_append hprefix tailTrace_6314040
  have hstable : (prefixWord ++ tailWord_6314040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314040).length < 2 ^ (prefixWord ++ tailWord_6314040).sum := by decide
  have hdescent : baseEnd_6314040 < baseStart_6314040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314056 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_6314056 : Nat := 118140960795 + 6314056 * 2 ^ 59
def prefixEnd_6314056 : Nat := 4983230072969 + 3 ^ 40 * 6314056 * 2
def baseEnd_6314056 : Nat := 3242145607405053460562191

theorem tailTrace_6314056 : CollatzResearch.WordTrace tailWord_6314056 prefixEnd_6314056 3242145607405053460562191 := by
  unfold tailWord_6314056
  simp only [CollatzResearch.WordTrace]
  refine ⟨115146270806630470878845011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153528361075507294505126681 115146270806630470878845011)
  ·
    refine ⟨172719406209945706318267517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115146270806630470878845011 172719406209945706318267517)
    ·
      refine ⟨64769777328729639869350319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172719406209945706318267517 64769777328729639869350319)
      ·
        refine ⟨97154665993094459804025479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64769777328729639869350319 97154665993094459804025479)
        ·
          refine ⟨145731998989641689706038219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97154665993094459804025479 145731998989641689706038219)
          ·
            refine ⟨218597998484462534559057329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145731998989641689706038219 218597998484462534559057329)
            ·
              refine ⟨163948498863346900919292997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218597998484462534559057329 163948498863346900919292997)
              ·
                refine ⟨30740343536877543922367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163948498863346900919292997 30740343536877543922367437)
                ·
                  refine ⟨11527628826329078970887789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30740343536877543922367437 11527628826329078970887789)
                  ·
                    refine ⟨4322860809873404614082921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11527628826329078970887789 4322860809873404614082921)
                    ·
                      refine ⟨3242145607405053460562191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322860809873404614082921 3242145607405053460562191)
                      ·
                        rfl

theorem cell23_6314056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_6314056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314056 prefixEnd_6314056 := by exact prefixLift 6314056
  have htrace : WordTrace (prefixWord ++ tailWord_6314056) baseStart_6314056 baseEnd_6314056 := by
    simpa [prefixWord, tailWord_6314056, baseEnd_6314056] using wordTrace_append hprefix tailTrace_6314056
  have hstable : (prefixWord ++ tailWord_6314056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314056).length < 2 ^ (prefixWord ++ tailWord_6314056).sum := by decide
  have hdescent : baseEnd_6314056 < baseStart_6314056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314070 : List Nat := [5, 2, 2, 1, 1, 3, 2, 7]
def baseStart_6314070 : Nat := 118140960795 + 6314070 * 2 ^ 59
def prefixEnd_6314070 : Nat := 4983230072969 + 3 ^ 40 * 6314070 * 2
def baseEnd_6314070 : Nat := 120079733190156163177301

theorem tailTrace_6314070 : CollatzResearch.WordTrace tailWord_6314070 prefixEnd_6314070 120079733190156163177301 := by
  unfold tailWord_6314070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393315764700638884293729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153528701490140148099133109 14393315764700638884293729)
  ·
    refine ⟨10794986823525479163220297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14393315764700638884293729 10794986823525479163220297)
    ·
      refine ⟨8096240117644109372415223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10794986823525479163220297 8096240117644109372415223)
      ·
        refine ⟨12144360176466164058622835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096240117644109372415223 12144360176466164058622835)
        ·
          refine ⟨18216540264699246087934253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12144360176466164058622835 18216540264699246087934253)
          ·
            refine ⟨6831202599262217282975345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18216540264699246087934253 6831202599262217282975345)
            ·
              refine ⟨5123401949446662962231509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831202599262217282975345 5123401949446662962231509)
              ·
                refine ⟨120079733190156163177301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5123401949446662962231509 120079733190156163177301)
                ·
                  rfl

theorem cell23_6314070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_6314070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314070 prefixEnd_6314070 := by exact prefixLift 6314070
  have htrace : WordTrace (prefixWord ++ tailWord_6314070) baseStart_6314070 baseEnd_6314070 := by
    simpa [prefixWord, tailWord_6314070, baseEnd_6314070] using wordTrace_append hprefix tailTrace_6314070
  have hstable : (prefixWord ++ tailWord_6314070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314070).length < 2 ^ (prefixWord ++ tailWord_6314070).sum := by decide
  have hdescent : baseEnd_6314070 < baseStart_6314070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314073 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 1, 3, 2]
def baseStart_6314073 : Nat := 118140960795 + 6314073 * 2 ^ 59
def prefixEnd_6314073 : Nat := 4983230072969 + 3 ^ 40 * 6314073 * 2
def baseEnd_6314073 : Nat := 3242154336576179894049613

theorem tailTrace_6314073 : CollatzResearch.WordTrace tailWord_6314073 prefixEnd_6314073 3242154336576179894049613 := by
  unfold tailWord_6314073
  simp only [CollatzResearch.WordTrace]
  refine ⟨230293161654199353661058873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153528774436132902440705915 230293161654199353661058873)
  ·
    refine ⟨172719871240649515245794155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230293161654199353661058873 172719871240649515245794155)
    ·
      refine ⟨259079806860974272868691233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172719871240649515245794155 259079806860974272868691233)
      ·
        refine ⟨194309855145730704651518425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259079806860974272868691233 194309855145730704651518425)
        ·
          refine ⟨145732391359298028488638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194309855145730704651518425 145732391359298028488638819)
          ·
            refine ⟨218598587038947042732958229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145732391359298028488638819 218598587038947042732958229)
            ·
              refine ⟨10246808767450642628107417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 218598587038947042732958229 10246808767450642628107417)
              ·
                refine ⟨7685106575587981971080563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246808767450642628107417 7685106575587981971080563)
                ·
                  refine ⟨11527659863381972956620845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685106575587981971080563 11527659863381972956620845)
                  ·
                    refine ⟨4322872448768239858732817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11527659863381972956620845 4322872448768239858732817)
                    ·
                      refine ⟨3242154336576179894049613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322872448768239858732817 3242154336576179894049613)
                      ·
                        rfl

theorem cell23_6314073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_6314073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314073 prefixEnd_6314073 := by exact prefixLift 6314073
  have htrace : WordTrace (prefixWord ++ tailWord_6314073) baseStart_6314073 baseEnd_6314073 := by
    simpa [prefixWord, tailWord_6314073, baseEnd_6314073] using wordTrace_append hprefix tailTrace_6314073
  have hstable : (prefixWord ++ tailWord_6314073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314073).length < 2 ^ (prefixWord ++ tailWord_6314073).sum := by decide
  have hdescent : baseEnd_6314073 < baseStart_6314073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314089 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_6314089 : Nat := 118140960795 + 6314089 * 2 ^ 59
def prefixEnd_6314089 : Nat := 4983230072969 + 3 ^ 40 * 6314089 * 2
def baseEnd_6314089 : Nat := 3242162552266651831449539

theorem tailTrace_6314089 : CollatzResearch.WordTrace tailWord_6314089 prefixEnd_6314089 3242162552266651831449539 := by
  unfold tailWord_6314089
  simp only [CollatzResearch.WordTrace]
  refine ⟨230293745222141388393641321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153529163481427592262427547 230293745222141388393641321)
  ·
    refine ⟨172720308916606041295230991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230293745222141388393641321 172720308916606041295230991)
    ·
      refine ⟨259080463374909061942846487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172720308916606041295230991 259080463374909061942846487)
      ·
        refine ⟨388620695062363592914269731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259080463374909061942846487 388620695062363592914269731)
        ·
          refine ⟨582931042593545389371404597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388620695062363592914269731 582931042593545389371404597)
          ·
            refine ⟨54649785243144880253569181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 582931042593545389371404597 54649785243144880253569181)
            ·
              refine ⟨20493669466179330095088443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54649785243144880253569181 20493669466179330095088443)
              ·
                refine ⟨30740504199268995142632665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20493669466179330095088443 30740504199268995142632665)
                ·
                  refine ⟨23055378149451746356974499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30740504199268995142632665 23055378149451746356974499)
                  ·
                    refine ⟨34583067224177619535461749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23055378149451746356974499 34583067224177619535461749)
                    ·
                      refine ⟨3242162552266651831449539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34583067224177619535461749 3242162552266651831449539)
                      ·
                        rfl

theorem cell23_6314089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_6314089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314089 prefixEnd_6314089 := by exact prefixLift 6314089
  have htrace : WordTrace (prefixWord ++ tailWord_6314089) baseStart_6314089 baseEnd_6314089 := by
    simpa [prefixWord, tailWord_6314089, baseEnd_6314089] using wordTrace_append hprefix tailTrace_6314089
  have hstable : (prefixWord ++ tailWord_6314089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314089).length < 2 ^ (prefixWord ++ tailWord_6314089).sum := by decide
  have hdescent : baseEnd_6314089 < baseStart_6314089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314103 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_6314103 : Nat := 118140960795 + 6314103 * 2 ^ 59
def prefixEnd_6314103 : Nat := 4983230072969 + 3 ^ 40 * 6314103 * 2
def baseEnd_6314103 : Nat := 3242169740995814776674475

theorem tailTrace_6314103 : CollatzResearch.WordTrace tailWord_6314103 prefixEnd_6314103 3242169740995814776674475 := by
  unfold tailWord_6314103
  simp only [CollatzResearch.WordTrace]
  refine ⟨230294255844090668784650963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153529503896060445856433975 230294255844090668784650963)
  ·
    refine ⟨345441383766136003176976445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230294255844090668784650963 345441383766136003176976445)
    ·
      refine ⟨129540518912301001191366167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345441383766136003176976445 129540518912301001191366167)
      ·
        refine ⟨194310778368451501787049251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129540518912301001191366167 194310778368451501787049251)
        ·
          refine ⟨291466167552677252680573877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194310778368451501787049251 291466167552677252680573877)
          ·
            refine ⟨27324953208063492438803801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291466167552677252680573877 27324953208063492438803801)
            ·
              refine ⟨20493714906047619329102851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27324953208063492438803801 20493714906047619329102851)
              ·
                refine ⟨30740572359071428993654277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20493714906047619329102851 30740572359071428993654277)
                ·
                  refine ⟨5763857317325892936310177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30740572359071428993654277 5763857317325892936310177)
                  ·
                    refine ⟨4322892987994419702232633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763857317325892936310177 4322892987994419702232633)
                    ·
                      refine ⟨3242169740995814776674475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322892987994419702232633 3242169740995814776674475)
                      ·
                        rfl

theorem cell23_6314103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_6314103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314103 prefixEnd_6314103 := by exact prefixLift 6314103
  have htrace : WordTrace (prefixWord ++ tailWord_6314103) baseStart_6314103 baseEnd_6314103 := by
    simpa [prefixWord, tailWord_6314103, baseEnd_6314103] using wordTrace_append hprefix tailTrace_6314103
  have hstable : (prefixWord ++ tailWord_6314103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314103).length < 2 ^ (prefixWord ++ tailWord_6314103).sum := by decide
  have hdescent : baseEnd_6314103 < baseStart_6314103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314149 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_6314149 : Nat := 118140960795 + 6314149 * 2 ^ 59
def prefixEnd_6314149 : Nat := 4983230072969 + 3 ^ 40 * 6314149 * 2
def baseEnd_6314149 : Nat := 3242193361105921596699263

theorem tailTrace_6314149 : CollatzResearch.WordTrace tailWord_6314149 prefixEnd_6314149 3242193361105921596699263 := by
  unfold tailWord_6314149
  simp only [CollatzResearch.WordTrace]
  refine ⟨230295933601924018640825501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153530622401282679093883667 230295933601924018640825501)
  ·
    refine ⟨86360975100721506990309563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230295933601924018640825501 86360975100721506990309563)
    ·
      refine ⟨129541462651082260485464345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86360975100721506990309563 129541462651082260485464345)
      ·
        refine ⟨97156096988311695364098259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129541462651082260485464345 97156096988311695364098259)
        ·
          refine ⟨145734145482467543046147389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97156096988311695364098259 145734145482467543046147389)
          ·
            refine ⟨54650304555925328642305271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145734145482467543046147389 54650304555925328642305271)
            ·
              refine ⟨81975456833887992963457907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54650304555925328642305271 81975456833887992963457907)
              ·
                refine ⟨122963185250831989445186861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81975456833887992963457907 122963185250831989445186861)
                ·
                  refine ⟨46111194469061996041945073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122963185250831989445186861 46111194469061996041945073)
                  ·
                    refine ⟨34583395851796497031458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46111194469061996041945073 34583395851796497031458805)
                    ·
                      refine ⟨3242193361105921596699263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34583395851796497031458805 3242193361105921596699263)
                      ·
                        rfl

theorem cell23_6314149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_6314149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314149 prefixEnd_6314149 := by exact prefixLift 6314149
  have htrace : WordTrace (prefixWord ++ tailWord_6314149) baseStart_6314149 baseEnd_6314149 := by
    simpa [prefixWord, tailWord_6314149, baseEnd_6314149] using wordTrace_append hprefix tailTrace_6314149
  have hstable : (prefixWord ++ tailWord_6314149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314149).length < 2 ^ (prefixWord ++ tailWord_6314149).sum := by decide
  have hdescent : baseEnd_6314149 < baseStart_6314149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314154 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6314154 : Nat := 118140960795 + 6314154 * 2 ^ 59
def prefixEnd_6314154 : Nat := 4983230072969 + 3 ^ 40 * 6314154 * 2
def baseEnd_6314154 : Nat := 3242195928509194077136741

theorem tailTrace_6314154 : CollatzResearch.WordTrace tailWord_6314154 prefixEnd_6314154 3242195928509194077136741 := by
  unfold tailWord_6314154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57574028991726476123689379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153530743977937269663171677 57574028991726476123689379)
  ·
    refine ⟨86361043487589714185534069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57574028991726476123689379 86361043487589714185534069)
    ·
      refine ⟨8096347826961535704893819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86361043487589714185534069 8096347826961535704893819)
      ·
        refine ⟨12144521740442303557340729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096347826961535704893819 12144521740442303557340729)
        ·
          refine ⟨9108391305331727668005547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12144521740442303557340729 9108391305331727668005547)
          ·
            refine ⟨13662586957997591502008321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108391305331727668005547 13662586957997591502008321)
            ·
              refine ⟨10246940218498193626506241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13662586957997591502008321 10246940218498193626506241)
              ·
                refine ⟨7685205163873645219879681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246940218498193626506241 7685205163873645219879681)
                ·
                  refine ⟨5763903872905233914909761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685205163873645219879681 5763903872905233914909761)
                  ·
                    refine ⟨4322927904678925436182321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763903872905233914909761 4322927904678925436182321)
                    ·
                      refine ⟨3242195928509194077136741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4322927904678925436182321 3242195928509194077136741)
                      ·
                        rfl

theorem cell23_6314154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6314154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314154 prefixEnd_6314154 := by exact prefixLift 6314154
  have htrace : WordTrace (prefixWord ++ tailWord_6314154) baseStart_6314154 baseEnd_6314154 := by
    simpa [prefixWord, tailWord_6314154, baseEnd_6314154] using wordTrace_append hprefix tailTrace_6314154
  have hstable : (prefixWord ++ tailWord_6314154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314154).length < 2 ^ (prefixWord ++ tailWord_6314154).sum := by decide
  have hdescent : baseEnd_6314154 < baseStart_6314154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314159 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_6314159 : Nat := 118140960795 + 6314159 * 2 ^ 59
def prefixEnd_6314159 : Nat := 4983230072969 + 3 ^ 40 * 6314159 * 2
def baseEnd_6314159 : Nat := 3242198495912466557574217

theorem tailTrace_6314159 : CollatzResearch.WordTrace tailWord_6314159 prefixEnd_6314159 3242198495912466557574217 := by
  unfold tailWord_6314159
  simp only [CollatzResearch.WordTrace]
  refine ⟨230296298331887790348689531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153530865554591860232459687 230296298331887790348689531)
  ·
    refine ⟨345444447497831685523034297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230296298331887790348689531 345444447497831685523034297)
    ·
      refine ⟨259083335623373764142275723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345444447497831685523034297 259083335623373764142275723)
      ·
        refine ⟨388625003435060646213413585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259083335623373764142275723 388625003435060646213413585)
        ·
          refine ⟨291468752576295484660060189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388625003435060646213413585 291468752576295484660060189)
          ·
            refine ⟨109300782216110806747522571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291468752576295484660060189 109300782216110806747522571)
            ·
              refine ⟨163951173324166210121283857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109300782216110806747522571 163951173324166210121283857)
              ·
                refine ⟨122963379993124657590962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163951173324166210121283857 122963379993124657590962893)
                ·
                  refine ⟨46111267497421746596611085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122963379993124657590962893 46111267497421746596611085)
                  ·
                    refine ⟨17291725311533154973729157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46111267497421746596611085 17291725311533154973729157)
                    ·
                      refine ⟨3242198495912466557574217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17291725311533154973729157 3242198495912466557574217)
                      ·
                        rfl

theorem cell23_6314159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_6314159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314159 prefixEnd_6314159 := by exact prefixLift 6314159
  have htrace : WordTrace (prefixWord ++ tailWord_6314159) baseStart_6314159 baseEnd_6314159 := by
    simpa [prefixWord, tailWord_6314159, baseEnd_6314159] using wordTrace_append hprefix tailTrace_6314159
  have hstable : (prefixWord ++ tailWord_6314159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314159).length < 2 ^ (prefixWord ++ tailWord_6314159).sum := by decide
  have hdescent : baseEnd_6314159 < baseStart_6314159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314199 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 8]
def baseStart_6314199 : Nat := 118140960795 + 6314199 * 2 ^ 59
def prefixEnd_6314199 : Nat := 4983230072969 + 3 ^ 40 * 6314199 * 2
def baseEnd_6314199 : Nat := 360246559459849600119337

theorem tailTrace_6314199 : CollatzResearch.WordTrace tailWord_6314199 prefixEnd_6314199 360246559459849600119337 := by
  unfold tailWord_6314199
  simp only [CollatzResearch.WordTrace]
  refine ⟨230297757251742877180145651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153531838167828584786763767 230297757251742877180145651)
  ·
    refine ⟨345446635877614315770218477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230297757251742877180145651 345446635877614315770218477)
    ·
      refine ⟨129542488454105368413831929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345446635877614315770218477 129542488454105368413831929)
      ·
        refine ⟨97156866340579026310373947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129542488454105368413831929 97156866340579026310373947)
        ·
          refine ⟨145735299510868539465560921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97156866340579026310373947 145735299510868539465560921)
          ·
            refine ⟨109301474633151404599170691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145735299510868539465560921 109301474633151404599170691)
            ·
              refine ⟨163952211949727106898756037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109301474633151404599170691 163952211949727106898756037)
              ·
                refine ⟨30741039740573832543516757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163952211949727106898756037 30741039740573832543516757)
                ·
                  refine ⟨360246559459849600119337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30741039740573832543516757 360246559459849600119337)
                  ·
                    rfl

theorem cell23_6314199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 8].length) (baseStart_6314199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314199 prefixEnd_6314199 := by exact prefixLift 6314199
  have htrace : WordTrace (prefixWord ++ tailWord_6314199) baseStart_6314199 baseEnd_6314199 := by
    simpa [prefixWord, tailWord_6314199, baseEnd_6314199] using wordTrace_append hprefix tailTrace_6314199
  have hstable : (prefixWord ++ tailWord_6314199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314199).length < 2 ^ (prefixWord ++ tailWord_6314199).sum := by decide
  have hdescent : baseEnd_6314199 < baseStart_6314199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314203 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 1, 4]
def baseStart_6314203 : Nat := 118140960795 + 6314203 * 2 ^ 59
def prefixEnd_6314203 : Nat := 4983230072969 + 3 ^ 40 * 6314203 * 2
def baseEnd_6314203 : Nat := 1080740363020421461808005

theorem tailTrace_6314203 : CollatzResearch.WordTrace tailWord_6314203 prefixEnd_6314203 1080740363020421461808005 := by
  unfold tailWord_6314203
  simp only [CollatzResearch.WordTrace]
  refine ⟨230297903143728385863291263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153531935429152257242194175 230297903143728385863291263)
  ·
    refine ⟨345446854715592578794936895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230297903143728385863291263 345446854715592578794936895)
    ·
      refine ⟨518170282073388868192405343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345446854715592578794936895 518170282073388868192405343)
      ·
        refine ⟨777255423110083302288608015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518170282073388868192405343 777255423110083302288608015)
        ·
          refine ⟨1165883134665124953432912023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777255423110083302288608015 1165883134665124953432912023)
          ·
            refine ⟨1748824701997687430149368035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165883134665124953432912023 1748824701997687430149368035)
            ·
              refine ⟨2623237052996531145224052053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748824701997687430149368035 2623237052996531145224052053)
              ·
                refine ⟨3842632401850387419761795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2623237052996531145224052053 3842632401850387419761795)
                ·
                  refine ⟨5763948602775581129642693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842632401850387419761795 5763948602775581129642693)
                  ·
                    refine ⟨1080740363020421461808005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763948602775581129642693 1080740363020421461808005)
                    ·
                      rfl

theorem cell23_6314203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 4].length) (baseStart_6314203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314203 prefixEnd_6314203 := by exact prefixLift 6314203
  have htrace : WordTrace (prefixWord ++ tailWord_6314203) baseStart_6314203 baseEnd_6314203 := by
    simpa [prefixWord, tailWord_6314203, baseEnd_6314203] using wordTrace_append hprefix tailTrace_6314203
  have hstable : (prefixWord ++ tailWord_6314203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314203).length < 2 ^ (prefixWord ++ tailWord_6314203).sum := by decide
  have hdescent : baseEnd_6314203 < baseStart_6314203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314216 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 8]
def baseStart_6314216 : Nat := 118140960795 + 6314216 * 2 ^ 59
def prefixEnd_6314216 : Nat := 4983230072969 + 3 ^ 40 * 6314216 * 2
def baseEnd_6314216 : Nat := 360247529367752537173495

theorem tailTrace_6314216 : CollatzResearch.WordTrace tailWord_6314216 prefixEnd_6314216 360247529367752537173495 := by
  unfold tailWord_6314216
  simp only [CollatzResearch.WordTrace]
  refine ⟨115149188646340644541757251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153532251528454192722343001 115149188646340644541757251)
  ·
    refine ⟨172723782969510966812635877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115149188646340644541757251 172723782969510966812635877)
    ·
      refine ⟨32385709306783306277369227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172723782969510966812635877 32385709306783306277369227)
      ·
        refine ⟨48578563960174959416053841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32385709306783306277369227 48578563960174959416053841)
        ·
          refine ⟨36433922970131219562040381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48578563960174959416053841 36433922970131219562040381)
          ·
            refine ⟨13662721113799207335765143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36433922970131219562040381 13662721113799207335765143)
            ·
              refine ⟨20494081670698811003647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13662721113799207335765143 20494081670698811003647715)
              ·
                refine ⟨30741122506048216505471573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494081670698811003647715 30741122506048216505471573)
                ·
                  refine ⟨360247529367752537173495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30741122506048216505471573 360247529367752537173495)
                  ·
                    rfl

theorem cell23_6314216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_6314216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314216 prefixEnd_6314216 := by exact prefixLift 6314216
  have htrace : WordTrace (prefixWord ++ tailWord_6314216) baseStart_6314216 baseEnd_6314216 := by
    simpa [prefixWord, tailWord_6314216, baseEnd_6314216] using wordTrace_append hprefix tailTrace_6314216
  have hstable : (prefixWord ++ tailWord_6314216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314216).length < 2 ^ (prefixWord ++ tailWord_6314216).sum := by decide
  have hdescent : baseEnd_6314216 < baseStart_6314216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314219 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_6314219 : Nat := 118140960795 + 6314219 * 2 ^ 59
def prefixEnd_6314219 : Nat := 4983230072969 + 3 ^ 40 * 6314219 * 2
def baseEnd_6314219 : Nat := 3242229304751736322823941

theorem tailTrace_6314219 : CollatzResearch.WordTrace tailWord_6314219 prefixEnd_6314219 3242229304751736322823941 := by
  unfold tailWord_6314219
  simp only [CollatzResearch.WordTrace]
  refine ⟨230298486711670420595873711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153532324474446947063915807 230298486711670420595873711)
  ·
    refine ⟨345447730067505630893810567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230298486711670420595873711 345447730067505630893810567)
    ·
      refine ⟨518171595101258446340715851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345447730067505630893810567 518171595101258446340715851)
      ·
        refine ⟨777257392651887669511073777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518171595101258446340715851 777257392651887669511073777)
        ·
          refine ⟨582943044488915752133305333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777257392651887669511073777 582943044488915752133305333)
          ·
            refine ⟨54650910420835851762497375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 582943044488915752133305333 54650910420835851762497375)
            ·
              refine ⟨81976365631253777643746063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54650910420835851762497375 81976365631253777643746063)
              ·
                refine ⟨122964548446880666465619095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81976365631253777643746063 122964548446880666465619095)
                ·
                  refine ⟨184446822670320999698428643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122964548446880666465619095 184446822670320999698428643)
                  ·
                    refine ⟨276670234005481499547642965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184446822670320999698428643 276670234005481499547642965)
                    ·
                      refine ⟨3242229304751736322823941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 276670234005481499547642965 3242229304751736322823941)
                      ·
                        rfl

theorem cell23_6314219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_6314219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314219 prefixEnd_6314219 := by exact prefixLift 6314219
  have htrace : WordTrace (prefixWord ++ tailWord_6314219) baseStart_6314219 baseEnd_6314219 := by
    simpa [prefixWord, tailWord_6314219, baseEnd_6314219] using wordTrace_append hprefix tailTrace_6314219
  have hstable : (prefixWord ++ tailWord_6314219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314219).length < 2 ^ (prefixWord ++ tailWord_6314219).sum := by decide
  have hdescent : baseEnd_6314219 < baseStart_6314219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314243 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 3]
def baseStart_6314243 : Nat := 118140960795 + 6314243 * 2 ^ 59
def prefixEnd_6314243 : Nat := 4983230072969 + 3 ^ 40 * 6314243 * 2
def baseEnd_6314243 : Nat := 3242241628287444228923831

theorem tailTrace_6314243 : CollatzResearch.WordTrace tailWord_6314243 prefixEnd_6314243 3242241628287444228923831 := by
  unfold tailWord_6314243
  simp only [CollatzResearch.WordTrace]
  refine ⟨230299362063583472694747383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153532908042388981796498255 230299362063583472694747383)
  ·
    refine ⟨345449043095375209042121075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230299362063583472694747383 345449043095375209042121075)
    ·
      refine ⟨518173564643062813563181613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345449043095375209042121075 518173564643062813563181613)
      ·
        refine ⟨194315086741148555086193105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518173564643062813563181613 194315086741148555086193105)
        ·
          refine ⟨145736315055861416314644829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194315086741148555086193105 145736315055861416314644829)
          ·
            refine ⟨54651118145948031117991811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145736315055861416314644829 54651118145948031117991811)
            ·
              refine ⟨81976677218922046676987717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54651118145948031117991811 81976677218922046676987717)
              ·
                refine ⟨15370626978547883751935197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81976677218922046676987717 15370626978547883751935197)
                ·
                  refine ⟨5763985116955456406975699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15370626978547883751935197 5763985116955456406975699)
                  ·
                    refine ⟨8645977675433184610463549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763985116955456406975699 8645977675433184610463549)
                    ·
                      refine ⟨3242241628287444228923831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8645977675433184610463549 3242241628287444228923831)
                      ·
                        rfl

theorem cell23_6314243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_6314243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314243 prefixEnd_6314243 := by exact prefixLift 6314243
  have htrace : WordTrace (prefixWord ++ tailWord_6314243) baseStart_6314243 baseEnd_6314243 := by
    simpa [prefixWord, tailWord_6314243, baseEnd_6314243] using wordTrace_append hprefix tailTrace_6314243
  have hstable : (prefixWord ++ tailWord_6314243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314243).length < 2 ^ (prefixWord ++ tailWord_6314243).sum := by decide
  have hdescent : baseEnd_6314243 < baseStart_6314243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314263 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 1, 5]
def baseStart_6314263 : Nat := 118140960795 + 6314263 * 2 ^ 59
def prefixEnd_6314263 : Nat := 4983230072969 + 3 ^ 40 * 6314263 * 2
def baseEnd_6314263 : Nat := 1080750632633511383557913

theorem tailTrace_6314263 : CollatzResearch.WordTrace tailWord_6314263 prefixEnd_6314263 1080750632633511383557913 := by
  unfold tailWord_6314263
  simp only [CollatzResearch.WordTrace]
  refine ⟨230300091523511016110475443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153533394349007344073650295 230300091523511016110475443)
  ·
    refine ⟨345450137285266524165713165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230300091523511016110475443 345450137285266524165713165)
    ·
      refine ⟨129543801481974946562142437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345450137285266524165713165 129543801481974946562142437)
      ·
        refine ⟨24289462777870302480401707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129543801481974946562142437 24289462777870302480401707)
        ·
          refine ⟨36434194166805453720602561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24289462777870302480401707 36434194166805453720602561)
          ·
            refine ⟨27325645625104090290451921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36434194166805453720602561 27325645625104090290451921)
            ·
              refine ⟨20494234218828067717838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27325645625104090290451921 20494234218828067717838941)
              ·
                refine ⟨7685337832060525394189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20494234218828067717838941 7685337832060525394189603)
                ·
                  refine ⟨11528006748090788091284405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685337832060525394189603 11528006748090788091284405)
                  ·
                    refine ⟨1080750632633511383557913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11528006748090788091284405 1080750632633511383557913)
                    ·
                      rfl

theorem cell23_6314263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_6314263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314263 prefixEnd_6314263 := by exact prefixLift 6314263
  have htrace : WordTrace (prefixWord ++ tailWord_6314263) baseStart_6314263 baseEnd_6314263 := by
    simpa [prefixWord, tailWord_6314263, baseEnd_6314263] using wordTrace_append hprefix tailTrace_6314263
  have hstable : (prefixWord ++ tailWord_6314263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314263).length < 2 ^ (prefixWord ++ tailWord_6314263).sum := by decide
  have hdescent : baseEnd_6314263 < baseStart_6314263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314277 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_6314277 : Nat := 118140960795 + 6314277 * 2 ^ 59
def prefixEnd_6314277 : Nat := 4983230072969 + 3 ^ 40 * 6314277 * 2
def baseEnd_6314277 : Nat := 3242259086629697095898675

theorem tailTrace_6314277 : CollatzResearch.WordTrace tailWord_6314277 prefixEnd_6314277 3242259086629697095898675 := by
  unfold tailWord_6314277
  simp only [CollatzResearch.WordTrace]
  refine ⟨230300602145460296501485085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153533734763640197667656723 230300602145460296501485085)
  ·
    refine ⟨86362725804547611188056907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230300602145460296501485085 86362725804547611188056907)
    ·
      refine ⟨129544088706821416782085361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86362725804547611188056907 129544088706821416782085361)
      ·
        refine ⟨97158066530116062586564021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129544088706821416782085361 97158066530116062586564021)
        ·
          refine ⟨9108568737198380867490377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97158066530116062586564021 9108568737198380867490377)
          ·
            refine ⟨6831426552898785650617783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9108568737198380867490377 6831426552898785650617783)
            ·
              refine ⟨10247139829348178475926675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831426552898785650617783 10247139829348178475926675)
              ·
                refine ⟨15370709744022267713890013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247139829348178475926675 15370709744022267713890013)
                ·
                  refine ⟨5764016154008350392708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15370709744022267713890013 5764016154008350392708755)
                  ·
                    refine ⟨8646024231012525589063133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764016154008350392708755 8646024231012525589063133)
                    ·
                      refine ⟨3242259086629697095898675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646024231012525589063133 3242259086629697095898675)
                      ·
                        rfl

theorem cell23_6314277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_6314277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314277 prefixEnd_6314277 := by exact prefixLift 6314277
  have htrace : WordTrace (prefixWord ++ tailWord_6314277) baseStart_6314277 baseEnd_6314277 := by
    simpa [prefixWord, tailWord_6314277, baseEnd_6314277] using wordTrace_append hprefix tailTrace_6314277
  have hstable : (prefixWord ++ tailWord_6314277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314277).length < 2 ^ (prefixWord ++ tailWord_6314277).sum := by decide
  have hdescent : baseEnd_6314277 < baseStart_6314277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314296 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_6314296 : Nat := 118140960795 + 6314296 * 2 ^ 59
def prefixEnd_6314296 : Nat := 4983230072969 + 3 ^ 40 * 6314296 * 2
def baseEnd_6314296 : Nat := 3242268842762132521561087

theorem tailTrace_6314296 : CollatzResearch.WordTrace tailWord_6314296 prefixEnd_6314296 3242268842762132521561087 := by
  unfold tailWord_6314296
  simp only [CollatzResearch.WordTrace]
  refine ⟨115150647566195731373213371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153534196754927641830951161 115150647566195731373213371)
  ·
    refine ⟨172725971349293597059820057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115150647566195731373213371 172725971349293597059820057)
    ·
      refine ⟨129544478511970197794865043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172725971349293597059820057 129544478511970197794865043)
      ·
        refine ⟨194316717767955296692297565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129544478511970197794865043 194316717767955296692297565)
        ·
          refine ⟨72868769162983236259611587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194316717767955296692297565 72868769162983236259611587)
          ·
            refine ⟨109303153744474854389417381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72868769162983236259611587 109303153744474854389417381)
            ·
              refine ⟨20494341327089035198015759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109303153744474854389417381 20494341327089035198015759)
              ·
                refine ⟨30741511990633552797023639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494341327089035198015759 30741511990633552797023639)
                ·
                  refine ⟨46112267985950329195535459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30741511990633552797023639 46112267985950329195535459)
                  ·
                    refine ⟨69168401978925493793303189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46112267985950329195535459 69168401978925493793303189)
                    ·
                      refine ⟨3242268842762132521561087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69168401978925493793303189 3242268842762132521561087)
                      ·
                        rfl

theorem cell23_6314296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_6314296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314296 prefixEnd_6314296 := by exact prefixLift 6314296
  have htrace : WordTrace (prefixWord ++ tailWord_6314296) baseStart_6314296 baseEnd_6314296 := by
    simpa [prefixWord, tailWord_6314296, baseEnd_6314296] using wordTrace_append hprefix tailTrace_6314296
  have hstable : (prefixWord ++ tailWord_6314296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314296).length < 2 ^ (prefixWord ++ tailWord_6314296).sum := by decide
  have hdescent : baseEnd_6314296 < baseStart_6314296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314300 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_6314300 : Nat := 118140960795 + 6314300 * 2 ^ 59
def prefixEnd_6314300 : Nat := 4983230072969 + 3 ^ 40 * 6314300 * 2
def baseEnd_6314300 : Nat := 3242270896684750505911069

theorem tailTrace_6314300 : CollatzResearch.WordTrace tailWord_6314300 prefixEnd_6314300 3242270896684750505911069 := by
  unfold tailWord_6314300
  simp only [CollatzResearch.WordTrace]
  refine ⟨115150720512188485714786177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153534294016251314286381569 115150720512188485714786177)
  ·
    refine ⟨86363040384141364286089633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115150720512188485714786177 86363040384141364286089633)
    ·
      refine ⟨64772280288106023214567225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86363040384141364286089633 64772280288106023214567225)
      ·
        refine ⟨48579210216079517410925419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64772280288106023214567225 48579210216079517410925419)
        ·
          refine ⟨72868815324119276116388129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48579210216079517410925419 72868815324119276116388129)
          ·
            refine ⟨54651611493089457087291097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72868815324119276116388129 54651611493089457087291097)
            ·
              refine ⟨40988708619817092815468323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54651611493089457087291097 40988708619817092815468323)
              ·
                refine ⟨61483062929725639223202485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40988708619817092815468323 61483062929725639223202485)
                ·
                  refine ⟨5764037149661778677175233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61483062929725639223202485 5764037149661778677175233)
                  ·
                    refine ⟨4323027862246334007881425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764037149661778677175233 4323027862246334007881425)
                    ·
                      refine ⟨3242270896684750505911069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323027862246334007881425 3242270896684750505911069)
                      ·
                        rfl

theorem cell23_6314300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_6314300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314300 prefixEnd_6314300 := by exact prefixLift 6314300
  have htrace : WordTrace (prefixWord ++ tailWord_6314300) baseStart_6314300 baseEnd_6314300 := by
    simpa [prefixWord, tailWord_6314300, baseEnd_6314300] using wordTrace_append hprefix tailTrace_6314300
  have hstable : (prefixWord ++ tailWord_6314300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314300).length < 2 ^ (prefixWord ++ tailWord_6314300).sum := by decide
  have hdescent : baseEnd_6314300 < baseStart_6314300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314303 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_6314303 : Nat := 118140960795 + 6314303 * 2 ^ 59
def prefixEnd_6314303 : Nat := 4983230072969 + 3 ^ 40 * 6314303 * 2
def baseEnd_6314303 : Nat := 3242272437126713994173555

theorem tailTrace_6314303 : CollatzResearch.WordTrace tailWord_6314303 prefixEnd_6314303 3242272437126713994173555 := by
  unfold tailWord_6314303
  simp only [CollatzResearch.WordTrace]
  refine ⟨230301550443366102941931563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153534366962244068627954375 230301550443366102941931563)
  ·
    refine ⟨345452325665049154412897345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230301550443366102941931563 345452325665049154412897345)
    ·
      refine ⟨259089244248786865809673009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345452325665049154412897345 259089244248786865809673009)
      ·
        refine ⟨194316933186590149357254757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259089244248786865809673009 194316933186590149357254757)
        ·
          refine ⟨36434424972485653004485267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194316933186590149357254757 36434424972485653004485267)
          ·
            refine ⟨54651637458728479506727901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36434424972485653004485267 54651637458728479506727901)
            ·
              refine ⟨20494364047023179815022963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54651637458728479506727901 20494364047023179815022963)
              ·
                refine ⟨30741546070534769722534445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494364047023179815022963 30741546070534769722534445)
                ·
                  refine ⟨11528079776450538645950417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30741546070534769722534445 11528079776450538645950417)
                  ·
                    refine ⟨8646059832337903984462813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11528079776450538645950417 8646059832337903984462813)
                    ·
                      refine ⟨3242272437126713994173555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646059832337903984462813 3242272437126713994173555)
                      ·
                        rfl

theorem cell23_6314303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_6314303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314303 prefixEnd_6314303 := by exact prefixLift 6314303
  have htrace : WordTrace (prefixWord ++ tailWord_6314303) baseStart_6314303 baseEnd_6314303 := by
    simpa [prefixWord, tailWord_6314303, baseEnd_6314303] using wordTrace_append hprefix tailTrace_6314303
  have hstable : (prefixWord ++ tailWord_6314303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314303).length < 2 ^ (prefixWord ++ tailWord_6314303).sum := by decide
  have hdescent : baseEnd_6314303 < baseStart_6314303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314377 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 1, 3, 2]
def baseStart_6314377 : Nat := 118140960795 + 6314377 * 2 ^ 59
def prefixEnd_6314377 : Nat := 4983230072969 + 3 ^ 40 * 6314377 * 2
def baseEnd_6314377 : Nat := 3242310434695146704648215

theorem tailTrace_6314377 : CollatzResearch.WordTrace tailWord_6314377 prefixEnd_6314377 3242310434695146704648215 := by
  unfold tailWord_6314377
  simp only [CollatzResearch.WordTrace]
  refine ⟨230304249445098013580125385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153536166296732009053416923 230304249445098013580125385)
  ·
    refine ⟨172728187083823510185094039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230304249445098013580125385 172728187083823510185094039)
    ·
      refine ⟨259092280625735265277641059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172728187083823510185094039 259092280625735265277641059)
      ·
        refine ⟨388638420938602897916461589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259092280625735265277641059 388638420938602897916461589)
        ·
          refine ⟨18217425981497010839834137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 388638420938602897916461589 18217425981497010839834137)
          ·
            refine ⟨13663069486122758129875603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18217425981497010839834137 13663069486122758129875603)
            ·
              refine ⟨20494604229184137194813405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663069486122758129875603 20494604229184137194813405)
              ·
                refine ⟨7685476585944051448055027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20494604229184137194813405 7685476585944051448055027)
                ·
                  refine ⟨11528214878916077172082541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685476585944051448055027 11528214878916077172082541)
                  ·
                    refine ⟨4323080579593528939530953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11528214878916077172082541 4323080579593528939530953)
                    ·
                      refine ⟨3242310434695146704648215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323080579593528939530953 3242310434695146704648215)
                      ·
                        rfl

theorem cell23_6314377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3, 2].length) (baseStart_6314377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314377 prefixEnd_6314377 := by exact prefixLift 6314377
  have htrace : WordTrace (prefixWord ++ tailWord_6314377) baseStart_6314377 baseEnd_6314377 := by
    simpa [prefixWord, tailWord_6314377, baseEnd_6314377] using wordTrace_append hprefix tailTrace_6314377
  have hstable : (prefixWord ++ tailWord_6314377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314377).length < 2 ^ (prefixWord ++ tailWord_6314377).sum := by decide
  have hdescent : baseEnd_6314377 < baseStart_6314377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314401 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6314401 : Nat := 118140960795 + 6314401 * 2 ^ 59
def prefixEnd_6314401 : Nat := 4983230072969 + 3 ^ 40 * 6314401 * 2
def baseEnd_6314401 : Nat := 3242322758230854610748105

theorem tailTrace_6314401 : CollatzResearch.WordTrace tailWord_6314401 prefixEnd_6314401 3242322758230854610748105 := by
  unfold tailWord_6314401
  simp only [CollatzResearch.WordTrace]
  refine ⟨230305124797011065678999057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153536749864674043785999371 230305124797011065678999057)
  ·
    refine ⟨172728843597758299259249293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230305124797011065678999057 172728843597758299259249293)
    ·
      refine ⟨64773316349159362222218485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172728843597758299259249293 64773316349159362222218485)
      ·
        refine ⟨6072498407733690208332983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64773316349159362222218485 6072498407733690208332983)
        ·
          refine ⟨9108747611600535312499475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072498407733690208332983 9108747611600535312499475)
          ·
            refine ⟨13663121417400802968749213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108747611600535312499475 13663121417400802968749213)
            ·
              refine ⟨5123670531525301113280955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13663121417400802968749213 5123670531525301113280955)
              ·
                refine ⟨7685505797287951669921433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123670531525301113280955 7685505797287951669921433)
                ·
                  refine ⟨5764129347965963752441075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685505797287951669921433 5764129347965963752441075)
                  ·
                    refine ⟨8646194021948945628661613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764129347965963752441075 8646194021948945628661613)
                    ·
                      refine ⟨3242322758230854610748105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646194021948945628661613 3242322758230854610748105)
                      ·
                        rfl

theorem cell23_6314401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6314401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314401 prefixEnd_6314401 := by exact prefixLift 6314401
  have htrace : WordTrace (prefixWord ++ tailWord_6314401) baseStart_6314401 baseEnd_6314401 := by
    simpa [prefixWord, tailWord_6314401, baseEnd_6314401] using wordTrace_append hprefix tailTrace_6314401
  have hstable : (prefixWord ++ tailWord_6314401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314401).length < 2 ^ (prefixWord ++ tailWord_6314401).sum := by decide
  have hdescent : baseEnd_6314401 < baseStart_6314401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314403 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_6314403 : Nat := 118140960795 + 6314403 * 2 ^ 59
def prefixEnd_6314403 : Nat := 4983230072969 + 3 ^ 40 * 6314403 * 2
def baseEnd_6314403 : Nat := 3242323785192163602923095

theorem tailTrace_6314403 : CollatzResearch.WordTrace tailWord_6314403 prefixEnd_6314403 3242323785192163602923095 := by
  unfold tailWord_6314403
  simp only [CollatzResearch.WordTrace]
  refine ⟨230305197743003820020571863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153536798495335880013714575 230305197743003820020571863)
  ·
    refine ⟨345457796614505730030857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230305197743003820020571863 345457796614505730030857795)
    ·
      refine ⟨518186694921758595046286693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345457796614505730030857795 518186694921758595046286693)
      ·
        refine ⟨97160005297829736571178755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518186694921758595046286693 97160005297829736571178755)
        ·
          refine ⟨145740007946744604856768133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97160005297829736571178755 145740007946744604856768133)
          ·
            refine ⟨27326251490014613410644025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145740007946744604856768133 27326251490014613410644025)
            ·
              refine ⟨20494688617510960057983019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27326251490014613410644025 20494688617510960057983019)
              ·
                refine ⟨30742032926266440086974529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494688617510960057983019 30742032926266440086974529)
                ·
                  refine ⟨23056524694699830065230897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30742032926266440086974529 23056524694699830065230897)
                  ·
                    refine ⟨17292393521024872548923173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23056524694699830065230897 17292393521024872548923173)
                    ·
                      refine ⟨3242323785192163602923095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17292393521024872548923173 3242323785192163602923095)
                      ·
                        rfl

theorem cell23_6314403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_6314403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314403 prefixEnd_6314403 := by exact prefixLift 6314403
  have htrace : WordTrace (prefixWord ++ tailWord_6314403) baseStart_6314403 baseEnd_6314403 := by
    simpa [prefixWord, tailWord_6314403, baseEnd_6314403] using wordTrace_append hprefix tailTrace_6314403
  have hstable : (prefixWord ++ tailWord_6314403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314403).length < 2 ^ (prefixWord ++ tailWord_6314403).sum := by decide
  have hdescent : baseEnd_6314403 < baseStart_6314403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314407 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6314407 : Nat := 118140960795 + 6314407 * 2 ^ 59
def prefixEnd_6314407 : Nat := 4983230072969 + 3 ^ 40 * 6314407 * 2
def baseEnd_6314407 : Nat := 3242325839114781587273077

theorem tailTrace_6314407 : CollatzResearch.WordTrace tailWord_6314407 prefixEnd_6314407 3242325839114781587273077 := by
  unfold tailWord_6314407
  simp only [CollatzResearch.WordTrace]
  refine ⟨230305343634989328703717475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153536895756659552469144983 230305343634989328703717475)
  ·
    refine ⟨345458015452483993055576213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230305343634989328703717475 345458015452483993055576213)
    ·
      refine ⟨16193344474335187174480135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 345458015452483993055576213 16193344474335187174480135)
      ·
        refine ⟨24290016711502780761720203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193344474335187174480135 24290016711502780761720203)
        ·
          refine ⟨36435025067254171142580305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24290016711502780761720203 36435025067254171142580305)
          ·
            refine ⟨27326268800440628356935229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36435025067254171142580305 27326268800440628356935229)
            ·
              refine ⟨10247350800165235633850711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27326268800440628356935229 10247350800165235633850711)
              ·
                refine ⟨15371026200247853450776067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247350800165235633850711 15371026200247853450776067)
                ·
                  refine ⟨23056539300371780176164101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15371026200247853450776067 23056539300371780176164101)
                  ·
                    refine ⟨4323101118819708783030769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23056539300371780176164101 4323101118819708783030769)
                    ·
                      refine ⟨3242325839114781587273077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323101118819708783030769 3242325839114781587273077)
                      ·
                        rfl

theorem cell23_6314407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6314407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314407 prefixEnd_6314407 := by exact prefixLift 6314407
  have htrace : WordTrace (prefixWord ++ tailWord_6314407) baseStart_6314407 baseEnd_6314407 := by
    simpa [prefixWord, tailWord_6314407, baseEnd_6314407] using wordTrace_append hprefix tailTrace_6314407
  have hstable : (prefixWord ++ tailWord_6314407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314407).length < 2 ^ (prefixWord ++ tailWord_6314407).sum := by decide
  have hdescent : baseEnd_6314407 < baseStart_6314407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314416 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_6314416 : Nat := 118140960795 + 6314416 * 2 ^ 59
def prefixEnd_6314416 : Nat := 4983230072969 + 3 ^ 40 * 6314416 * 2
def baseEnd_6314416 : Nat := 3242330460440672052060535

theorem tailTrace_6314416 : CollatzResearch.WordTrace tailWord_6314416 prefixEnd_6314416 3242330460440672052060535 := by
  unfold tailWord_6314416
  simp only [CollatzResearch.WordTrace]
  refine ⟨115152835945978361620397551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153537114594637815493863401 115152835945978361620397551)
  ·
    refine ⟨172729253918967542430596327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115152835945978361620397551 172729253918967542430596327)
    ·
      refine ⟨259093880878451313645894491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172729253918967542430596327 259093880878451313645894491)
      ·
        refine ⟨388640821317676970468841737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259093880878451313645894491 388640821317676970468841737)
        ·
          refine ⟨291480615988257727851631303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388640821317676970468841737 291480615988257727851631303)
          ·
            refine ⟨437220923982386591777446955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291480615988257727851631303 437220923982386591777446955)
            ·
              refine ⟨655831385973579887666170433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437220923982386591777446955 655831385973579887666170433)
              ·
                refine ⟨491873539480184915749627825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655831385973579887666170433 491873539480184915749627825)
                ·
                  refine ⟨368905154610138686812220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491873539480184915749627825 368905154610138686812220869)
                  ·
                    refine ⟨69169716489401003777291413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368905154610138686812220869 69169716489401003777291413)
                    ·
                      refine ⟨3242330460440672052060535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69169716489401003777291413 3242330460440672052060535)
                      ·
                        rfl

theorem cell23_6314416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_6314416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314416 prefixEnd_6314416 := by exact prefixLift 6314416
  have htrace : WordTrace (prefixWord ++ tailWord_6314416) baseStart_6314416 baseEnd_6314416 := by
    simpa [prefixWord, tailWord_6314416, baseEnd_6314416] using wordTrace_append hprefix tailTrace_6314416
  have hstable : (prefixWord ++ tailWord_6314416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314416).length < 2 ^ (prefixWord ++ tailWord_6314416).sum := by decide
  have hdescent : baseEnd_6314416 < baseStart_6314416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314453 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6314453 : Nat := 118140960795 + 6314453 * 2 ^ 59
def prefixEnd_6314453 : Nat := 4983230072969 + 3 ^ 40 * 6314453 * 2
def baseEnd_6314453 : Nat := 3242349459224888407297865

theorem tailTrace_6314453 : CollatzResearch.WordTrace tailWord_6314453 prefixEnd_6314453 3242349459224888407297865 := by
  unfold tailWord_6314453
  simp only [CollatzResearch.WordTrace]
  refine ⟨230307021392822678559892013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153538014261881785706594675 230307021392822678559892013)
  ·
    refine ⟨86365133022308504459959505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230307021392822678559892013 86365133022308504459959505)
    ·
      refine ⟨64773849766731378344969629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86365133022308504459959505 64773849766731378344969629)
      ·
        refine ⟨24290193662524266879363611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64773849766731378344969629 24290193662524266879363611)
        ·
          refine ⟨36435290493786400319045417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24290193662524266879363611 36435290493786400319045417)
          ·
            refine ⟨27326467870339800239284063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36435290493786400319045417 27326467870339800239284063)
            ·
              refine ⟨40989701805509700358926095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27326467870339800239284063 40989701805509700358926095)
              ·
                refine ⟨61484552708264550538389143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40989701805509700358926095 61484552708264550538389143)
                ·
                  refine ⟨92226829062396825807583715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61484552708264550538389143 92226829062396825807583715)
                  ·
                    refine ⟨138340243593595238711375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92226829062396825807583715 138340243593595238711375573)
                    ·
                      refine ⟨3242349459224888407297865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138340243593595238711375573 3242349459224888407297865)
                      ·
                        rfl

theorem cell23_6314453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6314453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314453 prefixEnd_6314453 := by exact prefixLift 6314453
  have htrace : WordTrace (prefixWord ++ tailWord_6314453) baseStart_6314453 baseEnd_6314453 := by
    simpa [prefixWord, tailWord_6314453, baseEnd_6314453] using wordTrace_append hprefix tailTrace_6314453
  have hstable : (prefixWord ++ tailWord_6314453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314453).length < 2 ^ (prefixWord ++ tailWord_6314453).sum := by decide
  have hdescent : baseEnd_6314453 < baseStart_6314453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314477 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_6314477 : Nat := 118140960795 + 6314477 * 2 ^ 59
def prefixEnd_6314477 : Nat := 4983230072969 + 3 ^ 40 * 6314477 * 2
def baseEnd_6314477 : Nat := 1080787260920198771132585

theorem tailTrace_6314477 : CollatzResearch.WordTrace tailWord_6314477 prefixEnd_6314477 1080787260920198771132585 := by
  unfold tailWord_6314477
  simp only [CollatzResearch.WordTrace]
  refine ⟨230307896744735730658765685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153538597829823820439177123 230307896744735730658765685)
  ·
    refine ⟨21591365319818974749259283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230307896744735730658765685 21591365319818974749259283)
    ·
      refine ⟨32387047979728462123888925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21591365319818974749259283 32387047979728462123888925)
      ·
        refine ⟨12145142992398173296458347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32387047979728462123888925 12145142992398173296458347)
        ·
          refine ⟨18217714488597259944687521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12145142992398173296458347 18217714488597259944687521)
          ·
            refine ⟨13663285866447944958515641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18217714488597259944687521 13663285866447944958515641)
            ·
              refine ⟨10247464399835958718886731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13663285866447944958515641 10247464399835958718886731)
              ·
                refine ⟨15371196599753938078330097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247464399835958718886731 15371196599753938078330097)
                ·
                  refine ⟨11528397449815453558747573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371196599753938078330097 11528397449815453558747573)
                  ·
                    refine ⟨1080787260920198771132585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11528397449815453558747573 1080787260920198771132585)
                    ·
                      rfl

theorem cell23_6314477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_6314477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314477 prefixEnd_6314477 := by exact prefixLift 6314477
  have htrace : WordTrace (prefixWord ++ tailWord_6314477) baseStart_6314477 baseEnd_6314477 := by
    simpa [prefixWord, tailWord_6314477, baseEnd_6314477] using wordTrace_append hprefix tailTrace_6314477
  have hstable : (prefixWord ++ tailWord_6314477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314477).length < 2 ^ (prefixWord ++ tailWord_6314477).sum := by decide
  have hdescent : baseEnd_6314477 < baseStart_6314477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314480 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_6314480 : Nat := 118140960795 + 6314480 * 2 ^ 59
def prefixEnd_6314480 : Nat := 4983230072969 + 3 ^ 40 * 6314480 * 2
def baseEnd_6314480 : Nat := 3242363323202559801660241

theorem tailTrace_6314480 : CollatzResearch.WordTrace tailWord_6314480 prefixEnd_6314480 3242363323202559801660241 := by
  unfold tailWord_6314480
  simp only [CollatzResearch.WordTrace]
  refine ⟨115154003081862431085562447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153538670775816574780749929 115154003081862431085562447)
  ·
    refine ⟨172731004622793646628343671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115154003081862431085562447 172731004622793646628343671)
    ·
      refine ⟨259096506934190469942515507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172731004622793646628343671 259096506934190469942515507)
      ·
        refine ⟨388644760401285704913773261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259096506934190469942515507 388644760401285704913773261)
        ·
          refine ⟨145741785150482139342664973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388644760401285704913773261 145741785150482139342664973)
          ·
            refine ⟨54653169431430802253499365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145741785150482139342664973 54653169431430802253499365)
            ·
              refine ⟨10247469268393275422531131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54653169431430802253499365 10247469268393275422531131)
              ·
                refine ⟨15371203902589913133796697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247469268393275422531131 15371203902589913133796697)
                ·
                  refine ⟨11528402926942434850347523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371203902589913133796697 11528402926942434850347523)
                  ·
                    refine ⟨17292604390413652275521285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11528402926942434850347523 17292604390413652275521285)
                    ·
                      refine ⟨3242363323202559801660241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17292604390413652275521285 3242363323202559801660241)
                      ·
                        rfl

theorem cell23_6314480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_6314480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314480 prefixEnd_6314480 := by exact prefixLift 6314480
  have htrace : WordTrace (prefixWord ++ tailWord_6314480) baseStart_6314480 baseEnd_6314480 := by
    simpa [prefixWord, tailWord_6314480, baseEnd_6314480] using wordTrace_append hprefix tailTrace_6314480
  have hstable : (prefixWord ++ tailWord_6314480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314480).length < 2 ^ (prefixWord ++ tailWord_6314480).sum := by decide
  have hdescent : baseEnd_6314480 < baseStart_6314480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314493 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_6314493 : Nat := 118140960795 + 6314493 * 2 ^ 59
def prefixEnd_6314493 : Nat := 4983230072969 + 3 ^ 40 * 6314493 * 2
def baseEnd_6314493 : Nat := 3242369998451068250797681

theorem tailTrace_6314493 : CollatzResearch.WordTrace tailWord_6314493 prefixEnd_6314493 3242369998451068250797681 := by
  unfold tailWord_6314493
  simp only [CollatzResearch.WordTrace]
  refine ⟨230308480312677765391348133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153538986875118510260898755 230308480312677765391348133)
  ·
    refine ⟨43182840058627081010877775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230308480312677765391348133 43182840058627081010877775)
    ·
      refine ⟨64774260087940621516316663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43182840058627081010877775 64774260087940621516316663)
      ·
        refine ⟨97161390131910932274474995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64774260087940621516316663 97161390131910932274474995)
        ·
          refine ⟨145742085197866398411712493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97161390131910932274474995 145742085197866398411712493)
          ·
            refine ⟨54653281949199899404392185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145742085197866398411712493 54653281949199899404392185)
            ·
              refine ⟨40989961461899924553294139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54653281949199899404392185 40989961461899924553294139)
              ·
                refine ⟨61484942192849886829941209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40989961461899924553294139 61484942192849886829941209)
                ·
                  refine ⟨46113706644637415122455907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61484942192849886829941209 46113706644637415122455907)
                  ·
                    refine ⟨69170559966956122683683861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46113706644637415122455907 69170559966956122683683861)
                    ·
                      refine ⟨3242369998451068250797681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69170559966956122683683861 3242369998451068250797681)
                      ·
                        rfl

theorem cell23_6314493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_6314493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314493 prefixEnd_6314493 := by exact prefixLift 6314493
  have htrace : WordTrace (prefixWord ++ tailWord_6314493) baseStart_6314493 baseEnd_6314493 := by
    simpa [prefixWord, tailWord_6314493, baseEnd_6314493] using wordTrace_append hprefix tailTrace_6314493
  have hstable : (prefixWord ++ tailWord_6314493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314493).length < 2 ^ (prefixWord ++ tailWord_6314493).sum := by decide
  have hdescent : baseEnd_6314493 < baseStart_6314493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314498 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6314498 : Nat := 118140960795 + 6314498 * 2 ^ 59
def prefixEnd_6314498 : Nat := 4983230072969 + 3 ^ 40 * 6314498 * 2
def baseEnd_6314498 : Nat := 360263618428260081248351

theorem tailTrace_6314498 : CollatzResearch.WordTrace tailWord_6314498 prefixEnd_6314498 360263618428260081248351 := by
  unfold tailWord_6314498
  simp only [CollatzResearch.WordTrace]
  refine ⟨57577165669414912811320037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153539108451773100830186765 57577165669414912811320037)
  ·
    refine ⟨10795718563015296152122507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57577165669414912811320037 10795718563015296152122507)
    ·
      refine ⟨16193577844522944228183761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795718563015296152122507 16193577844522944228183761)
      ·
        refine ⟨12145183383392208171137821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16193577844522944228183761 12145183383392208171137821)
        ·
          refine ⟨4554443768772078064176683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12145183383392208171137821 4554443768772078064176683)
          ·
            refine ⟨6831665653158117096265025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554443768772078064176683 6831665653158117096265025)
            ·
              refine ⟨5123749239868587822198769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831665653158117096265025 5123749239868587822198769)
              ·
                refine ⟨3842811929901440866649077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123749239868587822198769 3842811929901440866649077)
                ·
                  refine ⟨360263618428260081248351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842811929901440866649077 360263618428260081248351)
                  ·
                    rfl

theorem cell23_6314498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6314498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314498 prefixEnd_6314498 := by exact prefixLift 6314498
  have htrace : WordTrace (prefixWord ++ tailWord_6314498) baseStart_6314498 baseEnd_6314498 := by
    simpa [prefixWord, tailWord_6314498, baseEnd_6314498] using wordTrace_append hprefix tailTrace_6314498
  have hstable : (prefixWord ++ tailWord_6314498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314498).length < 2 ^ (prefixWord ++ tailWord_6314498).sum := by decide
  have hdescent : baseEnd_6314498 < baseStart_6314498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314520 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 6]
def baseStart_6314520 : Nat := 118140960795 + 6314520 * 2 ^ 59
def prefixEnd_6314520 : Nat := 4983230072969 + 3 ^ 40 * 6314520 * 2
def baseEnd_6314520 : Nat := 360264873603193293906673

theorem tailTrace_6314520 : CollatzResearch.WordTrace tailWord_6314520 prefixEnd_6314520 360264873603193293906673 := by
  unfold tailWord_6314520
  simp only [CollatzResearch.WordTrace]
  refine ⟨115154732541789974501290507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153539643389053299335054009 115154732541789974501290507)
  ·
    refine ⟨172732098812684961751935761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115154732541789974501290507 172732098812684961751935761)
    ·
      refine ⟨129549074109513721313951821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172732098812684961751935761 129549074109513721313951821)
      ·
        refine ⟨48580902791067645492731933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129549074109513721313951821 48580902791067645492731933)
        ·
          refine ⟨18217838546650367059774475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48580902791067645492731933 18217838546650367059774475)
          ·
            refine ⟨27326757819975550589661713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18217838546650367059774475 27326757819975550589661713)
            ·
              refine ⟨20495068364981662942246285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27326757819975550589661713 20495068364981662942246285)
              ·
                refine ⟨7685650636868123603342357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20495068364981662942246285 7685650636868123603342357)
                ·
                  refine ⟨360264873603193293906673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7685650636868123603342357 360264873603193293906673)
                  ·
                    rfl

theorem cell23_6314520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_6314520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314520 prefixEnd_6314520 := by exact prefixLift 6314520
  have htrace : WordTrace (prefixWord ++ tailWord_6314520) baseStart_6314520 baseEnd_6314520 := by
    simpa [prefixWord, tailWord_6314520, baseEnd_6314520] using wordTrace_append hprefix tailTrace_6314520
  have hstable : (prefixWord ++ tailWord_6314520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314520).length < 2 ^ (prefixWord ++ tailWord_6314520).sum := by decide
  have hdescent : baseEnd_6314520 < baseStart_6314520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314563 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 6]
def baseStart_6314563 : Nat := 118140960795 + 6314563 * 2 ^ 59
def prefixEnd_6314563 : Nat := 4983230072969 + 3 ^ 40 * 6314563 * 2
def baseEnd_6314563 : Nat := 1080801980698960992307453

theorem tailTrace_6314563 : CollatzResearch.WordTrace tailWord_6314563 prefixEnd_6314563 1080801980698960992307453 := by
  unfold tailWord_6314563
  simp only [CollatzResearch.WordTrace]
  refine ⟨230311033422424167346396343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153540688948282778230930895 230311033422424167346396343)
  ·
    refine ⟨345466550133636251019594515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230311033422424167346396343 345466550133636251019594515)
    ·
      refine ⟨518199825200454376529391773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345466550133636251019594515 518199825200454376529391773)
      ·
        refine ⟨194324934450170391198521915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518199825200454376529391773 194324934450170391198521915)
        ·
          refine ⟨291487401675255586797782873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194324934450170391198521915 291487401675255586797782873)
          ·
            refine ⟨218615551256441690098337155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291487401675255586797782873 218615551256441690098337155)
            ·
              refine ⟨327923326884662535147505733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218615551256441690098337155 327923326884662535147505733)
              ·
                refine ⟨61485623790874225340157325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327923326884662535147505733 61485623790874225340157325)
                ·
                  refine ⟨23057108921577834502558997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61485623790874225340157325 23057108921577834502558997)
                  ·
                    refine ⟨1080801980698960992307453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23057108921577834502558997 1080801980698960992307453)
                    ·
                      rfl

theorem cell23_6314563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_6314563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314563 prefixEnd_6314563 := by exact prefixLift 6314563
  have htrace : WordTrace (prefixWord ++ tailWord_6314563) baseStart_6314563 baseEnd_6314563 := by
    simpa [prefixWord, tailWord_6314563, baseEnd_6314563] using wordTrace_append hprefix tailTrace_6314563
  have hstable : (prefixWord ++ tailWord_6314563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314563).length < 2 ^ (prefixWord ++ tailWord_6314563).sum := by decide
  have hdescent : baseEnd_6314563 < baseStart_6314563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314607 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_6314607 : Nat := 118140960795 + 6314607 * 2 ^ 59
def prefixEnd_6314607 : Nat := 4983230072969 + 3 ^ 40 * 6314607 * 2
def baseEnd_6314607 : Nat := 3242428535245680804772157

theorem tailTrace_6314607 : CollatzResearch.WordTrace tailWord_6314607 prefixEnd_6314607 3242428535245680804772157 := by
  unfold tailWord_6314607
  simp only [CollatzResearch.WordTrace]
  refine ⟨230312638234264762860998075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153541758822843175240665383 230312638234264762860998075)
  ·
    refine ⟨345468957351397144291497113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230312638234264762860998075 345468957351397144291497113)
    ·
      refine ⟨259101718013547858218622835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345468957351397144291497113 259101718013547858218622835)
      ·
        refine ⟨388652577020321787327934253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259101718013547858218622835 388652577020321787327934253)
        ·
          refine ⟨145744716382620670247975345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388652577020321787327934253 145744716382620670247975345)
          ·
            refine ⟨109308537286965502685981509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145744716382620670247975345 109308537286965502685981509)
            ·
              refine ⟨20495350741306031753621533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109308537286965502685981509 20495350741306031753621533)
              ·
                refine ⟨7685756527989761907608075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20495350741306031753621533 7685756527989761907608075)
                ·
                  refine ⟨11528634791984642861412113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685756527989761907608075 11528634791984642861412113)
                  ·
                    refine ⟨8646476093988482146059085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11528634791984642861412113 8646476093988482146059085)
                    ·
                      refine ⟨3242428535245680804772157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646476093988482146059085 3242428535245680804772157)
                      ·
                        rfl

theorem cell23_6314607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_6314607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314607 prefixEnd_6314607 := by exact prefixLift 6314607
  have htrace : WordTrace (prefixWord ++ tailWord_6314607) baseStart_6314607 baseEnd_6314607 := by
    simpa [prefixWord, tailWord_6314607, baseEnd_6314607] using wordTrace_append hprefix tailTrace_6314607
  have hstable : (prefixWord ++ tailWord_6314607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314607).length < 2 ^ (prefixWord ++ tailWord_6314607).sum := by decide
  have hdescent : baseEnd_6314607 < baseStart_6314607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314654 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6314654 : Nat := 118140960795 + 6314654 * 2 ^ 59
def prefixEnd_6314654 : Nat := 4983230072969 + 3 ^ 40 * 6314654 * 2
def baseEnd_6314654 : Nat := 3242452668836442120884441

theorem tailTrace_6314654 : CollatzResearch.WordTrace tailWord_6314654 prefixEnd_6314654 3242452668836442120884441 := by
  unfold tailWord_6314654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28789294058136811235994877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153542901643396326591972677 28789294058136811235994877)
  ·
    refine ⟨10795985271801304213498079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28789294058136811235994877 10795985271801304213498079)
    ·
      refine ⟨16193977907701956320247119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795985271801304213498079 16193977907701956320247119)
      ·
        refine ⟨24290966861552934480370679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193977907701956320247119 24290966861552934480370679)
        ·
          refine ⟨36436450292329401720556019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24290966861552934480370679 36436450292329401720556019)
          ·
            refine ⟨54654675438494102580834029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36436450292329401720556019 54654675438494102580834029)
            ·
              refine ⟨20495503289435288467812761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54654675438494102580834029 20495503289435288467812761)
              ·
                refine ⟨15371627467076466350859571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20495503289435288467812761 15371627467076466350859571)
                ·
                  refine ⟨23057441200614699526289357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15371627467076466350859571 23057441200614699526289357)
                  ·
                    refine ⟨8646540450230512322358509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23057441200614699526289357 8646540450230512322358509)
                    ·
                      refine ⟨3242452668836442120884441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646540450230512322358509 3242452668836442120884441)
                      ·
                        rfl

theorem cell23_6314654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6314654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314654 prefixEnd_6314654 := by exact prefixLift 6314654
  have htrace : WordTrace (prefixWord ++ tailWord_6314654) baseStart_6314654 baseEnd_6314654 := by
    simpa [prefixWord, tailWord_6314654, baseEnd_6314654] using wordTrace_append hprefix tailTrace_6314654
  have hstable : (prefixWord ++ tailWord_6314654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314654).length < 2 ^ (prefixWord ++ tailWord_6314654).sum := by decide
  have hdescent : baseEnd_6314654 < baseStart_6314654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314677 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6314677 : Nat := 118140960795 + 6314677 * 2 ^ 59
def prefixEnd_6314677 : Nat := 4983230072969 + 3 ^ 40 * 6314677 * 2
def baseEnd_6314677 : Nat := 3242464478891495530896835

theorem tailTrace_6314677 : CollatzResearch.WordTrace tailWord_6314677 prefixEnd_6314677 3242464478891495530896835 := by
  unfold tailWord_6314677
  simp only [CollatzResearch.WordTrace]
  refine ⟨230315191344011164816046285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153543460896007443210697523 230315191344011164816046285)
  ·
    refine ⟨86368196754004186806017357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230315191344011164816046285 86368196754004186806017357)
    ·
      refine ⟨32388073782751570052256509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86368196754004186806017357 32388073782751570052256509)
      ·
        refine ⟨12145527668531838769596191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32388073782751570052256509 12145527668531838769596191)
        ·
          refine ⟨18218291502797758154394287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12145527668531838769596191 18218291502797758154394287)
          ·
            refine ⟨27327437254196637231591431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18218291502797758154394287 27327437254196637231591431)
            ·
              refine ⟨40991155881294955847387147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27327437254196637231591431 40991155881294955847387147)
              ·
                refine ⟨61486733821942433771080721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40991155881294955847387147 61486733821942433771080721)
                ·
                  refine ⟨46115050366456825328310541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61486733821942433771080721 46115050366456825328310541)
                  ·
                    refine ⟨17293143887421309498116453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46115050366456825328310541 17293143887421309498116453)
                    ·
                      refine ⟨3242464478891495530896835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293143887421309498116453 3242464478891495530896835)
                      ·
                        rfl

theorem cell23_6314677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6314677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314677 prefixEnd_6314677 := by exact prefixLift 6314677
  have htrace : WordTrace (prefixWord ++ tailWord_6314677) baseStart_6314677 baseEnd_6314677 := by
    simpa [prefixWord, tailWord_6314677, baseEnd_6314677] using wordTrace_append hprefix tailTrace_6314677
  have hstable : (prefixWord ++ tailWord_6314677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314677).length < 2 ^ (prefixWord ++ tailWord_6314677).sum := by decide
  have hdescent : baseEnd_6314677 < baseStart_6314677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314734 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_6314734 : Nat := 118140960795 + 6314734 * 2 ^ 59
def prefixEnd_6314734 : Nat := 4983230072969 + 3 ^ 40 * 6314734 * 2
def baseEnd_6314734 : Nat := 360277083032089089764897

theorem tailTrace_6314734 : CollatzResearch.WordTrace tailWord_6314734 prefixEnd_6314734 360277083032089089764897 := by
  unfold tailWord_6314734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28789658788100582943858907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153544846869869775700580837 28789658788100582943858907)
  ·
    refine ⟨43184488182150874415788361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28789658788100582943858907 43184488182150874415788361)
    ·
      refine ⟨32388366136613155811841271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43184488182150874415788361 32388366136613155811841271)
      ·
        refine ⟨48582549204919733717761907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32388366136613155811841271 48582549204919733717761907)
        ·
          refine ⟨72873823807379600576642861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48582549204919733717761907 72873823807379600576642861)
          ·
            refine ⟨27327683927767350216241073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72873823807379600576642861 27327683927767350216241073)
            ·
              refine ⟨20495762945825512662180805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27327683927767350216241073 20495762945825512662180805)
              ·
                refine ⟨3842955552342283624158901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20495762945825512662180805 3842955552342283624158901)
                ·
                  refine ⟨360277083032089089764897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842955552342283624158901 360277083032089089764897)
                  ·
                    rfl

theorem cell23_6314734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_6314734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314734 prefixEnd_6314734 := by exact prefixLift 6314734
  have htrace : WordTrace (prefixWord ++ tailWord_6314734) baseStart_6314734 baseEnd_6314734 := by
    simpa [prefixWord, tailWord_6314734, baseEnd_6314734] using wordTrace_append hprefix tailTrace_6314734
  have hstable : (prefixWord ++ tailWord_6314734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314734).length < 2 ^ (prefixWord ++ tailWord_6314734).sum := by decide
  have hdescent : baseEnd_6314734 < baseStart_6314734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314767 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_6314767 : Nat := 118140960795 + 6314767 * 2 ^ 59
def prefixEnd_6314767 : Nat := 4983230072969 + 3 ^ 40 * 6314767 * 2
def baseEnd_6314767 : Nat := 3242510692150400178771421

theorem tailTrace_6314767 : CollatzResearch.WordTrace tailWord_6314767 prefixEnd_6314767 3242510692150400178771421 := by
  unfold tailWord_6314767
  simp only [CollatzResearch.WordTrace]
  refine ⟨230318473913685110186822555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153545649275790073457881703 230318473913685110186822555)
  ·
    refine ⟨345477710870527665280233833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230318473913685110186822555 345477710870527665280233833)
    ·
      refine ⟨259108283152895748960175375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345477710870527665280233833 259108283152895748960175375)
      ·
        refine ⟨388662424729343623440263063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259108283152895748960175375 388662424729343623440263063)
        ·
          refine ⟨582993637094015435160394595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388662424729343623440263063 582993637094015435160394595)
          ·
            refine ⟨874490455641023152740591893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582993637094015435160394595 874490455641023152740591893)
            ·
              refine ⟨40991740108172960284715245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 874490455641023152740591893 40991740108172960284715245)
              ·
                refine ⟨15371902540564860106768217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40991740108172960284715245 15371902540564860106768217)
                ·
                  refine ⟨11528926905423645080076163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371902540564860106768217 11528926905423645080076163)
                  ·
                    refine ⟨17293390358135467620114245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11528926905423645080076163 17293390358135467620114245)
                    ·
                      refine ⟨3242510692150400178771421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293390358135467620114245 3242510692150400178771421)
                      ·
                        rfl

theorem cell23_6314767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_6314767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314767 prefixEnd_6314767 := by exact prefixLift 6314767
  have htrace : WordTrace (prefixWord ++ tailWord_6314767) baseStart_6314767 baseEnd_6314767 := by
    simpa [prefixWord, tailWord_6314767, baseEnd_6314767] using wordTrace_append hprefix tailTrace_6314767
  have hstable : (prefixWord ++ tailWord_6314767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314767).length < 2 ^ (prefixWord ++ tailWord_6314767).sum := by decide
  have hdescent : baseEnd_6314767 < baseStart_6314767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314781 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6314781 : Nat := 118140960795 + 6314781 * 2 ^ 59
def prefixEnd_6314781 : Nat := 4983230072969 + 3 ^ 40 * 6314781 * 2
def baseEnd_6314781 : Nat := 1080839293626521041332119

theorem tailTrace_6314781 : CollatzResearch.WordTrace tailWord_6314781 prefixEnd_6314781 1080839293626521041332119 := by
  unfold tailWord_6314781
  simp only [CollatzResearch.WordTrace]
  refine ⟨230318984535634390577832197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153545989690422927051888131 230318984535634390577832197)
  ·
    refine ⟨43184809600431448233343537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230318984535634390577832197 43184809600431448233343537)
    ·
      refine ⟨32388607200323586175007653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43184809600431448233343537 32388607200323586175007653)
      ·
        refine ⟨6072863850060672407813935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32388607200323586175007653 6072863850060672407813935)
        ·
          refine ⟨9109295775091008611720903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072863850060672407813935 9109295775091008611720903)
          ·
            refine ⟨13663943662636512917581355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109295775091008611720903 13663943662636512917581355)
            ·
              refine ⟨20495915493954769376372033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663943662636512917581355 20495915493954769376372033)
              ·
                refine ⟨15371936620466077032279025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20495915493954769376372033 15371936620466077032279025)
                ·
                  refine ⟨11528952465349557774209269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371936620466077032279025 11528952465349557774209269)
                  ·
                    refine ⟨1080839293626521041332119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11528952465349557774209269 1080839293626521041332119)
                    ·
                      rfl

theorem cell23_6314781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6314781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314781 prefixEnd_6314781 := by exact prefixLift 6314781
  have htrace : WordTrace (prefixWord ++ tailWord_6314781) baseStart_6314781 baseEnd_6314781 := by
    simpa [prefixWord, tailWord_6314781, baseEnd_6314781] using wordTrace_append hprefix tailTrace_6314781
  have hstable : (prefixWord ++ tailWord_6314781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314781).length < 2 ^ (prefixWord ++ tailWord_6314781).sum := by decide
  have hdescent : baseEnd_6314781 < baseStart_6314781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314784 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6314784 : Nat := 118140960795 + 6314784 * 2 ^ 59
def prefixEnd_6314784 : Nat := 4983230072969 + 3 ^ 40 * 6314784 * 2
def baseEnd_6314784 : Nat := 3242519421321526612258843

theorem tailTrace_6314784 : CollatzResearch.WordTrace tailWord_6314784 prefixEnd_6314784 3242519421321526612258843 := by
  unfold tailWord_6314784
  simp only [CollatzResearch.WordTrace]
  refine ⟨115159546977311761045095703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153546062636415681393460937 115159546977311761045095703)
  ·
    refine ⟨172739320465967641567643555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115159546977311761045095703 172739320465967641567643555)
    ·
      refine ⟨259108980698951462351465333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172739320465967641567643555 259108980698951462351465333)
      ·
        refine ⟨24291466940526699595449875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259108980698951462351465333 24291466940526699595449875)
        ·
          refine ⟨36437200410790049393174813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24291466940526699595449875 36437200410790049393174813)
          ·
            refine ⟨13663950154046268522440555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36437200410790049393174813 13663950154046268522440555)
            ·
              refine ⟨20495925231069402783660833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663950154046268522440555 20495925231069402783660833)
              ·
                refine ⟨15371943923302052087745625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20495925231069402783660833 15371943923302052087745625)
                ·
                  refine ⟨11528957942476539065809219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371943923302052087745625 11528957942476539065809219)
                  ·
                    refine ⟨17293436913714808598713829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11528957942476539065809219 17293436913714808598713829)
                    ·
                      refine ⟨3242519421321526612258843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293436913714808598713829 3242519421321526612258843)
                      ·
                        rfl

theorem cell23_6314784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6314784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314784 prefixEnd_6314784 := by exact prefixLift 6314784
  have htrace : WordTrace (prefixWord ++ tailWord_6314784) baseStart_6314784 baseEnd_6314784 := by
    simpa [prefixWord, tailWord_6314784, baseEnd_6314784] using wordTrace_append hprefix tailTrace_6314784
  have hstable : (prefixWord ++ tailWord_6314784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314784).length < 2 ^ (prefixWord ++ tailWord_6314784).sum := by decide
  have hdescent : baseEnd_6314784 < baseStart_6314784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314807 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 6]
def baseStart_6314807 : Nat := 118140960795 + 6314807 * 2 ^ 59
def prefixEnd_6314807 : Nat := 4983230072969 + 3 ^ 40 * 6314807 * 2
def baseEnd_6314807 : Nat := 360281247930731113585693

theorem tailTrace_6314807 : CollatzResearch.WordTrace tailWord_6314807 prefixEnd_6314807 360281247930731113585693 := by
  unfold tailWord_6314807
  simp only [CollatzResearch.WordTrace]
  refine ⟨230319932833540197018278675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153546621889026798012185783 230319932833540197018278675)
  ·
    refine ⟨345479899250310295527418013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230319932833540197018278675 345479899250310295527418013)
    ·
      refine ⟨129554962218866360822781755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345479899250310295527418013 129554962218866360822781755)
      ·
        refine ⟨194332443328299541234172633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129554962218866360822781755 194332443328299541234172633)
        ·
          refine ⟨145749332496224655925629475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194332443328299541234172633 145749332496224655925629475)
          ·
            refine ⟨218623998744336983888444213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145749332496224655925629475 218623998744336983888444213)
            ·
              refine ⟨20495999882281592239541645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218623998744336983888444213 20495999882281592239541645)
              ·
                refine ⟨7685999955855597089828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20495999882281592239541645 7685999955855597089828117)
                ·
                  refine ⟨360281247930731113585693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7685999955855597089828117 360281247930731113585693)
                  ·
                    rfl

theorem cell23_6314807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 6].length) (baseStart_6314807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314807 prefixEnd_6314807 := by exact prefixLift 6314807
  have htrace : WordTrace (prefixWord ++ tailWord_6314807) baseStart_6314807 baseEnd_6314807 := by
    simpa [prefixWord, tailWord_6314807, baseEnd_6314807] using wordTrace_append hprefix tailTrace_6314807
  have hstable : (prefixWord ++ tailWord_6314807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314807).length < 2 ^ (prefixWord ++ tailWord_6314807).sum := by decide
  have hdescent : baseEnd_6314807 < baseStart_6314807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314867 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 6]
def baseStart_6314867 : Nat := 118140960795 + 6314867 * 2 ^ 59
def prefixEnd_6314867 : Nat := 4983230072969 + 3 ^ 40 * 6314867 * 2
def baseEnd_6314867 : Nat := 1080854013405283262506987

theorem tailTrace_6314867 : CollatzResearch.WordTrace tailWord_6314867 prefixEnd_6314867 1080854013405283262506987 := by
  unfold tailWord_6314867
  simp only [CollatzResearch.WordTrace]
  refine ⟨230322121213322827265462855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153548080808881884843641903 230322121213322827265462855)
  ·
    refine ⟨345483181819984240898194283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230322121213322827265462855 345483181819984240898194283)
    ·
      refine ⟨518224772729976361347291425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345483181819984240898194283 518224772729976361347291425)
      ·
        refine ⟨388668579547482271010468569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518224772729976361347291425 388668579547482271010468569)
        ·
          refine ⟨291501434660611703257851427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388668579547482271010468569 291501434660611703257851427)
          ·
            refine ⟨437252151990917554886777141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291501434660611703257851427 437252151990917554886777141)
            ·
              refine ⟨40992389249148520770635357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437252151990917554886777141 40992389249148520770635357)
              ·
                refine ⟨15372145968430695288988259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40992389249148520770635357 15372145968430695288988259)
                ·
                  refine ⟨23058218952646042933482389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15372145968430695288988259 23058218952646042933482389)
                  ·
                    refine ⟨1080854013405283262506987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23058218952646042933482389 1080854013405283262506987)
                    ·
                      rfl

theorem cell23_6314867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_6314867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314867 prefixEnd_6314867 := by exact prefixLift 6314867
  have htrace : WordTrace (prefixWord ++ tailWord_6314867) baseStart_6314867 baseEnd_6314867 := by
    simpa [prefixWord, tailWord_6314867, baseEnd_6314867] using wordTrace_append hprefix tailTrace_6314867
  have hstable : (prefixWord ++ tailWord_6314867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314867).length < 2 ^ (prefixWord ++ tailWord_6314867).sum := by decide
  have hdescent : baseEnd_6314867 < baseStart_6314867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_6314874 : Nat := 118140960795 + 6314874 * 2 ^ 59
def prefixEnd_6314874 : Nat := 4983230072969 + 3 ^ 40 * 6314874 * 2
def baseEnd_6314874 : Nat := 3242565634580431260133429

theorem tailTrace_6314874 : CollatzResearch.WordTrace tailWord_6314874 prefixEnd_6314874 3242565634580431260133429 := by
  unfold tailWord_6314874
  simp only [CollatzResearch.WordTrace]
  refine ⟨57580594131074366865241919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153548251016198311640645117 57580594131074366865241919)
  ·
    refine ⟨86370891196611550297862879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57580594131074366865241919 86370891196611550297862879)
    ·
      refine ⟨129556336794917325446794319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86370891196611550297862879 129556336794917325446794319)
      ·
        refine ⟨194334505192375988170191479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129556336794917325446794319 194334505192375988170191479)
        ·
          refine ⟨291501757788563982255287219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194334505192375988170191479 291501757788563982255287219)
          ·
            refine ⟨437252636682845973382930829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291501757788563982255287219 437252636682845973382930829)
            ·
              refine ⟨163969738756067240018599061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437252636682845973382930829 163969738756067240018599061)
              ·
                refine ⟨7686081504190651875871831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163969738756067240018599061 7686081504190651875871831)
                ·
                  refine ⟨11529122256285977813807747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686081504190651875871831 11529122256285977813807747)
                  ·
                    refine ⟨17293683384428966720711621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529122256285977813807747 17293683384428966720711621)
                    ·
                      refine ⟨3242565634580431260133429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293683384428966720711621 3242565634580431260133429)
                      ·
                        rfl

theorem cell23_6314874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_6314874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314874 prefixEnd_6314874 := by exact prefixLift 6314874
  have htrace : WordTrace (prefixWord ++ tailWord_6314874) baseStart_6314874 baseEnd_6314874 := by
    simpa [prefixWord, tailWord_6314874, baseEnd_6314874] using wordTrace_append hprefix tailTrace_6314874
  have hstable : (prefixWord ++ tailWord_6314874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314874).length < 2 ^ (prefixWord ++ tailWord_6314874).sum := by decide
  have hdescent : baseEnd_6314874 < baseStart_6314874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314884 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_6314884 : Nat := 118140960795 + 6314884 * 2 ^ 59
def prefixEnd_6314884 : Nat := 4983230072969 + 3 ^ 40 * 6314884 * 2
def baseEnd_6314884 : Nat := 1080856923128992073669461

theorem tailTrace_6314884 : CollatzResearch.WordTrace tailWord_6314884 prefixEnd_6314884 1080856923128992073669461 := by
  unfold tailWord_6314884
  simp only [CollatzResearch.WordTrace]
  refine ⟨115161370627130619584415853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153548494169507492779221137 115161370627130619584415853)
  ·
    refine ⟨43185513985173982344155945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115161370627130619584415853 43185513985173982344155945)
    ·
      refine ⟨32389135488880486758116959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43185513985173982344155945 32389135488880486758116959)
      ·
        refine ⟨48583703233320730137175439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32389135488880486758116959 48583703233320730137175439)
        ·
          refine ⟨72875554849981095205763159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48583703233320730137175439 72875554849981095205763159)
          ·
            refine ⟨109313332274971642808644739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72875554849981095205763159 109313332274971642808644739)
            ·
              refine ⟨163969998412457464212967109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109313332274971642808644739 163969998412457464212967109)
              ·
                refine ⟨30744374702335774539931333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163969998412457464212967109 30744374702335774539931333)
                ·
                  refine ⟨5764570256687957726237125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30744374702335774539931333 5764570256687957726237125)
                  ·
                    refine ⟨1080856923128992073669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764570256687957726237125 1080856923128992073669461)
                    ·
                      rfl

theorem cell23_6314884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_6314884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314884 prefixEnd_6314884 := by exact prefixLift 6314884
  have htrace : WordTrace (prefixWord ++ tailWord_6314884) baseStart_6314884 baseEnd_6314884 := by
    simpa [prefixWord, tailWord_6314884, baseEnd_6314884] using wordTrace_append hprefix tailTrace_6314884
  have hstable : (prefixWord ++ tailWord_6314884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314884).length < 2 ^ (prefixWord ++ tailWord_6314884).sum := by decide
  have hdescent : baseEnd_6314884 < baseStart_6314884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314888 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_6314888 : Nat := 118140960795 + 6314888 * 2 ^ 59
def prefixEnd_6314888 : Nat := 4983230072969 + 3 ^ 40 * 6314888 * 2
def baseEnd_6314888 : Nat := 1080857607769864735119455

theorem tailTrace_6314888 : CollatzResearch.WordTrace tailWord_6314888 prefixEnd_6314888 1080857607769864735119455 := by
  unfold tailWord_6314888
  simp only [CollatzResearch.WordTrace]
  refine ⟨115161443573123373925988659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153548591430831165234651545 115161443573123373925988659)
  ·
    refine ⟨172742165359685060888982989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115161443573123373925988659 172742165359685060888982989)
    ·
      refine ⟨64778312009881897833368621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172742165359685060888982989 64778312009881897833368621)
      ·
        refine ⟨24291867003705711687513233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64778312009881897833368621 24291867003705711687513233)
        ·
          refine ⟨18218900252779283765634925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24291867003705711687513233 18218900252779283765634925)
          ·
            refine ⟨6832087594792231412113097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18218900252779283765634925 6832087594792231412113097)
            ·
              refine ⟨5124065696094173559084823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6832087594792231412113097 5124065696094173559084823)
              ·
                refine ⟨7686098544141260338627235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124065696094173559084823 7686098544141260338627235)
                ·
                  refine ⟨11529147816211890507940853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686098544141260338627235 11529147816211890507940853)
                  ·
                    refine ⟨1080857607769864735119455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11529147816211890507940853 1080857607769864735119455)
                    ·
                      rfl

theorem cell23_6314888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_6314888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314888 prefixEnd_6314888 := by exact prefixLift 6314888
  have htrace : WordTrace (prefixWord ++ tailWord_6314888) baseStart_6314888 baseEnd_6314888 := by
    simpa [prefixWord, tailWord_6314888, baseEnd_6314888] using wordTrace_append hprefix tailTrace_6314888
  have hstable : (prefixWord ++ tailWord_6314888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314888).length < 2 ^ (prefixWord ++ tailWord_6314888).sum := by decide
  have hdescent : baseEnd_6314888 < baseStart_6314888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314891 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 1, 1, 4]
def baseStart_6314891 : Nat := 118140960795 + 6314891 * 2 ^ 59
def prefixEnd_6314891 : Nat := 4983230072969 + 3 ^ 40 * 6314891 * 2
def baseEnd_6314891 : Nat := 3242574363751557693620851

theorem tailTrace_6314891 : CollatzResearch.WordTrace tailWord_6314891 prefixEnd_6314891 3242574363751557693620851 := by
  unfold tailWord_6314891
  simp only [CollatzResearch.WordTrace]
  refine ⟨230322996565235879364336527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153548664376823919576224351 230322996565235879364336527)
  ·
    refine ⟨345484494847853819046504791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230322996565235879364336527 345484494847853819046504791)
    ·
      refine ⟨518226742271780728569757187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345484494847853819046504791 518226742271780728569757187)
      ·
        refine ⟨777340113407671092854635781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518226742271780728569757187 777340113407671092854635781)
        ·
          refine ⟨145751271263938329910244209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 777340113407671092854635781 145751271263938329910244209)
          ·
            refine ⟨109313453447953747432683157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145751271263938329910244209 109313453447953747432683157)
            ·
              refine ⟨5124068130372831910907023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109313453447953747432683157 5124068130372831910907023)
              ·
                refine ⟨7686102195559247866360535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124068130372831910907023 7686102195559247866360535)
                ·
                  refine ⟨11529153293338871799540803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686102195559247866360535 11529153293338871799540803)
                  ·
                    refine ⟨17293729940008307699311205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529153293338871799540803 17293729940008307699311205)
                    ·
                      refine ⟨3242574363751557693620851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293729940008307699311205 3242574363751557693620851)
                      ·
                        rfl

theorem cell23_6314891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 1, 4].length) (baseStart_6314891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314891 prefixEnd_6314891 := by exact prefixLift 6314891
  have htrace : WordTrace (prefixWord ++ tailWord_6314891) baseStart_6314891 baseEnd_6314891 := by
    simpa [prefixWord, tailWord_6314891, baseEnd_6314891] using wordTrace_append hprefix tailTrace_6314891
  have hstable : (prefixWord ++ tailWord_6314891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314891).length < 2 ^ (prefixWord ++ tailWord_6314891).sum := by decide
  have hdescent : baseEnd_6314891 < baseStart_6314891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314901 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_6314901 : Nat := 118140960795 + 6314901 * 2 ^ 59
def prefixEnd_6314901 : Nat := 4983230072969 + 3 ^ 40 * 6314901 * 2
def baseEnd_6314901 : Nat := 1080859832852700884831935

theorem tailTrace_6314901 : CollatzResearch.WordTrace tailWord_6314901 prefixEnd_6314901 1080859832852700884831935 := by
  unfold tailWord_6314901
  simp only [CollatzResearch.WordTrace]
  refine ⟨230323361295199651072200557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153548907530133100714800371 230323361295199651072200557)
  ·
    refine ⟨86371260485699869152075209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230323361295199651072200557 86371260485699869152075209)
    ·
      refine ⟨64778445364274901864056407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86371260485699869152075209 64778445364274901864056407)
      ·
        refine ⟨97167668046412352796084611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64778445364274901864056407 97167668046412352796084611)
        ·
          refine ⟨145751502069618529194126917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97167668046412352796084611 145751502069618529194126917)
          ·
            refine ⟨27328406638053474223898797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145751502069618529194126917 27328406638053474223898797)
            ·
              refine ⟨10248152489270052833962049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27328406638053474223898797 10248152489270052833962049)
              ·
                refine ⟨7686114366952539625471537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248152489270052833962049 7686114366952539625471537)
                ·
                  refine ⟨5764585775214404719103653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686114366952539625471537 5764585775214404719103653)
                  ·
                    refine ⟨1080859832852700884831935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764585775214404719103653 1080859832852700884831935)
                    ·
                      rfl

theorem cell23_6314901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_6314901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314901 prefixEnd_6314901 := by exact prefixLift 6314901
  have htrace : WordTrace (prefixWord ++ tailWord_6314901) baseStart_6314901 baseEnd_6314901 := by
    simpa [prefixWord, tailWord_6314901, baseEnd_6314901] using wordTrace_append hprefix tailTrace_6314901
  have hstable : (prefixWord ++ tailWord_6314901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314901).length < 2 ^ (prefixWord ++ tailWord_6314901).sum := by decide
  have hdescent : baseEnd_6314901 < baseStart_6314901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314902 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6314902 : Nat := 118140960795 + 6314902 * 2 ^ 59
def prefixEnd_6314902 : Nat := 4983230072969 + 3 ^ 40 * 6314902 * 2
def baseEnd_6314902 : Nat := 3242580012038757150583301

theorem tailTrace_6314902 : CollatzResearch.WordTrace tailWord_6314902 prefixEnd_6314902 3242580012038757150583301 := by
  unfold tailWord_6314902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395212360512251765186685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153548931845464018828657973 14395212360512251765186685)
  ·
    refine ⟨5398204635192094411945007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14395212360512251765186685 5398204635192094411945007)
    ·
      refine ⟨8097306952788141617917511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398204635192094411945007 8097306952788141617917511)
      ·
        refine ⟨12145960429182212426876267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097306952788141617917511 12145960429182212426876267)
        ·
          refine ⟨18218940643773318640314401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12145960429182212426876267 18218940643773318640314401)
          ·
            refine ⟨13664205482829988980235801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18218940643773318640314401 13664205482829988980235801)
            ·
              refine ⟨10248154112122491735176851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13664205482829988980235801 10248154112122491735176851)
              ·
                refine ⟨15372231168183737602765277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248154112122491735176851 15372231168183737602765277)
                ·
                  refine ⟨5764586688068901601036979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15372231168183737602765277 5764586688068901601036979)
                  ·
                    refine ⟨8646880032103352401555469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764586688068901601036979 8646880032103352401555469)
                    ·
                      refine ⟨3242580012038757150583301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8646880032103352401555469 3242580012038757150583301)
                      ·
                        rfl

theorem cell23_6314902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6314902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314902 prefixEnd_6314902 := by exact prefixLift 6314902
  have htrace : WordTrace (prefixWord ++ tailWord_6314902) baseStart_6314902 baseEnd_6314902 := by
    simpa [prefixWord, tailWord_6314902, baseEnd_6314902] using wordTrace_append hprefix tailTrace_6314902
  have hstable : (prefixWord ++ tailWord_6314902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314902).length < 2 ^ (prefixWord ++ tailWord_6314902).sum := by decide
  have hdescent : baseEnd_6314902 < baseStart_6314902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314925 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6314925 : Nat := 118140960795 + 6314925 * 2 ^ 59
def prefixEnd_6314925 : Nat := 4983230072969 + 3 ^ 40 * 6314925 * 2
def baseEnd_6314925 : Nat := 3242591822093810560595695

theorem tailTrace_6314925 : CollatzResearch.WordTrace tailWord_6314925 prefixEnd_6314925 3242591822093810560595695 := by
  unfold tailWord_6314925
  simp only [CollatzResearch.WordTrace]
  refine ⟨230324236647112703171074229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153549491098075135447382819 230324236647112703171074229)
  ·
    refine ⟨21592897185666815922288209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230324236647112703171074229 21592897185666815922288209)
    ·
      refine ⟨16194672889250111941716157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21592897185666815922288209 16194672889250111941716157)
      ·
        refine ⟨6073002333468791978143559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16194672889250111941716157 6073002333468791978143559)
        ·
          refine ⟨9109503500203187967215339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073002333468791978143559 9109503500203187967215339)
          ·
            refine ⟨13664255250304781950823009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109503500203187967215339 13664255250304781950823009)
            ·
              refine ⟨10248191437728586463117257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13664255250304781950823009 10248191437728586463117257)
              ·
                refine ⟨7686143578296439847337943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248191437728586463117257 7686143578296439847337943)
                ·
                  refine ⟨11529215367444659771006915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686143578296439847337943 11529215367444659771006915)
                  ·
                    refine ⟨17293823051166989656510373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529215367444659771006915 17293823051166989656510373)
                    ·
                      refine ⟨3242591822093810560595695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17293823051166989656510373 3242591822093810560595695)
                      ·
                        rfl

theorem cell23_6314925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6314925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314925 prefixEnd_6314925 := by exact prefixLift 6314925
  have htrace : WordTrace (prefixWord ++ tailWord_6314925) baseStart_6314925 baseEnd_6314925 := by
    simpa [prefixWord, tailWord_6314925, baseEnd_6314925] using wordTrace_append hprefix tailTrace_6314925
  have hstable : (prefixWord ++ tailWord_6314925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314925).length < 2 ^ (prefixWord ++ tailWord_6314925).sum := by decide
  have hdescent : baseEnd_6314925 < baseStart_6314925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314948 : List Nat := [2, 3, 3, 3, 2, 1, 9]
def baseStart_6314948 : Nat := 118140960795 + 6314948 * 2 ^ 59
def prefixEnd_6314948 : Nat := 4983230072969 + 3 ^ 40 * 6314948 * 2
def baseEnd_6314948 : Nat := 40032143606776098402569

theorem tailTrace_6314948 : CollatzResearch.WordTrace tailWord_6314948 prefixEnd_6314948 40032143606776098402569 := by
  unfold tailWord_6314948
  simp only [CollatzResearch.WordTrace]
  refine ⟨115162537763014689049580749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153550050350686252066107665 115162537763014689049580749)
  ·
    refine ⟨43185951661130508393592781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115162537763014689049580749 43185951661130508393592781)
    ·
      refine ⟨16194731872923940647597293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43185951661130508393592781 16194731872923940647597293)
      ·
        refine ⟨6073024452346477742848985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16194731872923940647597293 6073024452346477742848985)
        ·
          refine ⟨4554768339259858307136739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6073024452346477742848985 4554768339259858307136739)
          ·
            refine ⟨6832152508889787460705109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554768339259858307136739 6832152508889787460705109)
            ·
              refine ⟨40032143606776098402569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6832152508889787460705109 40032143606776098402569)
              ·
                rfl

theorem cell23_6314948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 9].length) (baseStart_6314948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314948 prefixEnd_6314948 := by exact prefixLift 6314948
  have htrace : WordTrace (prefixWord ++ tailWord_6314948) baseStart_6314948 baseEnd_6314948 := by
    simpa [prefixWord, tailWord_6314948, baseEnd_6314948] using wordTrace_append hprefix tailTrace_6314948
  have hstable : (prefixWord ++ tailWord_6314948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314948).length < 2 ^ (prefixWord ++ tailWord_6314948).sum := by decide
  have hdescent : baseEnd_6314948 < baseStart_6314948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314984 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6314984 : Nat := 118140960795 + 6314984 * 2 ^ 59
def prefixEnd_6314984 : Nat := 4983230072969 + 3 ^ 40 * 6314984 * 2
def baseEnd_6314984 : Nat := 3242622117452425829757923

theorem tailTrace_6314984 : CollatzResearch.WordTrace tailWord_6314984 prefixEnd_6314984 3242622117452425829757923 := by
  unfold tailWord_6314984
  simp only [CollatzResearch.WordTrace]
  refine ⟨115163194276949478123736003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153550925702599304164981337 115163194276949478123736003)
  ·
    refine ⟨172744791415424217185604005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115163194276949478123736003 172744791415424217185604005)
    ·
      refine ⟨32389648390392040722300751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172744791415424217185604005 32389648390392040722300751)
      ·
        refine ⟨48584472585588061083451127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32389648390392040722300751 48584472585588061083451127)
        ·
          refine ⟨72876708878382091625176691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48584472585588061083451127 72876708878382091625176691)
          ·
            refine ⟨109315063317573137437765037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72876708878382091625176691 109315063317573137437765037)
            ·
              refine ⟨40993148744089926539161889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109315063317573137437765037 40993148744089926539161889)
              ·
                refine ⟨30744861558067444904371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40993148744089926539161889 30744861558067444904371417)
                ·
                  refine ⟨23058646168550583678278563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30744861558067444904371417 23058646168550583678278563)
                  ·
                    refine ⟨34587969252825875517417845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23058646168550583678278563 34587969252825875517417845)
                    ·
                      refine ⟨3242622117452425829757923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34587969252825875517417845 3242622117452425829757923)
                      ·
                        rfl

theorem cell23_6314984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6314984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314984 prefixEnd_6314984 := by exact prefixLift 6314984
  have htrace : WordTrace (prefixWord ++ tailWord_6314984) baseStart_6314984 baseEnd_6314984 := by
    simpa [prefixWord, tailWord_6314984, baseEnd_6314984] using wordTrace_append hprefix tailTrace_6314984
  have hstable : (prefixWord ++ tailWord_6314984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314984).length < 2 ^ (prefixWord ++ tailWord_6314984).sum := by decide
  have hdescent : baseEnd_6314984 < baseStart_6314984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314996 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6314996 : Nat := 118140960795 + 6314996 * 2 ^ 59
def prefixEnd_6314996 : Nat := 4983230072969 + 3 ^ 40 * 6314996 * 2
def baseEnd_6314996 : Nat := 3242628279220279782807869

theorem tailTrace_6314996 : CollatzResearch.WordTrace tailWord_6314996 prefixEnd_6314996 3242628279220279782807869 := by
  unfold tailWord_6314996
  simp only [CollatzResearch.WordTrace]
  refine ⟨115163413114927741148454421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153551217486570321531272561 115163413114927741148454421)
  ·
    refine ⟨5398284989762237866333801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115163413114927741148454421 5398284989762237866333801)
    ·
      refine ⟨4048713742321678399750351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5398284989762237866333801 4048713742321678399750351)
      ·
        refine ⟨6073070613482517599625527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048713742321678399750351 6073070613482517599625527)
        ·
          refine ⟨9109605920223776399438291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073070613482517599625527 9109605920223776399438291)
          ·
            refine ⟨13664408880335664599157437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109605920223776399438291 13664408880335664599157437)
            ·
              refine ⟨5124153330125874224684039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13664408880335664599157437 5124153330125874224684039)
              ·
                refine ⟨7686229995188811337026059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124153330125874224684039 7686229995188811337026059)
                ·
                  refine ⟨11529344992783217005539089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686229995188811337026059 11529344992783217005539089)
                  ·
                    refine ⟨8647008744587412754154317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11529344992783217005539089 8647008744587412754154317)
                    ·
                      refine ⟨3242628279220279782807869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647008744587412754154317 3242628279220279782807869)
                      ·
                        rfl

theorem cell23_6314996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6314996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314996 prefixEnd_6314996 := by exact prefixLift 6314996
  have htrace : WordTrace (prefixWord ++ tailWord_6314996) baseStart_6314996 baseEnd_6314996 := by
    simpa [prefixWord, tailWord_6314996, baseEnd_6314996] using wordTrace_append hprefix tailTrace_6314996
  have hstable : (prefixWord ++ tailWord_6314996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314996).length < 2 ^ (prefixWord ++ tailWord_6314996).sum := by decide
  have hdescent : baseEnd_6314996 < baseStart_6314996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314998 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6314998 : Nat := 118140960795 + 6314998 * 2 ^ 59
def prefixEnd_6314998 : Nat := 4983230072969 + 3 ^ 40 * 6314998 * 2
def baseEnd_6314998 : Nat := 3242629306181588774982859

theorem tailTrace_6314998 : CollatzResearch.WordTrace tailWord_6314998 prefixEnd_6314998 3242629306181588774982859 := by
  unfold tailWord_6314998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395431198490514789905103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153551266117232157758987765 14395431198490514789905103)
  ·
    refine ⟨21593146797735772184857655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14395431198490514789905103 21593146797735772184857655)
    ·
      refine ⟨32389720196603658277286483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21593146797735772184857655 32389720196603658277286483)
      ·
        refine ⟨48584580294905487415929725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32389720196603658277286483 48584580294905487415929725)
        ·
          refine ⟨18219217610589557780973647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48584580294905487415929725 18219217610589557780973647)
          ·
            refine ⟨27328826415884336671460471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18219217610589557780973647 27328826415884336671460471)
            ·
              refine ⟨40993239623826505007190707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27328826415884336671460471 40993239623826505007190707)
              ·
                refine ⟨61489859435739757510786061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40993239623826505007190707 61489859435739757510786061)
                ·
                  refine ⟨23058697288402409066544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61489859435739757510786061 23058697288402409066544773)
                  ·
                    refine ⟨4323505741575451699977145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23058697288402409066544773 4323505741575451699977145)
                    ·
                      refine ⟨3242629306181588774982859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323505741575451699977145 3242629306181588774982859)
                      ·
                        rfl

theorem cell23_6314998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6314998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314998 prefixEnd_6314998 := by exact prefixLift 6314998
  have htrace : WordTrace (prefixWord ++ tailWord_6314998) baseStart_6314998 baseEnd_6314998 := by
    simpa [prefixWord, tailWord_6314998, baseEnd_6314998] using wordTrace_append hprefix tailTrace_6314998
  have hstable : (prefixWord ++ tailWord_6314998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314998).length < 2 ^ (prefixWord ++ tailWord_6314998).sum := by decide
  have hdescent : baseEnd_6314998 < baseStart_6314998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315015 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6315015 : Nat := 118140960795 + 6315015 * 2 ^ 59
def prefixEnd_6315015 : Nat := 4983230072969 + 3 ^ 40 * 6315015 * 2
def baseEnd_6315015 : Nat := 3242638035352715208470281

theorem tailTrace_6315015 : CollatzResearch.WordTrace tailWord_6315015 prefixEnd_6315015 3242638035352715208470281 := by
  unfold tailWord_6315015
  simp only [CollatzResearch.WordTrace]
  refine ⟨230327519216786648541850499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153551679477857765694566999 230327519216786648541850499)
  ·
    refine ⟨345491278825179972812775749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230327519216786648541850499 345491278825179972812775749)
    ·
      refine ⟨64779614779721244902395453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345491278825179972812775749 64779614779721244902395453)
      ·
        refine ⟨24292355542395466838398295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64779614779721244902395453 24292355542395466838398295)
        ·
          refine ⟨36438533313593200257597443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24292355542395466838398295 36438533313593200257597443)
          ·
            refine ⟨54657799970389800386396165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36438533313593200257597443 54657799970389800386396165)
            ·
              refine ⟨10248337494448087572449281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54657799970389800386396165 10248337494448087572449281)
              ·
                refine ⟨7686253120836065679336961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248337494448087572449281 7686253120836065679336961)
                ·
                  refine ⟨5764689840627049259502721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686253120836065679336961 5764689840627049259502721)
                  ·
                    refine ⟨4323517380470286944627041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764689840627049259502721 4323517380470286944627041)
                    ·
                      refine ⟨3242638035352715208470281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323517380470286944627041 3242638035352715208470281)
                      ·
                        rfl

theorem cell23_6315015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6315015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315015 prefixEnd_6315015 := by exact prefixLift 6315015
  have htrace : WordTrace (prefixWord ++ tailWord_6315015) baseStart_6315015 baseEnd_6315015 := by
    simpa [prefixWord, tailWord_6315015, baseEnd_6315015] using wordTrace_append hprefix tailTrace_6315015
  have hstable : (prefixWord ++ tailWord_6315015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315015).length < 2 ^ (prefixWord ++ tailWord_6315015).sum := by decide
  have hdescent : baseEnd_6315015 < baseStart_6315015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315031 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6315031 : Nat := 118140960795 + 6315031 * 2 ^ 59
def prefixEnd_6315031 : Nat := 4983230072969 + 3 ^ 40 * 6315031 * 2
def baseEnd_6315031 : Nat := 3242646251043187145870207

theorem tailTrace_6315031 : CollatzResearch.WordTrace tailWord_6315031 prefixEnd_6315031 3242646251043187145870207 := by
  unfold tailWord_6315031
  simp only [CollatzResearch.WordTrace]
  refine ⟨230328102784728683274432947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153552068523152455516288631 230328102784728683274432947)
  ·
    refine ⟨345492154177093024911649421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230328102784728683274432947 345492154177093024911649421)
    ·
      refine ⟨129559557816409884341868533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345492154177093024911649421 129559557816409884341868533)
      ·
        refine ⟨12146208545288426657050175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129559557816409884341868533 12146208545288426657050175)
        ·
          refine ⟨18219312817932639985575263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146208545288426657050175 18219312817932639985575263)
          ·
            refine ⟨27328969226898959978362895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18219312817932639985575263 27328969226898959978362895)
            ·
              refine ⟨40993453840348439967544343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27328969226898959978362895 40993453840348439967544343)
              ·
                refine ⟨61490180760522659951316515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40993453840348439967544343 61490180760522659951316515)
                ·
                  refine ⟨92235271140783989926974773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61490180760522659951316515 92235271140783989926974773)
                  ·
                    refine ⟨8647056669448499055653885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92235271140783989926974773 8647056669448499055653885)
                    ·
                      refine ⟨3242646251043187145870207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647056669448499055653885 3242646251043187145870207)
                      ·
                        rfl

theorem cell23_6315031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6315031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315031 prefixEnd_6315031 := by exact prefixLift 6315031
  have htrace : WordTrace (prefixWord ++ tailWord_6315031) baseStart_6315031 baseEnd_6315031 := by
    simpa [prefixWord, tailWord_6315031, baseEnd_6315031] using wordTrace_append hprefix tailTrace_6315031
  have hstable : (prefixWord ++ tailWord_6315031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315031).length < 2 ^ (prefixWord ++ tailWord_6315031).sum := by decide
  have hdescent : baseEnd_6315031 < baseStart_6315031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315034 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_6315034 : Nat := 118140960795 + 6315034 * 2 ^ 59
def prefixEnd_6315034 : Nat := 4983230072969 + 3 ^ 40 * 6315034 * 2
def baseEnd_6315034 : Nat := 1080882597161716878044231

theorem tailTrace_6315034 : CollatzResearch.WordTrace tailWord_6315034 prefixEnd_6315034 1080882597161716878044231 := by
  unfold tailWord_6315034
  simp only [CollatzResearch.WordTrace]
  refine ⟨57582053050929453696698039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153552141469145209857861437 57582053050929453696698039)
  ·
    refine ⟨86373079576394180545047059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57582053050929453696698039 86373079576394180545047059)
    ·
      refine ⟨129559619364591270817570589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86373079576394180545047059 129559619364591270817570589)
      ·
        refine ⟨48584857261721726556588971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129559619364591270817570589 48584857261721726556588971)
        ·
          refine ⟨72877285892582589834883457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48584857261721726556588971 72877285892582589834883457)
          ·
            refine ⟨54657964419436942376162593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72877285892582589834883457 54657964419436942376162593)
            ·
              refine ⟨40993473314577706782121945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54657964419436942376162593 40993473314577706782121945)
              ·
                refine ⟨30745104985933280086591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40993473314577706782121945 30745104985933280086591459)
                ·
                  refine ⟨46117657478899920129887189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30745104985933280086591459 46117657478899920129887189)
                  ·
                    refine ⟨1080882597161716878044231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46117657478899920129887189 1080882597161716878044231)
                    ·
                      rfl

theorem cell23_6315034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_6315034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315034 prefixEnd_6315034 := by exact prefixLift 6315034
  have htrace : WordTrace (prefixWord ++ tailWord_6315034) baseStart_6315034 baseEnd_6315034 := by
    simpa [prefixWord, tailWord_6315034, baseEnd_6315034] using wordTrace_append hprefix tailTrace_6315034
  have hstable : (prefixWord ++ tailWord_6315034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315034).length < 2 ^ (prefixWord ++ tailWord_6315034).sum := by decide
  have hdescent : baseEnd_6315034 < baseStart_6315034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315084 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6315084 : Nat := 118140960795 + 6315084 * 2 ^ 59
def prefixEnd_6315084 : Nat := 4983230072969 + 3 ^ 40 * 6315084 * 2
def baseEnd_6315084 : Nat := 3242673465517875438507463

theorem tailTrace_6315084 : CollatzResearch.WordTrace tailWord_6315084 prefixEnd_6315084 3242673465517875438507463 := by
  unfold tailWord_6315084
  simp only [CollatzResearch.WordTrace]
  refine ⟨115165017926768336663056153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153553357235691115550741537 115165017926768336663056153)
  ·
    refine ⟨86373763445076252497292115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115165017926768336663056153 86373763445076252497292115)
    ·
      refine ⟨129560645167614378745938173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86373763445076252497292115 129560645167614378745938173)
      ·
        refine ⟨48585241937855392029726815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129560645167614378745938173 48585241937855392029726815)
        ·
          refine ⟨72877862906783088044590223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48585241937855392029726815 72877862906783088044590223)
          ·
            refine ⟨109316794360174632066885335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72877862906783088044590223 109316794360174632066885335)
            ·
              refine ⟨163975191540261948100328003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109316794360174632066885335 163975191540261948100328003)
              ·
                refine ⟨245962787310392922150492005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163975191540261948100328003 245962787310392922150492005)
                ·
                  refine ⟨46118022620698672903217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245962787310392922150492005 46118022620698672903217251)
                  ·
                    refine ⟨69177033931048009354825877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46118022620698672903217251 69177033931048009354825877)
                    ·
                      refine ⟨3242673465517875438507463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69177033931048009354825877 3242673465517875438507463)
                      ·
                        rfl

theorem cell23_6315084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6315084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315084 prefixEnd_6315084 := by exact prefixLift 6315084
  have htrace : WordTrace (prefixWord ++ tailWord_6315084) baseStart_6315084 baseEnd_6315084 := by
    simpa [prefixWord, tailWord_6315084, baseEnd_6315084] using wordTrace_append hprefix tailTrace_6315084
  have hstable : (prefixWord ++ tailWord_6315084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315084).length < 2 ^ (prefixWord ++ tailWord_6315084).sum := by decide
  have hdescent : baseEnd_6315084 < baseStart_6315084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315165 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_6315165 : Nat := 118140960795 + 6315165 * 2 ^ 59
def prefixEnd_6315165 : Nat := 4983230072969 + 3 ^ 40 * 6315165 * 2
def baseEnd_6315165 : Nat := 3242715057450889621594591

theorem tailTrace_6315165 : CollatzResearch.WordTrace tailWord_6315165 prefixEnd_6315165 3242715057450889621594591 := by
  unfold tailWord_6315165
  simp only [CollatzResearch.WordTrace]
  refine ⟨230332990166243224159810949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153555326777495482773207299 230332990166243224159810949)
  ·
    refine ⟨43187435656170604529964553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230332990166243224159810949 43187435656170604529964553)
    ·
      refine ⟨32390576742127953397473415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43187435656170604529964553 32390576742127953397473415)
      ·
        refine ⟨48585865113191930096210123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32390576742127953397473415 48585865113191930096210123)
        ·
          refine ⟨72878797669787895144315185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48585865113191930096210123 72878797669787895144315185)
          ·
            refine ⟨54659098252340921358236389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72878797669787895144315185 54659098252340921358236389)
            ·
              refine ⟨10248580922313922754669323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54659098252340921358236389 10248580922313922754669323)
              ·
                refine ⟨15372871383470884132003985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248580922313922754669323 15372871383470884132003985)
                ·
                  refine ⟨11529653537603163099002989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15372871383470884132003985 11529653537603163099002989)
                  ·
                    refine ⟨4323620076601186162126121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11529653537603163099002989 4323620076601186162126121)
                    ·
                      refine ⟨3242715057450889621594591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323620076601186162126121 3242715057450889621594591)
                      ·
                        rfl

theorem cell23_6315165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_6315165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315165 prefixEnd_6315165 := by exact prefixLift 6315165
  have htrace : WordTrace (prefixWord ++ tailWord_6315165) baseStart_6315165 baseEnd_6315165 := by
    simpa [prefixWord, tailWord_6315165, baseEnd_6315165] using wordTrace_append hprefix tailTrace_6315165
  have hstable : (prefixWord ++ tailWord_6315165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315165).length < 2 ^ (prefixWord ++ tailWord_6315165).sum := by decide
  have hdescent : baseEnd_6315165 < baseStart_6315165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315171 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 6, 4]
def baseStart_6315171 : Nat := 118140960795 + 6315171 * 2 ^ 59
def prefixEnd_6315171 : Nat := 4983230072969 + 3 ^ 40 * 6315171 * 2
def baseEnd_6315171 : Nat := 1080906046111605532706521

theorem tailTrace_6315171 : CollatzResearch.WordTrace tailWord_6315171 prefixEnd_6315171 1080906046111605532706521 := by
  unfold tailWord_6315171
  simp only [CollatzResearch.WordTrace]
  refine ⟨230333209004221487184529367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153555472669480991456352911 230333209004221487184529367)
  ·
    refine ⟨345499813506332230776794051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230333209004221487184529367 345499813506332230776794051)
    ·
      refine ⟨518249720259498346165191077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345499813506332230776794051 518249720259498346165191077)
      ·
        refine ⟨97171822548655939905973327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518249720259498346165191077 97171822548655939905973327)
        ·
          refine ⟨145757733822983909858959991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97171822548655939905973327 145757733822983909858959991)
          ·
            refine ⟨218636600734475864788439987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145757733822983909858959991 218636600734475864788439987)
            ·
              refine ⟨327954901101713797182659981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218636600734475864788439987 327954901101713797182659981)
              ·
                refine ⟨122983087913142673943497493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327954901101713797182659981 122983087913142673943497493)
                ·
                  refine ⟨5764832245928562841101445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122983087913142673943497493 5764832245928562841101445)
                  ·
                    refine ⟨1080906046111605532706521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764832245928562841101445 1080906046111605532706521)
                    ·
                      rfl

theorem cell23_6315171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 4].length) (baseStart_6315171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315171 prefixEnd_6315171 := by exact prefixLift 6315171
  have htrace : WordTrace (prefixWord ++ tailWord_6315171) baseStart_6315171 baseEnd_6315171 := by
    simpa [prefixWord, tailWord_6315171, baseEnd_6315171] using wordTrace_append hprefix tailTrace_6315171
  have hstable : (prefixWord ++ tailWord_6315171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315171).length < 2 ^ (prefixWord ++ tailWord_6315171).sum := by decide
  have hdescent : baseEnd_6315171 < baseStart_6315171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315191 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_6315191 : Nat := 118140960795 + 6315191 * 2 ^ 59
def prefixEnd_6315191 : Nat := 4983230072969 + 3 ^ 40 * 6315191 * 2
def baseEnd_6315191 : Nat := 3242728407947906519869471

theorem tailTrace_6315191 : CollatzResearch.WordTrace tailWord_6315191 prefixEnd_6315191 3242728407947906519869471 := by
  unfold tailWord_6315191
  simp only [CollatzResearch.WordTrace]
  refine ⟨230333938464149030600257427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153555958976099353733504951 230333938464149030600257427)
  ·
    refine ⟨345500907696223545900386141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230333938464149030600257427 345500907696223545900386141)
    ·
      refine ⟨129562840386083829712644803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345500907696223545900386141 129562840386083829712644803)
      ·
        refine ⟨194344260579125744568967205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129562840386083829712644803 194344260579125744568967205)
        ·
          refine ⟨36439548858586077106681351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194344260579125744568967205 36439548858586077106681351)
          ·
            refine ⟨54659323287879115660022027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36439548858586077106681351 54659323287879115660022027)
            ·
              refine ⟨81988984931818673490033041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54659323287879115660022027 81988984931818673490033041)
              ·
                refine ⟨61491738698864005117524781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81988984931818673490033041 61491738698864005117524781)
                ·
                  refine ⟨23059402012074001919071793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61491738698864005117524781 23059402012074001919071793)
                  ·
                    refine ⟨17294551509055501439303845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23059402012074001919071793 17294551509055501439303845)
                    ·
                      refine ⟨3242728407947906519869471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17294551509055501439303845 3242728407947906519869471)
                      ·
                        rfl

theorem cell23_6315191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_6315191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315191 prefixEnd_6315191 := by exact prefixLift 6315191
  have htrace : WordTrace (prefixWord ++ tailWord_6315191) baseStart_6315191 baseEnd_6315191 := by
    simpa [prefixWord, tailWord_6315191, baseEnd_6315191] using wordTrace_append hprefix tailTrace_6315191
  have hstable : (prefixWord ++ tailWord_6315191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315191).length < 2 ^ (prefixWord ++ tailWord_6315191).sum := by decide
  have hdescent : baseEnd_6315191 < baseStart_6315191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315206 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6315206 : Nat := 118140960795 + 6315206 * 2 ^ 59
def prefixEnd_6315206 : Nat := 4983230072969 + 3 ^ 40 * 6315206 * 2
def baseEnd_6315206 : Nat := 3242736110157723961181903

theorem tailTrace_6315206 : CollatzResearch.WordTrace tailWord_6315206 prefixEnd_6315206 3242736110157723961181903 := by
  unfold tailWord_6315206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197952673721709005064171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153556323706063125441368981 7197952673721709005064171)
  ·
    refine ⟨10796929010582563507596257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7197952673721709005064171 10796929010582563507596257)
    ·
      refine ⟨8097696757936922630697193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10796929010582563507596257 8097696757936922630697193)
      ·
        refine ⟨6073272568452691973022895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8097696757936922630697193 6073272568452691973022895)
        ·
          refine ⟨9109908852679037959534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073272568452691973022895 9109908852679037959534343)
          ·
            refine ⟨13664863279018556939301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109908852679037959534343 13664863279018556939301515)
            ·
              refine ⟨20497294918527835408952273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13664863279018556939301515 20497294918527835408952273)
              ·
                refine ⟨15372971188895876556714205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20497294918527835408952273 15372971188895876556714205)
                ·
                  refine ⟨5764864195835953708767827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15372971188895876556714205 5764864195835953708767827)
                  ·
                    refine ⟨8647296293753930563151741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764864195835953708767827 8647296293753930563151741)
                    ·
                      refine ⟨3242736110157723961181903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647296293753930563151741 3242736110157723961181903)
                      ·
                        rfl

theorem cell23_6315206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6315206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315206 prefixEnd_6315206 := by exact prefixLift 6315206
  have htrace : WordTrace (prefixWord ++ tailWord_6315206) baseStart_6315206 baseEnd_6315206 := by
    simpa [prefixWord, tailWord_6315206, baseEnd_6315206] using wordTrace_append hprefix tailTrace_6315206
  have hstable : (prefixWord ++ tailWord_6315206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315206).length < 2 ^ (prefixWord ++ tailWord_6315206).sum := by decide
  have hdescent : baseEnd_6315206 < baseStart_6315206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315218 : List Nat := [3, 2, 2, 2, 1, 1, 5, 7]
def baseStart_6315218 : Nat := 118140960795 + 6315218 * 2 ^ 59
def prefixEnd_6315218 : Nat := 4983230072969 + 3 ^ 40 * 6315218 * 2
def baseEnd_6315218 : Nat := 120101565626873256082661

theorem tailTrace_6315218 : CollatzResearch.WordTrace tailWord_6315218 prefixEnd_6315218 120101565626873256082661 := by
  unfold tailWord_6315218
  simp only [CollatzResearch.WordTrace]
  refine ⟨57583730808762803552872577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153556615490034142807660205 57583730808762803552872577)
  ·
    refine ⟨43187798106572102664654433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57583730808762803552872577 43187798106572102664654433)
    ·
      refine ⟨32390848579929076998490825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43187798106572102664654433 32390848579929076998490825)
      ·
        refine ⟨24293136434946807748868119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32390848579929076998490825 24293136434946807748868119)
        ·
          refine ⟨36439704652420211623302179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293136434946807748868119 36439704652420211623302179)
          ·
            refine ⟨54659556978630317434953269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36439704652420211623302179 54659556978630317434953269)
            ·
              refine ⟨5124333466746592259526869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54659556978630317434953269 5124333466746592259526869)
              ·
                refine ⟨120101565626873256082661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5124333466746592259526869 120101565626873256082661)
                ·
                  rfl

theorem cell23_6315218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_6315218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315218 prefixEnd_6315218 := by exact prefixLift 6315218
  have htrace : WordTrace (prefixWord ++ tailWord_6315218) baseStart_6315218 baseEnd_6315218 := by
    simpa [prefixWord, tailWord_6315218, baseEnd_6315218] using wordTrace_append hprefix tailTrace_6315218
  have hstable : (prefixWord ++ tailWord_6315218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315218).length < 2 ^ (prefixWord ++ tailWord_6315218).sum := by decide
  have hdescent : baseEnd_6315218 < baseStart_6315218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315229 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6315229 : Nat := 118140960795 + 6315229 * 2 ^ 59
def prefixEnd_6315229 : Nat := 4983230072969 + 3 ^ 40 * 6315229 * 2
def baseEnd_6315229 : Nat := 3242747920212777371194297

theorem tailTrace_6315229 : CollatzResearch.WordTrace tailWord_6315229 prefixEnd_6315229 3242747920212777371194297 := by
  unfold tailWord_6315229
  simp only [CollatzResearch.WordTrace]
  refine ⟨230335324438011363090140741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153556882958674242060093827 230335324438011363090140741)
  ·
    refine ⟨43187873332127130579401389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230335324438011363090140741 43187873332127130579401389)
    ·
      refine ⟨16195452499547673967275521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43187873332127130579401389 16195452499547673967275521)
      ·
        refine ⟨12146589374660755475456641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16195452499547673967275521 12146589374660755475456641)
        ·
          refine ⟨9109942030995566606592481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12146589374660755475456641 9109942030995566606592481)
          ·
            refine ⟨6832456523246674954944361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9109942030995566606592481 6832456523246674954944361)
            ·
              refine ⟨5124342392435006216208271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6832456523246674954944361 5124342392435006216208271)
              ·
                refine ⟨7686513588652509324312407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124342392435006216208271 7686513588652509324312407)
                ·
                  refine ⟨11529770382978763986468611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686513588652509324312407 11529770382978763986468611)
                  ·
                    refine ⟨17294655574468145979702917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529770382978763986468611 17294655574468145979702917)
                    ·
                      refine ⟨3242747920212777371194297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17294655574468145979702917 3242747920212777371194297)
                      ·
                        rfl

theorem cell23_6315229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6315229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315229 prefixEnd_6315229 := by exact prefixLift 6315229
  have htrace : WordTrace (prefixWord ++ tailWord_6315229) baseStart_6315229 baseEnd_6315229 := by
    simpa [prefixWord, tailWord_6315229, baseEnd_6315229] using wordTrace_append hprefix tailTrace_6315229
  have hstable : (prefixWord ++ tailWord_6315229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315229).length < 2 ^ (prefixWord ++ tailWord_6315229).sum := by decide
  have hdescent : baseEnd_6315229 < baseStart_6315229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315232 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3]
def baseStart_6315232 : Nat := 118140960795 + 6315232 * 2 ^ 59
def prefixEnd_6315232 : Nat := 4983230072969 + 3 ^ 40 * 6315232 * 2
def baseEnd_6315232 : Nat := 3242749460654740859456783

theorem tailTrace_6315232 : CollatzResearch.WordTrace tailWord_6315232 prefixEnd_6315232 3242749460654740859456783 := by
  unfold tailWord_6315232
  simp only [CollatzResearch.WordTrace]
  refine ⟨115167716928500247301249975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153556955904666996401666633 115167716928500247301249975)
  ·
    refine ⟨172751575392750370951874963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115167716928500247301249975 172751575392750370951874963)
    ·
      refine ⟨259127363089125556427812445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172751575392750370951874963 259127363089125556427812445)
      ·
        refine ⟨97172761158422083660429667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259127363089125556427812445 97172761158422083660429667)
        ·
          refine ⟨145759141737633125490644501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97172761158422083660429667 145759141737633125490644501)
          ·
            refine ⟨6832459768951552757373961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145759141737633125490644501 6832459768951552757373961)
            ·
              refine ⟨5124344826713664568030471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6832459768951552757373961 5124344826713664568030471)
              ·
                refine ⟨7686517240070496852045707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124344826713664568030471 7686517240070496852045707)
                ·
                  refine ⟨11529775860105745278068561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686517240070496852045707 11529775860105745278068561)
                  ·
                    refine ⟨8647331895079308958551421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11529775860105745278068561 8647331895079308958551421)
                    ·
                      refine ⟨3242749460654740859456783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647331895079308958551421 3242749460654740859456783)
                      ·
                        rfl

theorem cell23_6315232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_6315232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315232 prefixEnd_6315232 := by exact prefixLift 6315232
  have htrace : WordTrace (prefixWord ++ tailWord_6315232) baseStart_6315232 baseEnd_6315232 := by
    simpa [prefixWord, tailWord_6315232, baseEnd_6315232] using wordTrace_append hprefix tailTrace_6315232
  have hstable : (prefixWord ++ tailWord_6315232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315232).length < 2 ^ (prefixWord ++ tailWord_6315232).sum := by decide
  have hdescent : baseEnd_6315232 < baseStart_6315232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315239 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6315239 : Nat := 118140960795 + 6315239 * 2 ^ 59
def prefixEnd_6315239 : Nat := 4983230072969 + 3 ^ 40 * 6315239 * 2
def baseEnd_6315239 : Nat := 1080917685006440777356417

theorem tailTrace_6315239 : CollatzResearch.WordTrace tailWord_6315239 prefixEnd_6315239 1080917685006440777356417 := by
  unfold tailWord_6315239
  simp only [CollatzResearch.WordTrace]
  refine ⟨230335689167975134798004771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153557126111983423198669847 230335689167975134798004771)
  ·
    refine ⟨345503533751962702197007157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230335689167975134798004771 345503533751962702197007157)
    ·
      refine ⟨32390956289246503330969421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345503533751962702197007157 32390956289246503330969421)
      ·
        refine ⟨12146608608467438749113533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32390956289246503330969421 12146608608467438749113533)
        ·
          refine ⟨4554978228175289530917575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12146608608467438749113533 4554978228175289530917575)
          ·
            refine ⟨6832467342262934296376363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554978228175289530917575 6832467342262934296376363)
            ·
              refine ⟨10248701013394401444564545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832467342262934296376363 10248701013394401444564545)
              ·
                refine ⟨7686525760045801083423409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248701013394401444564545 7686525760045801083423409)
                ·
                  refine ⟨5764894320034350812567557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686525760045801083423409 5764894320034350812567557)
                  ·
                    refine ⟨1080917685006440777356417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764894320034350812567557 1080917685006440777356417)
                    ·
                      rfl

theorem cell23_6315239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6315239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315239 prefixEnd_6315239 := by exact prefixLift 6315239
  have htrace : WordTrace (prefixWord ++ tailWord_6315239) baseStart_6315239 baseEnd_6315239 := by
    simpa [prefixWord, tailWord_6315239, baseEnd_6315239] using wordTrace_append hprefix tailTrace_6315239
  have hstable : (prefixWord ++ tailWord_6315239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315239).length < 2 ^ (prefixWord ++ tailWord_6315239).sum := by decide
  have hdescent : baseEnd_6315239 < baseStart_6315239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315262 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_6315262 : Nat := 118140960795 + 6315262 * 2 ^ 59
def prefixEnd_6315262 : Nat := 4983230072969 + 3 ^ 40 * 6315262 * 2
def baseEnd_6315262 : Nat := 3242764865074375742081645

theorem tailTrace_6315262 : CollatzResearch.WordTrace tailWord_6315262 prefixEnd_6315262 3242764865074375742081645 := by
  unfold tailWord_6315262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28792066005861476215761505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153557685364594539817394693 28792066005861476215761505)
  ·
    refine ⟨21594049504396107161821129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28792066005861476215761505 21594049504396107161821129)
    ·
      refine ⟨16195537128297080371365847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21594049504396107161821129 16195537128297080371365847)
      ·
        refine ⟨24293305692445620557048771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195537128297080371365847 24293305692445620557048771)
        ·
          refine ⟨36439958538668430835573157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293305692445620557048771 36439958538668430835573157)
          ·
            refine ⟨6832492226000330781669967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36439958538668430835573157 6832492226000330781669967)
            ·
              refine ⟨10248738339000496172504951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832492226000330781669967 10248738339000496172504951)
              ·
                refine ⟨15373107508500744258757427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248738339000496172504951 15373107508500744258757427)
                ·
                  refine ⟨23059661262751116388136141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15373107508500744258757427 23059661262751116388136141)
                  ·
                    refine ⟨8647372973531668645551053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23059661262751116388136141 8647372973531668645551053)
                    ·
                      refine ⟨3242764865074375742081645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647372973531668645551053 3242764865074375742081645)
                      ·
                        rfl

theorem cell23_6315262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_6315262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315262 prefixEnd_6315262 := by exact prefixLift 6315262
  have htrace : WordTrace (prefixWord ++ tailWord_6315262) baseStart_6315262 baseEnd_6315262 := by
    simpa [prefixWord, tailWord_6315262, baseEnd_6315262] using wordTrace_append hprefix tailTrace_6315262
  have hstable : (prefixWord ++ tailWord_6315262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315262).length < 2 ^ (prefixWord ++ tailWord_6315262).sum := by decide
  have hdescent : baseEnd_6315262 < baseStart_6315262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315288 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6315288 : Nat := 118140960795 + 6315288 * 2 ^ 59
def prefixEnd_6315288 : Nat := 4983230072969 + 3 ^ 40 * 6315288 * 2
def baseEnd_6315288 : Nat := 3242778215571392640356525

theorem tailTrace_6315288 : CollatzResearch.WordTrace tailWord_6315288 prefixEnd_6315288 3242778215571392640356525 := by
  unfold tailWord_6315288
  simp only [CollatzResearch.WordTrace]
  refine ⟨115168738172398808083269259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153558317563198410777692345 115168738172398808083269259)
  ·
    refine ⟨172753107258598212124903889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115168738172398808083269259 172753107258598212124903889)
    ·
      refine ⟨129564830443948659093677917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172753107258598212124903889 129564830443948659093677917)
      ·
        refine ⟨48586811416480747160129219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129564830443948659093677917 48586811416480747160129219)
        ·
          refine ⟨72880217124721120740193829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48586811416480747160129219 72880217124721120740193829)
          ·
            refine ⟨13665040710885210138786343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72880217124721120740193829 13665040710885210138786343)
            ·
              refine ⟨20497561066327815208179515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13665040710885210138786343 20497561066327815208179515)
              ·
                refine ⟨30746341599491722812269273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20497561066327815208179515 30746341599491722812269273)
                ·
                  refine ⟨23059756199618792109201955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30746341599491722812269273 23059756199618792109201955)
                  ·
                    refine ⟨34589634299428188163802933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23059756199618792109201955 34589634299428188163802933)
                    ·
                      refine ⟨3242778215571392640356525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34589634299428188163802933 3242778215571392640356525)
                      ·
                        rfl

theorem cell23_6315288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6315288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315288 prefixEnd_6315288 := by exact prefixLift 6315288
  have htrace : WordTrace (prefixWord ++ tailWord_6315288) baseStart_6315288 baseEnd_6315288 := by
    simpa [prefixWord, tailWord_6315288, baseEnd_6315288] using wordTrace_append hprefix tailTrace_6315288
  have hstable : (prefixWord ++ tailWord_6315288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315288).length < 2 ^ (prefixWord ++ tailWord_6315288).sum := by decide
  have hdescent : baseEnd_6315288 < baseStart_6315288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315331 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_6315331 : Nat := 118140960795 + 6315331 * 2 ^ 59
def prefixEnd_6315331 : Nat := 4983230072969 + 3 ^ 40 * 6315331 * 2
def baseEnd_6315331 : Nat := 3242800295239535972118827

theorem tailTrace_6315331 : CollatzResearch.WordTrace tailWord_6315331 prefixEnd_6315331 3242800295239535972118827 := by
  unfold tailWord_6315331
  simp only [CollatzResearch.WordTrace]
  refine ⟨230339044683641834510353847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153559363122427889673569231 230339044683641834510353847)
  ·
    refine ⟨345508567025462751765530771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230339044683641834510353847 345508567025462751765530771)
    ·
      refine ⟨518262850538194127648296157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345508567025462751765530771 518262850538194127648296157)
      ·
        refine ⟨194348568951822797868111059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518262850538194127648296157 194348568951822797868111059)
        ·
          refine ⟨291522853427734196802166589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194348568951822797868111059 291522853427734196802166589)
          ·
            refine ⟨109321070035400323800812471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291522853427734196802166589 109321070035400323800812471)
            ·
              refine ⟨163981605053100485701218707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109321070035400323800812471 163981605053100485701218707)
              ·
                refine ⟨245972407579650728551828061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163981605053100485701218707 245972407579650728551828061)
                ·
                  refine ⟨92239652842369023206935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245972407579650728551828061 92239652842369023206935523)
                  ·
                    refine ⟨138359479263553534810403285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92239652842369023206935523 138359479263553534810403285)
                    ·
                      refine ⟨3242800295239535972118827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138359479263553534810403285 3242800295239535972118827)
                      ·
                        rfl

theorem cell23_6315331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_6315331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315331 prefixEnd_6315331 := by exact prefixLift 6315331
  have htrace : WordTrace (prefixWord ++ tailWord_6315331) baseStart_6315331 baseEnd_6315331 := by
    simpa [prefixWord, tailWord_6315331, baseEnd_6315331] using wordTrace_append hprefix tailTrace_6315331
  have hstable : (prefixWord ++ tailWord_6315331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315331).length < 2 ^ (prefixWord ++ tailWord_6315331).sum := by decide
  have hdescent : baseEnd_6315331 < baseStart_6315331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315348 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6315348 : Nat := 118140960795 + 6315348 * 2 ^ 59
def prefixEnd_6315348 : Nat := 4983230072969 + 3 ^ 40 * 6315348 * 2
def baseEnd_6315348 : Nat := 3242809024410662405606249

theorem tailTrace_6315348 : CollatzResearch.WordTrace tailWord_6315348 prefixEnd_6315348 3242809024410662405606249 := by
  unfold tailWord_6315348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115169832362290123206861349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153559776483053497609148465 115169832362290123206861349)
  ·
    refine ⟨21594343567929398101286503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115169832362290123206861349 21594343567929398101286503)
    ·
      refine ⟨32391515351894097151929755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21594343567929398101286503 32391515351894097151929755)
      ·
        refine ⟨48587273027841145727894633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32391515351894097151929755 48587273027841145727894633)
        ·
          refine ⟨36440454770880859295920975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48587273027841145727894633 36440454770880859295920975)
          ·
            refine ⟨54660682156321288943881463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36440454770880859295920975 54660682156321288943881463)
            ·
              refine ⟨81991023234481933415822195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54660682156321288943881463 81991023234481933415822195)
              ·
                refine ⟨122986534851722900123733293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81991023234481933415822195 122986534851722900123733293)
                ·
                  refine ⟨46119950569396087546399985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122986534851722900123733293 46119950569396087546399985)
                  ·
                    refine ⟨34589962927047065659799989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46119950569396087546399985 34589962927047065659799989)
                    ·
                      refine ⟨3242809024410662405606249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34589962927047065659799989 3242809024410662405606249)
                      ·
                        rfl

theorem cell23_6315348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6315348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315348 prefixEnd_6315348 := by exact prefixLift 6315348
  have htrace : WordTrace (prefixWord ++ tailWord_6315348) baseStart_6315348 baseEnd_6315348 := by
    simpa [prefixWord, tailWord_6315348, baseEnd_6315348] using wordTrace_append hprefix tailTrace_6315348
  have hstable : (prefixWord ++ tailWord_6315348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315348).length < 2 ^ (prefixWord ++ tailWord_6315348).sum := by decide
  have hdescent : baseEnd_6315348 < baseStart_6315348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315375 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 4, 2]
def baseStart_6315375 : Nat := 118140960795 + 6315375 * 2 ^ 59
def prefixEnd_6315375 : Nat := 4983230072969 + 3 ^ 40 * 6315375 * 2
def baseEnd_6315375 : Nat := 3242822888388333799968625

theorem tailTrace_6315375 : CollatzResearch.WordTrace tailWord_6315375 prefixEnd_6315375 3242822888388333799968625 := by
  unfold tailWord_6315375
  simp only [CollatzResearch.WordTrace]
  refine ⟨230340649495482430024955579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153560432996988286683303719 230340649495482430024955579)
  ·
    refine ⟨345510974243223645037433369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230340649495482430024955579 345510974243223645037433369)
    ·
      refine ⟨259133230682417733778075027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345510974243223645037433369 259133230682417733778075027)
      ·
        refine ⟨388699846023626600667112541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259133230682417733778075027 388699846023626600667112541)
        ·
          refine ⟨145762442258859975250167203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388699846023626600667112541 145762442258859975250167203)
          ·
            refine ⟨218643663388289962875250805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145762442258859975250167203 218643663388289962875250805)
            ·
              refine ⟨20497843442652184019554763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218643663388289962875250805 20497843442652184019554763)
              ·
                refine ⟨30746765163978276029332145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20497843442652184019554763 30746765163978276029332145)
                ·
                  refine ⟨23060073872983707021999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30746765163978276029332145 23060073872983707021999109)
                  ·
                    refine ⟨4323763851184445066624833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23060073872983707021999109 4323763851184445066624833)
                    ·
                      refine ⟨3242822888388333799968625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323763851184445066624833 3242822888388333799968625)
                      ·
                        rfl

theorem cell23_6315375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4, 2].length) (baseStart_6315375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315375 prefixEnd_6315375 := by exact prefixLift 6315375
  have htrace : WordTrace (prefixWord ++ tailWord_6315375) baseStart_6315375 baseEnd_6315375 := by
    simpa [prefixWord, tailWord_6315375, baseEnd_6315375] using wordTrace_append hprefix tailTrace_6315375
  have hstable : (prefixWord ++ tailWord_6315375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315375).length < 2 ^ (prefixWord ++ tailWord_6315375).sum := by decide
  have hdescent : baseEnd_6315375 < baseStart_6315375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315395 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3]
def baseStart_6315395 : Nat := 118140960795 + 6315395 * 2 ^ 59
def prefixEnd_6315395 : Nat := 4983230072969 + 3 ^ 40 * 6315395 * 2
def baseEnd_6315395 : Nat := 3242833158001423721718533

theorem tailTrace_6315395 : CollatzResearch.WordTrace tailWord_6315395 prefixEnd_6315395 3242833158001423721718533 := by
  unfold tailWord_6315395
  simp only [CollatzResearch.WordTrace]
  refine ⟨230341378955409973440683639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153560919303606648960455759 230341378955409973440683639)
  ·
    refine ⟨345512068433114960161025459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230341378955409973440683639 345512068433114960161025459)
    ·
      refine ⟨518268102649672440241538189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345512068433114960161025459 518268102649672440241538189)
      ·
        refine ⟨194350538493627165090576821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518268102649672440241538189 194350538493627165090576821)
        ·
          refine ⟨18220362983777546727241577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194350538493627165090576821 18220362983777546727241577)
          ·
            refine ⟨13665272237833160045431183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18220362983777546727241577 13665272237833160045431183)
            ·
              refine ⟨20497908356749740068146775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13665272237833160045431183 20497908356749740068146775)
              ·
                refine ⟨30746862535124610102220163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20497908356749740068146775 30746862535124610102220163)
                ·
                  refine ⟨46120293802686915153330245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30746862535124610102220163 46120293802686915153330245)
                  ·
                    refine ⟨8647555088003796591249421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46120293802686915153330245 8647555088003796591249421)
                    ·
                      refine ⟨3242833158001423721718533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647555088003796591249421 3242833158001423721718533)
                      ·
                        rfl

theorem cell23_6315395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_6315395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315395 prefixEnd_6315395 := by exact prefixLift 6315395
  have htrace : WordTrace (prefixWord ++ tailWord_6315395) baseStart_6315395 baseEnd_6315395 := by
    simpa [prefixWord, tailWord_6315395, baseEnd_6315395] using wordTrace_append hprefix tailTrace_6315395
  have hstable : (prefixWord ++ tailWord_6315395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315395).length < 2 ^ (prefixWord ++ tailWord_6315395).sum := by decide
  have hdescent : baseEnd_6315395 < baseStart_6315395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315418 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6315418 : Nat := 118140960795 + 6315418 * 2 ^ 59
def prefixEnd_6315418 : Nat := 4983230072969 + 3 ^ 40 * 6315418 * 2
def baseEnd_6315418 : Nat := 3242844968056477131730927

theorem tailTrace_6315418 : CollatzResearch.WordTrace tailWord_6315418 prefixEnd_6315418 3242844968056477131730927 := by
  unfold tailWord_6315418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585554458581662092192727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153561478556217765579180605 57585554458581662092192727)
  ·
    refine ⟨86378331687872493138289091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57585554458581662092192727 86378331687872493138289091)
    ·
      refine ⟨129567497531808739707433637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86378331687872493138289091 129567497531808739707433637)
      ·
        refine ⟨24293905787214138695143807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129567497531808739707433637 24293905787214138695143807)
        ·
          refine ⟨36440858680821208042715711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293905787214138695143807 36440858680821208042715711)
          ·
            refine ⟨54661288021231812064073567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36440858680821208042715711 54661288021231812064073567)
            ·
              refine ⟨81991932031847718096110351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54661288021231812064073567 81991932031847718096110351)
              ·
                refine ⟨122987898047771577144165527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81991932031847718096110351 122987898047771577144165527)
                ·
                  refine ⟨184481847071657365716248291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122987898047771577144165527 184481847071657365716248291)
                  ·
                    refine ⟨276722770607486048574372437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184481847071657365716248291 276722770607486048574372437)
                    ·
                      refine ⟨3242844968056477131730927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 276722770607486048574372437 3242844968056477131730927)
                      ·
                        rfl

theorem cell23_6315418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6315418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315418 prefixEnd_6315418 := by exact prefixLift 6315418
  have htrace : WordTrace (prefixWord ++ tailWord_6315418) baseStart_6315418 baseEnd_6315418 := by
    simpa [prefixWord, tailWord_6315418, baseEnd_6315418] using wordTrace_append hprefix tailTrace_6315418
  have hstable : (prefixWord ++ tailWord_6315418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315418).length < 2 ^ (prefixWord ++ tailWord_6315418).sum := by decide
  have hdescent : baseEnd_6315418 < baseStart_6315418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315459 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 1, 1, 3]
def baseStart_6315459 : Nat := 118140960795 + 6315459 * 2 ^ 59
def prefixEnd_6315459 : Nat := 4983230072969 + 3 ^ 40 * 6315459 * 2
def baseEnd_6315459 : Nat := 3242866020763311471318239

theorem tailTrace_6315459 : CollatzResearch.WordTrace tailWord_6315459 prefixEnd_6315459 3242866020763311471318239 := by
  unfold tailWord_6315459
  simp only [CollatzResearch.WordTrace]
  refine ⟨230343713227178112371013431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153562475484785408247342287 230343713227178112371013431)
  ·
    refine ⟨345515569840767168556520147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230343713227178112371013431 345515569840767168556520147)
    ·
      refine ⟨518273354761150752834780221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345515569840767168556520147 518273354761150752834780221)
      ·
        refine ⟨194352508035431532313042583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518273354761150752834780221 194352508035431532313042583)
        ·
          refine ⟨291528762053147298469563875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194352508035431532313042583 291528762053147298469563875)
          ·
            refine ⟨437293143079720947704345813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291528762053147298469563875 437293143079720947704345813)
            ·
              refine ⟨10249058040930959711820605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 437293143079720947704345813 10249058040930959711820605)
              ·
                refine ⟨3843396765349109891932727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10249058040930959711820605 3843396765349109891932727)
                ·
                  refine ⟨5765095148023664837899091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843396765349109891932727 5765095148023664837899091)
                  ·
                    refine ⟨8647642722035497256848637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765095148023664837899091 8647642722035497256848637)
                    ·
                      refine ⟨3242866020763311471318239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647642722035497256848637 3242866020763311471318239)
                      ·
                        rfl

theorem cell23_6315459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_6315459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315459 prefixEnd_6315459 := by exact prefixLift 6315459
  have htrace : WordTrace (prefixWord ++ tailWord_6315459) baseStart_6315459 baseEnd_6315459 := by
    simpa [prefixWord, tailWord_6315459, baseEnd_6315459] using wordTrace_append hprefix tailTrace_6315459
  have hstable : (prefixWord ++ tailWord_6315459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315459).length < 2 ^ (prefixWord ++ tailWord_6315459).sum := by decide
  have hdescent : baseEnd_6315459 < baseStart_6315459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315476 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6315476 : Nat := 118140960795 + 6315476 * 2 ^ 59
def prefixEnd_6315476 : Nat := 4983230072969 + 3 ^ 40 * 6315476 * 2
def baseEnd_6315476 : Nat := 3242874749934437904805661

theorem tailTrace_6315476 : CollatzResearch.WordTrace tailWord_6315476 prefixEnd_6315476 3242874749934437904805661 := by
  unfold tailWord_6315476
  simp only [CollatzResearch.WordTrace]
  refine ⟨115172166634058262137191141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153562888845411016182921521 115172166634058262137191141)
  ·
    refine ⟨21594781243885924150723339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115172166634058262137191141 21594781243885924150723339)
    ·
      refine ⟨32392171865828886226085009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21594781243885924150723339 32392171865828886226085009)
      ·
        refine ⟨24294128899371664669563757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32392171865828886226085009 24294128899371664669563757)
        ·
          refine ⟨9110298337264374251086409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24294128899371664669563757 9110298337264374251086409)
          ·
            refine ⟨6832723752948280688314807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110298337264374251086409 6832723752948280688314807)
            ·
              refine ⟨10249085629422421032472211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832723752948280688314807 10249085629422421032472211)
              ·
                refine ⟨15373628444133631548708317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249085629422421032472211 15373628444133631548708317)
                ·
                  refine ⟨5765110666550111830765619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15373628444133631548708317 5765110666550111830765619)
                  ·
                    refine ⟨8647665999825167746148429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765110666550111830765619 8647665999825167746148429)
                    ·
                      refine ⟨3242874749934437904805661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647665999825167746148429 3242874749934437904805661)
                      ·
                        rfl

theorem cell23_6315476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6315476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315476 prefixEnd_6315476 := by exact prefixLift 6315476
  have htrace : WordTrace (prefixWord ++ tailWord_6315476) baseStart_6315476 baseEnd_6315476 := by
    simpa [prefixWord, tailWord_6315476, baseEnd_6315476] using wordTrace_append hprefix tailTrace_6315476
  have hstable : (prefixWord ++ tailWord_6315476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315476).length < 2 ^ (prefixWord ++ tailWord_6315476).sum := by decide
  have hdescent : baseEnd_6315476 < baseStart_6315476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315495 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6315495 : Nat := 118140960795 + 6315495 * 2 ^ 59
def prefixEnd_6315495 : Nat := 4983230072969 + 3 ^ 40 * 6315495 * 2
def baseEnd_6315495 : Nat := 3242884506066873330468073

theorem tailTrace_6315495 : CollatzResearch.WordTrace tailWord_6315495 prefixEnd_6315495 3242884506066873330468073 := by
  unfold tailWord_6315495
  simp only [CollatzResearch.WordTrace]
  refine ⟨230345026255047690519323939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153563350836698460346215959 230345026255047690519323939)
  ·
    refine ⟨345517539382571535778985909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230345026255047690519323939 345517539382571535778985909)
    ·
      refine ⟨32392269317116081479279929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345517539382571535778985909 32392269317116081479279929)
      ·
        refine ⟨24294201987837061109459947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32392269317116081479279929 24294201987837061109459947)
        ·
          refine ⟨36441302981755591664189921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24294201987837061109459947 36441302981755591664189921)
          ·
            refine ⟨27330977236316693748142441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36441302981755591664189921 27330977236316693748142441)
            ·
              refine ⟨20498232927237520311106831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27330977236316693748142441 20498232927237520311106831)
              ·
                refine ⟨30747349390856280466660247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20498232927237520311106831 30747349390856280466660247)
                ·
                  refine ⟨46121024086284420699990371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30747349390856280466660247 46121024086284420699990371)
                  ·
                    refine ⟨69181536129426631049985557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46121024086284420699990371 69181536129426631049985557)
                    ·
                      refine ⟨3242884506066873330468073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69181536129426631049985557 3242884506066873330468073)
                      ·
                        rfl

theorem cell23_6315495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6315495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315495 prefixEnd_6315495 := by exact prefixLift 6315495
  have htrace : WordTrace (prefixWord ++ tailWord_6315495) baseStart_6315495 baseEnd_6315495 := by
    simpa [prefixWord, tailWord_6315495, baseEnd_6315495] using wordTrace_append hprefix tailTrace_6315495
  have hstable : (prefixWord ++ tailWord_6315495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315495).length < 2 ^ (prefixWord ++ tailWord_6315495).sum := by decide
  have hdescent : baseEnd_6315495 < baseStart_6315495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315502 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_6315502 : Nat := 118140960795 + 6315502 * 2 ^ 59
def prefixEnd_6315502 : Nat := 4983230072969 + 3 ^ 40 * 6315502 * 2
def baseEnd_6315502 : Nat := 3242888100431454803080541

theorem tailTrace_6315502 : CollatzResearch.WordTrace tailWord_6315502 prefixEnd_6315502 3242888100431454803080541 := by
  unfold tailWord_6315502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793160195752791339353595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153563521044014887143219173 28793160195752791339353595)
  ·
    refine ⟨43189740293629187009030393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28793160195752791339353595 43189740293629187009030393)
    ·
      refine ⟨32392305220221890256772795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43189740293629187009030393 32392305220221890256772795)
      ·
        refine ⟨48588457830332835385159193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32392305220221890256772795 48588457830332835385159193)
        ·
          refine ⟨36441343372749626538869395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48588457830332835385159193 36441343372749626538869395)
          ·
            refine ⟨54662015059124439808304093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36441343372749626538869395 54662015059124439808304093)
            ·
              refine ⟨20498255647171664928114035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54662015059124439808304093 20498255647171664928114035)
              ·
                refine ⟨30747383470757497392171053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20498255647171664928114035 30747383470757497392171053)
                ·
                  refine ⟨11530268801534061522064145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30747383470757497392171053 11530268801534061522064145)
                  ·
                    refine ⟨8647701601150546141548109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11530268801534061522064145 8647701601150546141548109)
                    ·
                      refine ⟨3242888100431454803080541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647701601150546141548109 3242888100431454803080541)
                      ·
                        rfl

theorem cell23_6315502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_6315502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315502 prefixEnd_6315502 := by exact prefixLift 6315502
  have htrace : WordTrace (prefixWord ++ tailWord_6315502) baseStart_6315502 baseEnd_6315502 := by
    simpa [prefixWord, tailWord_6315502, baseEnd_6315502] using wordTrace_append hprefix tailTrace_6315502
  have hstable : (prefixWord ++ tailWord_6315502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315502).length < 2 ^ (prefixWord ++ tailWord_6315502).sum := by decide
  have hdescent : baseEnd_6315502 < baseStart_6315502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315515 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3]
def baseStart_6315515 : Nat := 118140960795 + 6315515 * 2 ^ 59
def prefixEnd_6315515 : Nat := 4983230072969 + 3 ^ 40 * 6315515 * 2
def baseEnd_6315515 : Nat := 3242894775679963252217981

theorem tailTrace_6315515 : CollatzResearch.WordTrace tailWord_6315515 prefixEnd_6315515 3242894775679963252217981 := by
  unfold tailWord_6315515
  simp only [CollatzResearch.WordTrace]
  refine ⟨230345755714975233935051999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153563837143316822623367999 230345755714975233935051999)
  ·
    refine ⟨345518633572462850902577999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230345755714975233935051999 345518633572462850902577999)
    ·
      refine ⟨518277950358694276353866999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345518633572462850902577999 518277950358694276353866999)
      ·
        refine ⟨777416925538041414530800499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518277950358694276353866999 777416925538041414530800499)
        ·
          refine ⟨1166125388307062121796200749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777416925538041414530800499 1166125388307062121796200749)
          ·
            refine ⟨437297020615148295673575281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1166125388307062121796200749 437297020615148295673575281)
            ·
              refine ⟨327972765461361221755181461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437297020615148295673575281 327972765461361221755181461)
              ·
                refine ⟨15373723381001307269774131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327972765461361221755181461 15373723381001307269774131)
                ·
                  refine ⟨23060585071501960904661197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15373723381001307269774131 23060585071501960904661197)
                  ·
                    refine ⟨8647719401813235339247949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23060585071501960904661197 8647719401813235339247949)
                    ·
                      refine ⟨3242894775679963252217981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647719401813235339247949 3242894775679963252217981)
                      ·
                        rfl

theorem cell23_6315515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].length) (baseStart_6315515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315515 prefixEnd_6315515 := by exact prefixLift 6315515
  have htrace : WordTrace (prefixWord ++ tailWord_6315515) baseStart_6315515 baseEnd_6315515 := by
    simpa [prefixWord, tailWord_6315515, baseEnd_6315515] using wordTrace_append hprefix tailTrace_6315515
  have hstable : (prefixWord ++ tailWord_6315515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315515).length < 2 ^ (prefixWord ++ tailWord_6315515).sum := by decide
  have hdescent : baseEnd_6315515 < baseStart_6315515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315549 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_6315549 : Nat := 118140960795 + 6315549 * 2 ^ 59
def prefixEnd_6315549 : Nat := 4983230072969 + 3 ^ 40 * 6315549 * 2
def baseEnd_6315549 : Nat := 3242912234022216119192825

theorem tailTrace_6315549 : CollatzResearch.WordTrace tailWord_6315549 prefixEnd_6315549 3242912234022216119192825 := by
  unfold tailWord_6315549
  simp only [CollatzResearch.WordTrace]
  refine ⟨230346995796852057741789701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153564663864568038494526467 230346995796852057741789701)
  ·
    refine ⟨43190061711909760826585569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230346995796852057741789701 43190061711909760826585569)
    ·
      refine ⟨32392546283932320619939177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43190061711909760826585569 32392546283932320619939177)
      ·
        refine ⟨24294409712949240464954383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32392546283932320619939177 24294409712949240464954383)
        ·
          refine ⟨36441614569423860697431575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24294409712949240464954383 36441614569423860697431575)
          ·
            refine ⟨54662421854135791046147363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36441614569423860697431575 54662421854135791046147363)
            ·
              refine ⟨81993632781203686569221045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54662421854135791046147363 81993632781203686569221045)
              ·
                refine ⟨7686903073237845615864473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81993632781203686569221045 7686903073237845615864473)
                ·
                  refine ⟨5765177304928384211898355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686903073237845615864473 5765177304928384211898355)
                  ·
                    refine ⟨8647765957392576317847533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765177304928384211898355 8647765957392576317847533)
                    ·
                      refine ⟨3242912234022216119192825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8647765957392576317847533 3242912234022216119192825)
                      ·
                        rfl

theorem cell23_6315549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_6315549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315549 prefixEnd_6315549 := by exact prefixLift 6315549
  have htrace : WordTrace (prefixWord ++ tailWord_6315549) baseStart_6315549 baseEnd_6315549 := by
    simpa [prefixWord, tailWord_6315549, baseEnd_6315549] using wordTrace_append hprefix tailTrace_6315549
  have hstable : (prefixWord ++ tailWord_6315549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315549).length < 2 ^ (prefixWord ++ tailWord_6315549).sum := by decide
  have hdescent : baseEnd_6315549 < baseStart_6315549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315576 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_6315576 : Nat := 118140960795 + 6315576 * 2 ^ 59
def prefixEnd_6315576 : Nat := 4983230072969 + 3 ^ 40 * 6315576 * 2
def baseEnd_6315576 : Nat := 3242926097999887513555201

theorem tailTrace_6315576 : CollatzResearch.WordTrace tailWord_6315576 prefixEnd_6315576 3242926097999887513555201 := by
  unfold tailWord_6315576
  simp only [CollatzResearch.WordTrace]
  refine ⟨115173990283877120676511291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153565320378502827568681721 115173990283877120676511291)
  ·
    refine ⟨172760985425815681014766937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115173990283877120676511291 172760985425815681014766937)
    ·
      refine ⟨129570739069361760761075203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172760985425815681014766937 129570739069361760761075203)
      ·
        refine ⟨194356108604042641141612805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129570739069361760761075203 194356108604042641141612805)
        ·
          refine ⟨36441770363257995214052401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194356108604042641141612805 36441770363257995214052401)
          ·
            refine ⟨27331327772443496410539301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36441770363257995214052401 27331327772443496410539301)
            ·
              refine ⟨5124623957333155576976119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27331327772443496410539301 5124623957333155576976119)
              ·
                refine ⟨7686935935999733365464179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124623957333155576976119 7686935935999733365464179)
                ·
                  refine ⟨11530403903999600048196269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686935935999733365464179 11530403903999600048196269)
                  ·
                    refine ⟨4323901463999850018073601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11530403903999600048196269 4323901463999850018073601)
                    ·
                      refine ⟨3242926097999887513555201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323901463999850018073601 3242926097999887513555201)
                      ·
                        rfl

theorem cell23_6315576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_6315576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315576 prefixEnd_6315576 := by exact prefixLift 6315576
  have htrace : WordTrace (prefixWord ++ tailWord_6315576) baseStart_6315576 baseEnd_6315576 := by
    simpa [prefixWord, tailWord_6315576, baseEnd_6315576] using wordTrace_append hprefix tailTrace_6315576
  have hstable : (prefixWord ++ tailWord_6315576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315576).length < 2 ^ (prefixWord ++ tailWord_6315576).sum := by decide
  have hdescent : baseEnd_6315576 < baseStart_6315576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315589 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_6315589 : Nat := 118140960795 + 6315589 * 2 ^ 59
def prefixEnd_6315589 : Nat := 4983230072969 + 3 ^ 40 * 6315589 * 2
def baseEnd_6315589 : Nat := 3242932773248395962692641

theorem tailTrace_6315589 : CollatzResearch.WordTrace tailWord_6315589 prefixEnd_6315589 3242932773248395962692641 := by
  unfold tailWord_6315589
  simp only [CollatzResearch.WordTrace]
  refine ⟨230348454716707144573245821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153565636477804763048830547 230348454716707144573245821)
  ·
    refine ⟨86380670518765179214967183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230348454716707144573245821 86380670518765179214967183)
    ·
      refine ⟨129571005778147768822450775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86380670518765179214967183 129571005778147768822450775)
      ·
        refine ⟨194356508667221653233676163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129571005778147768822450775 194356508667221653233676163)
        ·
          refine ⟨291534763000832479850514245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194356508667221653233676163 291534763000832479850514245)
          ·
            refine ⟨54662768062656089971971421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291534763000832479850514245 54662768062656089971971421)
            ·
              refine ⟨20498538023496033739489283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54662768062656089971971421 20498538023496033739489283)
              ·
                refine ⟨30747807035244050609233925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20498538023496033739489283 30747807035244050609233925)
                ·
                  refine ⟨5765213819108259489231361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30747807035244050609233925 5765213819108259489231361)
                  ·
                    refine ⟨4323910364331194616923521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5765213819108259489231361 4323910364331194616923521)
                    ·
                      refine ⟨3242932773248395962692641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4323910364331194616923521 3242932773248395962692641)
                      ·
                        rfl

theorem cell23_6315589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_6315589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315589 prefixEnd_6315589 := by exact prefixLift 6315589
  have htrace : WordTrace (prefixWord ++ tailWord_6315589) baseStart_6315589 baseEnd_6315589 := by
    simpa [prefixWord, tailWord_6315589, baseEnd_6315589] using wordTrace_append hprefix tailTrace_6315589
  have hstable : (prefixWord ++ tailWord_6315589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315589).length < 2 ^ (prefixWord ++ tailWord_6315589).sum := by decide
  have hdescent : baseEnd_6315589 < baseStart_6315589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315602 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6315602 : Nat := 118140960795 + 6315602 * 2 ^ 59
def prefixEnd_6315602 : Nat := 4983230072969 + 3 ^ 40 * 6315602 * 2
def baseEnd_6315602 : Nat := 3242939448496904411830081

theorem tailTrace_6315602 : CollatzResearch.WordTrace tailWord_6315602 prefixEnd_6315602 3242939448496904411830081 := by
  unfold tailWord_6315602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57587232216415011948367265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153565952577106698528979373 57587232216415011948367265)
  ·
    refine ⟨43190424162311258961275449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57587232216415011948367265 43190424162311258961275449)
    ·
      refine ⟨32392818121733444220956587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43190424162311258961275449 32392818121733444220956587)
      ·
        refine ⟨48589227182600166331434881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32392818121733444220956587 48589227182600166331434881)
        ·
          refine ⟨36441920386950124748576161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48589227182600166331434881 36441920386950124748576161)
          ·
            refine ⟨27331440290212593561432121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36441920386950124748576161 27331440290212593561432121)
            ·
              refine ⟨20498580217659445171074091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27331440290212593561432121 20498580217659445171074091)
              ·
                refine ⟨30747870326489167756611137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20498580217659445171074091 30747870326489167756611137)
                ·
                  refine ⟨23060902744866875817458353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30747870326489167756611137 23060902744866875817458353)
                  ·
                    refine ⟨17295677058650156863093765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23060902744866875817458353 17295677058650156863093765)
                    ·
                      refine ⟨3242939448496904411830081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17295677058650156863093765 3242939448496904411830081)
                      ·
                        rfl

theorem cell23_6315602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6315602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315602 prefixEnd_6315602 := by exact prefixLift 6315602
  have htrace : WordTrace (prefixWord ++ tailWord_6315602) baseStart_6315602 baseEnd_6315602 := by
    simpa [prefixWord, tailWord_6315602, baseEnd_6315602] using wordTrace_append hprefix tailTrace_6315602
  have hstable : (prefixWord ++ tailWord_6315602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315602).length < 2 ^ (prefixWord ++ tailWord_6315602).sum := by decide
  have hdescent : baseEnd_6315602 < baseStart_6315602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315612 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 7]
def baseStart_6315612 : Nat := 118140960795 + 6315612 * 2 ^ 59
def prefixEnd_6315612 : Nat := 4983230072969 + 3 ^ 40 * 6315612 * 2
def baseEnd_6315612 : Nat := 360327175922605485856115

theorem tailTrace_6315612 : CollatzResearch.WordTrace tailWord_6315612 prefixEnd_6315612 360327175922605485856115 := by
  unfold tailWord_6315612
  simp only [CollatzResearch.WordTrace]
  refine ⟨115174646797811909750666545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153566195730415879667555393 115174646797811909750666545)
  ·
    refine ⟨86380985098358932312999909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115174646797811909750666545 86380985098358932312999909)
    ·
      refine ⟨16196434705942299808687483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86380985098358932312999909 16196434705942299808687483)
      ·
        refine ⟨24294652058913449713031225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16196434705942299808687483 24294652058913449713031225)
        ·
          refine ⟨18220989044185087284773419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24294652058913449713031225 18220989044185087284773419)
          ·
            refine ⟨27331483566277630927160129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18220989044185087284773419 27331483566277630927160129)
            ·
              refine ⟨20498612674708223195370097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27331483566277630927160129 20498612674708223195370097)
              ·
                refine ⟨15373959506031167396527573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20498612674708223195370097 15373959506031167396527573)
                ·
                  refine ⟨360327175922605485856115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15373959506031167396527573 360327175922605485856115)
                  ·
                    rfl

theorem cell23_6315612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_6315612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315612 prefixEnd_6315612 := by exact prefixLift 6315612
  have htrace : WordTrace (prefixWord ++ tailWord_6315612) baseStart_6315612 baseEnd_6315612 := by
    simpa [prefixWord, tailWord_6315612, baseEnd_6315612] using wordTrace_append hprefix tailTrace_6315612
  have hstable : (prefixWord ++ tailWord_6315612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315612).length < 2 ^ (prefixWord ++ tailWord_6315612).sum := by decide
  have hdescent : baseEnd_6315612 < baseStart_6315612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315625 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_6315625 : Nat := 118140960795 + 6315625 * 2 ^ 59
def prefixEnd_6315625 : Nat := 4983230072969 + 3 ^ 40 * 6315625 * 2
def baseEnd_6315625 : Nat := 1080983752850652607280825

theorem tailTrace_6315625 : CollatzResearch.WordTrace tailWord_6315625 prefixEnd_6315625 1080983752850652607280825 := by
  unfold tailWord_6315625
  simp only [CollatzResearch.WordTrace]
  refine ⟨230349767744576722721556329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153566511829717815147704219 230349767744576722721556329)
  ·
    refine ⟨172762325808432542041167247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230349767744576722721556329 172762325808432542041167247)
    ·
      refine ⟨259143488712648813061750871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172762325808432542041167247 259143488712648813061750871)
      ·
        refine ⟨388715233068973219592626307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259143488712648813061750871 388715233068973219592626307)
        ·
          refine ⟨583072849603459829388939461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388715233068973219592626307 583072849603459829388939461)
          ·
            refine ⟨109326159300648718010426149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583072849603459829388939461 109326159300648718010426149)
            ·
              refine ⟨20498654868871634626954903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109326159300648718010426149 20498654868871634626954903)
              ·
                refine ⟨30747982303307451940432355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20498654868871634626954903 30747982303307451940432355)
                ·
                  refine ⟨46121973454961177910648533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30747982303307451940432355 46121973454961177910648533)
                  ·
                    refine ⟨1080983752850652607280825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46121973454961177910648533 1080983752850652607280825)
                    ·
                      rfl

theorem cell23_6315625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_6315625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315625 prefixEnd_6315625 := by exact prefixLift 6315625
  have htrace : WordTrace (prefixWord ++ tailWord_6315625) baseStart_6315625 baseEnd_6315625 := by
    simpa [prefixWord, tailWord_6315625, baseEnd_6315625] using wordTrace_append hprefix tailTrace_6315625
  have hstable : (prefixWord ++ tailWord_6315625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315625).length < 2 ^ (prefixWord ++ tailWord_6315625).sum := by decide
  have hdescent : baseEnd_6315625 < baseStart_6315625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315685 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 10]
def baseStart_6315685 : Nat := 118140960795 + 6315685 * 2 ^ 59
def prefixEnd_6315685 : Nat := 4983230072969 + 3 ^ 40 * 6315685 * 2
def baseEnd_6315685 : Nat := 360331340821247509676911

theorem tailTrace_6315685 : CollatzResearch.WordTrace tailWord_6315685 prefixEnd_6315685 360331340821247509676911 := by
  unfold tailWord_6315685
  simp only [CollatzResearch.WordTrace]
  refine ⟨230351956124359352968740509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153567970749572901979160339 230351956124359352968740509)
  ·
    refine ⟨86381983546634757363277691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230351956124359352968740509 86381983546634757363277691)
    ·
      refine ⟨129572975319952136044916537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86381983546634757363277691 129572975319952136044916537)
      ·
        refine ⟨97179731489964102033687403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129572975319952136044916537 97179731489964102033687403)
        ·
          refine ⟨145769597234946153050531105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97179731489964102033687403 145769597234946153050531105)
          ·
            refine ⟨109327197926209614787898329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145769597234946153050531105 109327197926209614787898329)
            ·
              refine ⟨81995398444657211090923747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109327197926209614787898329 81995398444657211090923747)
              ·
                refine ⟨122993097666985816636385621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81995398444657211090923747 122993097666985816636385621)
                ·
                  refine ⟨360331340821247509676911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122993097666985816636385621 360331340821247509676911)
                  ·
                    rfl

theorem cell23_6315685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_6315685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315685 prefixEnd_6315685 := by exact prefixLift 6315685
  have htrace : WordTrace (prefixWord ++ tailWord_6315685) baseStart_6315685 baseEnd_6315685 := by
    simpa [prefixWord, tailWord_6315685, baseEnd_6315685] using wordTrace_append hprefix tailTrace_6315685
  have hstable : (prefixWord ++ tailWord_6315685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315685).length < 2 ^ (prefixWord ++ tailWord_6315685).sum := by decide
  have hdescent : baseEnd_6315685 < baseStart_6315685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315706 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_6315706 : Nat := 118140960795 + 6315706 * 2 ^ 59
def prefixEnd_6315706 : Nat := 4983230072969 + 3 ^ 40 * 6315706 * 2
def baseEnd_6315706 : Nat := 1080997616828324001643201

theorem tailTrace_6315706 : CollatzResearch.WordTrace tailWord_6315706 prefixEnd_6315706 1080997616828324001643201 := by
  unfold tailWord_6315706
  simp only [CollatzResearch.WordTrace]
  refine ⟨57588180514320818388813743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153568481371522182370169981 57588180514320818388813743)
  ·
    refine ⟨86382270771481227583220615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57588180514320818388813743 86382270771481227583220615)
    ·
      refine ⟨129573406157221841374830923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86382270771481227583220615 129573406157221841374830923)
      ·
        refine ⟨194360109235832762062246385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129573406157221841374830923 194360109235832762062246385)
        ·
          refine ⟨145770081926874571546684789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194360109235832762062246385 145770081926874571546684789)
          ·
            refine ⟨13665945180644491082501699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145770081926874571546684789 13665945180644491082501699)
            ·
              refine ⟨20498917770966736623752549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13665945180644491082501699 20498917770966736623752549)
              ·
                refine ⟨3843547082056263116953603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20498917770966736623752549 3843547082056263116953603)
                ·
                  refine ⟨5765320623084394675430405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843547082056263116953603 5765320623084394675430405)
                  ·
                    refine ⟨1080997616828324001643201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765320623084394675430405 1080997616828324001643201)
                    ·
                      rfl

theorem cell23_6315706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_6315706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315706 prefixEnd_6315706 := by exact prefixLift 6315706
  have htrace : WordTrace (prefixWord ++ tailWord_6315706) baseStart_6315706 baseEnd_6315706 := by
    simpa [prefixWord, tailWord_6315706, baseEnd_6315706] using wordTrace_append hprefix tailTrace_6315706
  have hstable : (prefixWord ++ tailWord_6315706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315706).length < 2 ^ (prefixWord ++ tailWord_6315706).sum := by decide
  have hdescent : baseEnd_6315706 < baseStart_6315706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315729 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_6315729 : Nat := 118140960795 + 6315729 * 2 ^ 59
def prefixEnd_6315729 : Nat := 4983230072969 + 3 ^ 40 * 6315729 * 2
def baseEnd_6315729 : Nat := 3243004660540025414941997

theorem tailTrace_6315729 : CollatzResearch.WordTrace tailWord_6315729 prefixEnd_6315729 3243004660540025414941997 := by
  unfold tailWord_6315729
  simp only [CollatzResearch.WordTrace]
  refine ⟨230353560936199948483342241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153569040624133298988894827 230353560936199948483342241)
  ·
    refine ⟨172765170702149961362506681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230353560936199948483342241 172765170702149961362506681)
    ·
      refine ⟨129573878026612471021880011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172765170702149961362506681 129573878026612471021880011)
      ·
        refine ⟨194360817039918706532820017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129573878026612471021880011 194360817039918706532820017)
        ·
          refine ⟨145770612779939029899615013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194360817039918706532820017 145770612779939029899615013)
          ·
            refine ⟨27331989896238568106177815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145770612779939029899615013 27331989896238568106177815)
            ·
              refine ⟨40997984844357852159266723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27331989896238568106177815 40997984844357852159266723)
              ·
                refine ⟨61496977266536778238900085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40997984844357852159266723 61496977266536778238900085)
                ·
                  refine ⟨5765341618737822959896883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61496977266536778238900085 5765341618737822959896883)
                  ·
                    refine ⟨8648012428106734439845325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765341618737822959896883 8648012428106734439845325)
                    ·
                      refine ⟨3243004660540025414941997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8648012428106734439845325 3243004660540025414941997)
                      ·
                        rfl

theorem cell23_6315729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_6315729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315729 prefixEnd_6315729 := by exact prefixLift 6315729
  have htrace : WordTrace (prefixWord ++ tailWord_6315729) baseStart_6315729 baseEnd_6315729 := by
    simpa [prefixWord, tailWord_6315729, baseEnd_6315729] using wordTrace_append hprefix tailTrace_6315729
  have hstable : (prefixWord ++ tailWord_6315729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315729).length < 2 ^ (prefixWord ++ tailWord_6315729).sum := by decide
  have hdescent : baseEnd_6315729 < baseStart_6315729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315740 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6315740 : Nat := 118140960795 + 6315740 * 2 ^ 59
def prefixEnd_6315740 : Nat := 4983230072969 + 3 ^ 40 * 6315740 * 2
def baseEnd_6315740 : Nat := 1081003436275741623968149

theorem tailTrace_6315740 : CollatzResearch.WordTrace tailWord_6315740 prefixEnd_6315740 1081003436275741623968149 := by
  unfold tailWord_6315740
  simp only [CollatzResearch.WordTrace]
  refine ⟨115176981069580048680996337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153569308092773398241328449 115176981069580048680996337)
  ·
    refine ⟨86382735802185036510747253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115176981069580048680996337 86382735802185036510747253)
    ·
      refine ⟨8098381481454847172882555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86382735802185036510747253 8098381481454847172882555)
      ·
        refine ⟨12147572222182270759323833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098381481454847172882555 12147572222182270759323833)
        ·
          refine ⟨9110679166636703069492875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12147572222182270759323833 9110679166636703069492875)
          ·
            refine ⟨13666018749955054604239313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9110679166636703069492875 13666018749955054604239313)
            ·
              refine ⟨10249514062466290953179485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13666018749955054604239313 10249514062466290953179485)
              ·
                refine ⟨3843567773424859107442307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10249514062466290953179485 3843567773424859107442307)
                ·
                  refine ⟨5765351660137288661163461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843567773424859107442307 5765351660137288661163461)
                  ·
                    refine ⟨1081003436275741623968149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765351660137288661163461 1081003436275741623968149)
                    ·
                      rfl

theorem cell23_6315740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6315740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315740 prefixEnd_6315740 := by exact prefixLift 6315740
  have htrace : WordTrace (prefixWord ++ tailWord_6315740) baseStart_6315740 baseEnd_6315740 := by
    simpa [prefixWord, tailWord_6315740, baseEnd_6315740] using wordTrace_append hprefix tailTrace_6315740
  have hstable : (prefixWord ++ tailWord_6315740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315740).length < 2 ^ (prefixWord ++ tailWord_6315740).sum := by decide
  have hdescent : baseEnd_6315740 < baseStart_6315740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315749 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_6315749 : Nat := 118140960795 + 6315749 * 2 ^ 59
def prefixEnd_6315749 : Nat := 4983230072969 + 3 ^ 40 * 6315749 * 2
def baseEnd_6315749 : Nat := 1081004976717705112230635

theorem tailTrace_6315749 : CollatzResearch.WordTrace tailWord_6315749 prefixEnd_6315749 1081004976717705112230635 := by
  unfold tailWord_6315749
  simp only [CollatzResearch.WordTrace]
  refine ⟨230354290396127491899070301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153569526930751661266046867 230354290396127491899070301)
  ·
    refine ⟨86382858898547809462151363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230354290396127491899070301 86382858898547809462151363)
    ·
      refine ⟨129574288347821714193227045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86382858898547809462151363 129574288347821714193227045)
      ·
        refine ⟨24295179065216571411230071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129574288347821714193227045 24295179065216571411230071)
        ·
          refine ⟨36442768597824857116845107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24295179065216571411230071 36442768597824857116845107)
          ·
            refine ⟨54664152896737285675267661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36442768597824857116845107 54664152896737285675267661)
            ·
              refine ⟨20499057336276482128225373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54664152896737285675267661 20499057336276482128225373)
              ·
                refine ⟨7687146501103680798084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20499057336276482128225373 7687146501103680798084515)
                ·
                  refine ⟨11530719751655521197126773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7687146501103680798084515 11530719751655521197126773)
                  ·
                    refine ⟨1081004976717705112230635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11530719751655521197126773 1081004976717705112230635)
                    ·
                      rfl

theorem cell23_6315749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_6315749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315749 prefixEnd_6315749 := by exact prefixLift 6315749
  have htrace : WordTrace (prefixWord ++ tailWord_6315749) baseStart_6315749 baseEnd_6315749 := by
    simpa [prefixWord, tailWord_6315749, baseEnd_6315749] using wordTrace_append hprefix tailTrace_6315749
  have hstable : (prefixWord ++ tailWord_6315749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315749).length < 2 ^ (prefixWord ++ tailWord_6315749).sum := by decide
  have hdescent : baseEnd_6315749 < baseStart_6315749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315779 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 2, 4]
def baseStart_6315779 : Nat := 118140960795 + 6315779 * 2 ^ 59
def prefixEnd_6315779 : Nat := 4983230072969 + 3 ^ 40 * 6315779 * 2
def baseEnd_6315779 : Nat := 1081010111524250073105589

theorem tailTrace_6315779 : CollatzResearch.WordTrace tailWord_6315779 prefixEnd_6315779 1081010111524250073105589 := by
  unfold tailWord_6315779
  simp only [CollatzResearch.WordTrace]
  refine ⟨230355384586018807022662391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153570256390679204681774927 230355384586018807022662391)
  ·
    refine ⟨345533076879028210533993587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230355384586018807022662391 345533076879028210533993587)
    ·
      refine ⟨518299615318542315800990381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345533076879028210533993587 518299615318542315800990381)
      ·
        refine ⟨194362355744453368425371393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518299615318542315800990381 194362355744453368425371393)
        ·
          refine ⟨145771766808340026319028545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194362355744453368425371393 145771766808340026319028545)
          ·
            refine ⟨109328825106255019739271409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145771766808340026319028545 109328825106255019739271409)
            ·
              refine ⟨81996618829691264804453557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109328825106255019739271409 81996618829691264804453557)
              ·
                refine ⟨7687183015283556075417521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81996618829691264804453557 7687183015283556075417521)
                ·
                  refine ⟨5765387261462667056563141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687183015283556075417521 5765387261462667056563141)
                  ·
                    refine ⟨1081010111524250073105589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765387261462667056563141 1081010111524250073105589)
                    ·
                      rfl

theorem cell23_6315779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 4].length) (baseStart_6315779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315779 prefixEnd_6315779 := by exact prefixLift 6315779
  have htrace : WordTrace (prefixWord ++ tailWord_6315779) baseStart_6315779 baseEnd_6315779 := by
    simpa [prefixWord, tailWord_6315779, baseEnd_6315779] using wordTrace_append hprefix tailTrace_6315779
  have hstable : (prefixWord ++ tailWord_6315779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315779).length < 2 ^ (prefixWord ++ tailWord_6315779).sum := by decide
  have hdescent : baseEnd_6315779 < baseStart_6315779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315786 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_6315786 : Nat := 118140960795 + 6315786 * 2 ^ 59
def prefixEnd_6315786 : Nat := 4983230072969 + 3 ^ 40 * 6315786 * 2
def baseEnd_6315786 : Nat := 3243033928937331691929235

theorem tailTrace_6315786 : CollatzResearch.WordTrace tailWord_6315786 prefixEnd_6315786 3243033928937331691929235 := by
  unfold tailWord_6315786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57588909974248361804541803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153570426597995631478778141 57588909974248361804541803)
  ·
    refine ⟨86383364961372542706812705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57588909974248361804541803 86383364961372542706812705)
    ·
      refine ⟨64787523721029407030109529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86383364961372542706812705 64787523721029407030109529)
      ·
        refine ⟨48590642790772055272582147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64787523721029407030109529 48590642790772055272582147)
        ·
          refine ⟨72885964186158082908873221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48590642790772055272582147 72885964186158082908873221)
          ·
            refine ⟨13666118284904640545413729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72885964186158082908873221 13666118284904640545413729)
            ·
              refine ⟨10249588713678480409060297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13666118284904640545413729 10249588713678480409060297)
              ·
                refine ⟨7687191535258860306795223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10249588713678480409060297 7687191535258860306795223)
                ·
                  refine ⟨11530787302888290460192835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7687191535258860306795223 11530787302888290460192835)
                  ·
                    refine ⟨17296180954332435690289253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11530787302888290460192835 17296180954332435690289253)
                    ·
                      refine ⟨3243033928937331691929235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17296180954332435690289253 3243033928937331691929235)
                      ·
                        rfl

theorem cell23_6315786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_6315786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315786 prefixEnd_6315786 := by exact prefixLift 6315786
  have htrace : WordTrace (prefixWord ++ tailWord_6315786) baseStart_6315786 baseEnd_6315786 := by
    simpa [prefixWord, tailWord_6315786, baseEnd_6315786] using wordTrace_append hprefix tailTrace_6315786
  have hstable : (prefixWord ++ tailWord_6315786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315786).length < 2 ^ (prefixWord ++ tailWord_6315786).sum := by decide
  have hdescent : baseEnd_6315786 < baseStart_6315786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315819 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 3]
def baseStart_6315819 : Nat := 118140960795 + 6315819 * 2 ^ 59
def prefixEnd_6315819 : Nat := 4983230072969 + 3 ^ 40 * 6315819 * 2
def baseEnd_6315819 : Nat := 3243050873798930062816583

theorem tailTrace_6315819 : CollatzResearch.WordTrace tailWord_6315819 prefixEnd_6315819 3243050873798930062816583 := by
  unfold tailWord_6315819
  simp only [CollatzResearch.WordTrace]
  refine ⟨230356843505873893854118511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153571229003915929236079007 230356843505873893854118511)
  ·
    refine ⟨345535265258810840781177767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230356843505873893854118511 345535265258810840781177767)
    ·
      refine ⟨518302897888216261171766651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345535265258810840781177767 518302897888216261171766651)
      ·
        refine ⟨777454346832324391757649977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518302897888216261171766651 777454346832324391757649977)
        ·
          refine ⟨583090760124243293818237483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777454346832324391757649977 583090760124243293818237483)
          ·
            refine ⟨874636140186364940727356225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583090760124243293818237483 874636140186364940727356225)
            ·
              refine ⟨655977105139773705545517169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874636140186364940727356225 655977105139773705545517169)
              ·
                refine ⟨491982828854830279159137877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655977105139773705545517169 491982828854830279159137877)
                ·
                  refine ⟨5765423775642542333896147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 491982828854830279159137877 5765423775642542333896147)
                  ·
                    refine ⟨8648135663463813500844221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765423775642542333896147 8648135663463813500844221)
                    ·
                      refine ⟨3243050873798930062816583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8648135663463813500844221 3243050873798930062816583)
                      ·
                        rfl

theorem cell23_6315819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 3].length) (baseStart_6315819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315819 prefixEnd_6315819 := by exact prefixLift 6315819
  have htrace : WordTrace (prefixWord ++ tailWord_6315819) baseStart_6315819 baseEnd_6315819 := by
    simpa [prefixWord, tailWord_6315819, baseEnd_6315819] using wordTrace_append hprefix tailTrace_6315819
  have hstable : (prefixWord ++ tailWord_6315819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315819).length < 2 ^ (prefixWord ++ tailWord_6315819).sum := by decide
  have hdescent : baseEnd_6315819 < baseStart_6315819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315830 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6315830 : Nat := 118140960795 + 6315830 * 2 ^ 59
def prefixEnd_6315830 : Nat := 4983230072969 + 3 ^ 40 * 6315830 * 2
def baseEnd_6315830 : Nat := 1081018840695376506593011

theorem tailTrace_6315830 : CollatzResearch.WordTrace tailWord_6315830 prefixEnd_6315830 1081018840695376506593011 := by
  unfold tailWord_6315830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14397327794302127670798059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153571496472556028488512629 14397327794302127670798059)
  ·
    refine ⟨21595991691453191506197089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14397327794302127670798059 21595991691453191506197089)
    ·
      refine ⟨16196993768589893629647817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21595991691453191506197089 16196993768589893629647817)
      ·
        refine ⟨12147745326442420222235863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16196993768589893629647817 12147745326442420222235863)
        ·
          refine ⟨18221617989663630333353795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147745326442420222235863 18221617989663630333353795)
          ·
            refine ⟨27332426984495445500030693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18221617989663630333353795 27332426984495445500030693)
            ·
              refine ⟨5124830059592896031255755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27332426984495445500030693 5124830059592896031255755)
              ·
                refine ⟨7687245089389344046883633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124830059592896031255755 7687245089389344046883633)
                ·
                  refine ⟨5765433817042008035162725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687245089389344046883633 5765433817042008035162725)
                  ·
                    refine ⟨1081018840695376506593011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765433817042008035162725 1081018840695376506593011)
                    ·
                      rfl

theorem cell23_6315830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6315830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315830 prefixEnd_6315830 := by exact prefixLift 6315830
  have htrace : WordTrace (prefixWord ++ tailWord_6315830) baseStart_6315830 baseEnd_6315830 := by
    simpa [prefixWord, tailWord_6315830, baseEnd_6315830] using wordTrace_append hprefix tailTrace_6315830
  have hstable : (prefixWord ++ tailWord_6315830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315830).length < 2 ^ (prefixWord ++ tailWord_6315830).sum := by decide
  have hdescent : baseEnd_6315830 < baseStart_6315830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315853 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6315853 : Nat := 118140960795 + 6315853 * 2 ^ 59
def prefixEnd_6315853 : Nat := 4983230072969 + 3 ^ 40 * 6315853 * 2
def baseEnd_6315853 : Nat := 3243068332141182929791427

theorem tailTrace_6315853 : CollatzResearch.WordTrace tailWord_6315853 prefixEnd_6315853 3243068332141182929791427 := by
  unfold tailWord_6315853
  simp only [CollatzResearch.WordTrace]
  refine ⟨230358083587750717660856213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153572055725167145107237475 230358083587750717660856213)
  ·
    refine ⟨10798035168175814890352635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230358083587750717660856213 10798035168175814890352635)
    ·
      refine ⟨16197052752263722335528953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798035168175814890352635 16197052752263722335528953)
      ·
        refine ⟨12147789564197791751646715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16197052752263722335528953 12147789564197791751646715)
        ·
          refine ⟨18221684346296687627470073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147789564197791751646715 18221684346296687627470073)
          ·
            refine ⟨13666263259722515720602555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18221684346296687627470073 13666263259722515720602555)
            ·
              refine ⟨20499394889583773580903833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13666263259722515720602555 20499394889583773580903833)
              ·
                refine ⟨15374546167187830185677875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20499394889583773580903833 15374546167187830185677875)
                ·
                  refine ⟨23061819250781745278516813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15374546167187830185677875 23061819250781745278516813)
                  ·
                    refine ⟨8648182219043154479443805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23061819250781745278516813 8648182219043154479443805)
                    ·
                      refine ⟨3243068332141182929791427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8648182219043154479443805 3243068332141182929791427)
                      ·
                        rfl

theorem cell23_6315853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6315853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315853 prefixEnd_6315853 := by exact prefixLift 6315853
  have htrace : WordTrace (prefixWord ++ tailWord_6315853) baseStart_6315853 baseEnd_6315853 := by
    simpa [prefixWord, tailWord_6315853, baseEnd_6315853] using wordTrace_append hprefix tailTrace_6315853
  have hstable : (prefixWord ++ tailWord_6315853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315853).length < 2 ^ (prefixWord ++ tailWord_6315853).sum := by decide
  have hdescent : baseEnd_6315853 < baseStart_6315853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315879 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_6315879 : Nat := 118140960795 + 6315879 * 2 ^ 59
def prefixEnd_6315879 : Nat := 4983230072969 + 3 ^ 40 * 6315879 * 2
def baseEnd_6315879 : Nat := 3243081682638199828066307

theorem tailTrace_6315879 : CollatzResearch.WordTrace tailWord_6315879 prefixEnd_6315879 3243081682638199828066307 := by
  unfold tailWord_6315879
  simp only [CollatzResearch.WordTrace]
  refine ⟨230359031885656524101302691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153572687923771016067535127 230359031885656524101302691)
  ·
    refine ⟨345538547828484786151954037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230359031885656524101302691 345538547828484786151954037)
    ·
      refine ⟨32394238858920448701745691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345538547828484786151954037 32394238858920448701745691)
      ·
        refine ⟨48591358288380673052618537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32394238858920448701745691 48591358288380673052618537)
        ·
          refine ⟨36443518716285504789463903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48591358288380673052618537 36443518716285504789463903)
          ·
            refine ⟨54665278074428257184195855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36443518716285504789463903 54665278074428257184195855)
            ·
              refine ⟨81997917111642385776293783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54665278074428257184195855 81997917111642385776293783)
              ·
                refine ⟨122996875667463578664440675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81997917111642385776293783 122996875667463578664440675)
                ·
                  refine ⟨184495313501195367996661013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122996875667463578664440675 184495313501195367996661013)
                  ·
                    refine ⟨8648217820368532874843485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184495313501195367996661013 8648217820368532874843485)
                    ·
                      refine ⟨3243081682638199828066307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8648217820368532874843485 3243081682638199828066307)
                      ·
                        rfl

theorem cell23_6315879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_6315879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315879 prefixEnd_6315879 := by exact prefixLift 6315879
  have htrace : WordTrace (prefixWord ++ tailWord_6315879) baseStart_6315879 baseEnd_6315879 := by
    simpa [prefixWord, tailWord_6315879, baseEnd_6315879] using wordTrace_append hprefix tailTrace_6315879
  have hstable : (prefixWord ++ tailWord_6315879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315879).length < 2 ^ (prefixWord ++ tailWord_6315879).sum := by decide
  have hdescent : baseEnd_6315879 < baseStart_6315879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315886 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6315886 : Nat := 118140960795 + 6315886 * 2 ^ 59
def prefixEnd_6315886 : Nat := 4983230072969 + 3 ^ 40 * 6315886 * 2
def baseEnd_6315886 : Nat := 1081028425667593766892925

theorem tailTrace_6315886 : CollatzResearch.WordTrace tailWord_6315886 prefixEnd_6315886 1081028425667593766892925 := by
  unfold tailWord_6315886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794910899578895537100939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153572858131087442864538341 28794910899578895537100939)
  ·
    refine ⟨43192366349368343305651409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28794910899578895537100939 43192366349368343305651409)
    ·
      refine ⟨32394274762026257479238557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43192366349368343305651409 32394274762026257479238557)
      ·
        refine ⟨12147853035759846554714459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32394274762026257479238557 12147853035759846554714459)
        ·
          refine ⟨18221779553639769832071689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147853035759846554714459 18221779553639769832071689)
          ·
            refine ⟨13666334665229827374053767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18221779553639769832071689 13666334665229827374053767)
            ·
              refine ⟨20499501997844741061080651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13666334665229827374053767 20499501997844741061080651)
              ·
                refine ⟨30749252996767111591620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20499501997844741061080651 30749252996767111591620977)
                ·
                  refine ⟨23061939747575333693715733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30749252996767111591620977 23061939747575333693715733)
                  ·
                    refine ⟨1081028425667593766892925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23061939747575333693715733 1081028425667593766892925)
                    ·
                      rfl

theorem cell23_6315886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6315886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315886 prefixEnd_6315886 := by exact prefixLift 6315886
  have htrace : WordTrace (prefixWord ++ tailWord_6315886) baseStart_6315886 baseEnd_6315886 := by
    simpa [prefixWord, tailWord_6315886, baseEnd_6315886] using wordTrace_append hprefix tailTrace_6315886
  have hstable : (prefixWord ++ tailWord_6315886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315886).length < 2 ^ (prefixWord ++ tailWord_6315886).sum := by decide
  have hdescent : baseEnd_6315886 < baseStart_6315886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315889 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_6315889 : Nat := 118140960795 + 6315889 * 2 ^ 59
def prefixEnd_6315889 : Nat := 4983230072969 + 3 ^ 40 * 6315889 * 2
def baseEnd_6315889 : Nat := 3243086817444744788941261

theorem tailTrace_6315889 : CollatzResearch.WordTrace tailWord_6315889 prefixEnd_6315889 3243086817444744788941261 := by
  unfold tailWord_6315889
  simp only [CollatzResearch.WordTrace]
  refine ⟨230359396615620295809166721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153572931077080197206111147 230359396615620295809166721)
  ·
    refine ⟨172769547461715221856875041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230359396615620295809166721 172769547461715221856875041)
    ·
      refine ⟨129577160596286416392656281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172769547461715221856875041 129577160596286416392656281)
      ·
        refine ⟨97182870447214812294492211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129577160596286416392656281 97182870447214812294492211)
        ·
          refine ⟨145774305670822218441738317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97182870447214812294492211 145774305670822218441738317)
          ·
            refine ⟨54665364626558331915651869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145774305670822218441738317 54665364626558331915651869)
            ·
              refine ⟨20499511734959374468369451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54665364626558331915651869 20499511734959374468369451)
              ·
                refine ⟨30749267602439061702554177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20499511734959374468369451 30749267602439061702554177)
                ·
                  refine ⟨23061950701829296276915633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30749267602439061702554177 23061950701829296276915633)
                  ·
                    refine ⟨17296463026371972207686725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23061950701829296276915633 17296463026371972207686725)
                    ·
                      refine ⟨3243086817444744788941261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17296463026371972207686725 3243086817444744788941261)
                      ·
                        rfl

theorem cell23_6315889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_6315889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315889 prefixEnd_6315889 := by exact prefixLift 6315889
  have htrace : WordTrace (prefixWord ++ tailWord_6315889) baseStart_6315889 baseEnd_6315889 := by
    simpa [prefixWord, tailWord_6315889, baseEnd_6315889] using wordTrace_append hprefix tailTrace_6315889
  have hstable : (prefixWord ++ tailWord_6315889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315889).length < 2 ^ (prefixWord ++ tailWord_6315889).sum := by decide
  have hdescent : baseEnd_6315889 < baseStart_6315889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315893 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6315893 : Nat := 118140960795 + 6315893 * 2 ^ 59
def prefixEnd_6315893 : Nat := 4983230072969 + 3 ^ 40 * 6315893 * 2
def baseEnd_6315893 : Nat := 3243088871367362773291243

theorem tailTrace_6315893 : CollatzResearch.WordTrace tailWord_6315893 prefixEnd_6315893 3243088871367362773291243 := by
  unfold tailWord_6315893
  simp only [CollatzResearch.WordTrace]
  refine ⟨230359542507605804492312333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153573028338403869661541555 230359542507605804492312333)
  ·
    refine ⟨86384828440352176684617125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230359542507605804492312333 86384828440352176684617125)
    ·
      refine ⟨16197155332566033128365711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86384828440352176684617125 16197155332566033128365711)
      ·
        refine ⟨24295732998849049692548567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16197155332566033128365711 24295732998849049692548567)
        ·
          refine ⟨36443599498273574538822851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24295732998849049692548567 36443599498273574538822851)
          ·
            refine ⟨54665399247410361808234277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36443599498273574538822851 54665399247410361808234277)
            ·
              refine ⟨10249762358889442839043927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54665399247410361808234277 10249762358889442839043927)
              ·
                refine ⟨15374643538334164258565891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249762358889442839043927 15374643538334164258565891)
                ·
                  refine ⟨23061965307501246387848837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15374643538334164258565891 23061965307501246387848837)
                  ·
                    refine ⟨4324118495156483697721657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23061965307501246387848837 4324118495156483697721657)
                    ·
                      refine ⟨3243088871367362773291243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324118495156483697721657 3243088871367362773291243)
                      ·
                        rfl

theorem cell23_6315893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6315893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315893 prefixEnd_6315893 := by exact prefixLift 6315893
  have htrace : WordTrace (prefixWord ++ tailWord_6315893) baseStart_6315893 baseEnd_6315893 := by
    simpa [prefixWord, tailWord_6315893, baseEnd_6315893] using wordTrace_append hprefix tailTrace_6315893
  have hstable : (prefixWord ++ tailWord_6315893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315893).length < 2 ^ (prefixWord ++ tailWord_6315893).sum := by decide
  have hdescent : baseEnd_6315893 < baseStart_6315893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315909 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_6315909 : Nat := 118140960795 + 6315909 * 2 ^ 59
def prefixEnd_6315909 : Nat := 4983230072969 + 3 ^ 40 * 6315909 * 2
def baseEnd_6315909 : Nat := 3243097087057834710691169

theorem tailTrace_6315909 : CollatzResearch.WordTrace tailWord_6315909 prefixEnd_6315909 3243097087057834710691169 := by
  unfold tailWord_6315909
  simp only [CollatzResearch.WordTrace]
  refine ⟨230360126075547839224894781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153573417383698559483263187 230360126075547839224894781)
  ·
    refine ⟨86385047278330439709335543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230360126075547839224894781 86385047278330439709335543)
    ·
      refine ⟨129577570917495659564003315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86385047278330439709335543 129577570917495659564003315)
      ·
        refine ⟨194366356376243489346004973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129577570917495659564003315 194366356376243489346004973)
        ·
          refine ⟨72887383641091308504751865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194366356376243489346004973 72887383641091308504751865)
          ·
            refine ⟨54665537730818481378563899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72887383641091308504751865 54665537730818481378563899)
            ·
              refine ⟨81998306596227722067845849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54665537730818481378563899 81998306596227722067845849)
              ·
                refine ⟨61498729947170791550884387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81998306596227722067845849 61498729947170791550884387)
                ·
                  refine ⟨92248094920756187326326581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61498729947170791550884387 92248094920756187326326581)
                  ·
                    refine ⟨8648258898820892561843117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92248094920756187326326581 8648258898820892561843117)
                    ·
                      refine ⟨3243097087057834710691169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8648258898820892561843117 3243097087057834710691169)
                      ·
                        rfl

theorem cell23_6315909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_6315909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315909 prefixEnd_6315909 := by exact prefixLift 6315909
  have htrace : WordTrace (prefixWord ++ tailWord_6315909) baseStart_6315909 baseEnd_6315909 := by
    simpa [prefixWord, tailWord_6315909, baseEnd_6315909] using wordTrace_append hprefix tailTrace_6315909
  have hstable : (prefixWord ++ tailWord_6315909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315909).length < 2 ^ (prefixWord ++ tailWord_6315909).sum := by decide
  have hdescent : baseEnd_6315909 < baseStart_6315909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315914 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6315914 : Nat := 118140960795 + 6315914 * 2 ^ 59
def prefixEnd_6315914 : Nat := 4983230072969 + 3 ^ 40 * 6315914 * 2
def baseEnd_6315914 : Nat := 3243099654461107191128647

theorem tailTrace_6315914 : CollatzResearch.WordTrace tailWord_6315914 prefixEnd_6315914 3243099654461107191128647 := by
  unfold tailWord_6315914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590077110132431269706699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153573538960353150052551197 57590077110132431269706699)
  ·
    refine ⟨86385115665198646904560049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57590077110132431269706699 86385115665198646904560049)
    ·
      refine ⟨64788836748898985178420037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86385115665198646904560049 64788836748898985178420037)
      ·
        refine ⟨12147906890418559720953757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64788836748898985178420037 12147906890418559720953757)
        ·
          refine ⟨4555465083906959895357659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12147906890418559720953757 4555465083906959895357659)
          ·
            refine ⟨6833197625860439843036489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555465083906959895357659 6833197625860439843036489)
            ·
              refine ⟨5124898219395329882277367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6833197625860439843036489 5124898219395329882277367)
              ·
                refine ⟨7687347329092994823416051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124898219395329882277367 7687347329092994823416051)
                ·
                  refine ⟨11531020993639492235124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7687347329092994823416051 11531020993639492235124077)
                  ·
                    refine ⟨4324132872614809588171529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11531020993639492235124077 4324132872614809588171529)
                    ·
                      refine ⟨3243099654461107191128647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324132872614809588171529 3243099654461107191128647)
                      ·
                        rfl

theorem cell23_6315914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6315914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315914 prefixEnd_6315914 := by exact prefixLift 6315914
  have htrace : WordTrace (prefixWord ++ tailWord_6315914) baseStart_6315914 baseEnd_6315914 := by
    simpa [prefixWord, tailWord_6315914, baseEnd_6315914] using wordTrace_append hprefix tailTrace_6315914
  have hstable : (prefixWord ++ tailWord_6315914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315914).length < 2 ^ (prefixWord ++ tailWord_6315914).sum := by decide
  have hdescent : baseEnd_6315914 < baseStart_6315914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315929 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_6315929 : Nat := 118140960795 + 6315929 * 2 ^ 59
def prefixEnd_6315929 : Nat := 4983230072969 + 3 ^ 40 * 6315929 * 2
def baseEnd_6315929 : Nat := 1081035785556974877480359

theorem tailTrace_6315929 : CollatzResearch.WordTrace tailWord_6315929 prefixEnd_6315929 1081035785556974877480359 := by
  unfold tailWord_6315929
  simp only [CollatzResearch.WordTrace]
  refine ⟨230360855535475382640622841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153573903690316921760415227 230360855535475382640622841)
  ·
    refine ⟨172770641651606536980467131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230360855535475382640622841 172770641651606536980467131)
    ·
      refine ⟨259155962477409805470700697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172770641651606536980467131 259155962477409805470700697)
      ·
        refine ⟨194366971858057354103025523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259155962477409805470700697 194366971858057354103025523)
        ·
          refine ⟨291550457787086031154538285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194366971858057354103025523 291550457787086031154538285)
          ·
            refine ⟨109331421670157261682951857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291550457787086031154538285 109331421670157261682951857)
            ·
              refine ⟨81998566252617946262213893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109331421670157261682951857 81998566252617946262213893)
              ·
                refine ⟨15374731172365864924165105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81998566252617946262213893 15374731172365864924165105)
                ·
                  refine ⟨11531048379274398693123829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15374731172365864924165105 11531048379274398693123829)
                  ·
                    refine ⟨1081035785556974877480359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11531048379274398693123829 1081035785556974877480359)
                    ·
                      rfl

theorem cell23_6315929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_6315929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315929 prefixEnd_6315929 := by exact prefixLift 6315929
  have htrace : WordTrace (prefixWord ++ tailWord_6315929) baseStart_6315929 baseEnd_6315929 := by
    simpa [prefixWord, tailWord_6315929, baseEnd_6315929] using wordTrace_append hprefix tailTrace_6315929
  have hstable : (prefixWord ++ tailWord_6315929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315929).length < 2 ^ (prefixWord ++ tailWord_6315929).sum := by decide
  have hdescent : baseEnd_6315929 < baseStart_6315929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315944 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6315944 : Nat := 118140960795 + 6315944 * 2 ^ 59
def prefixEnd_6315944 : Nat := 4983230072969 + 3 ^ 40 * 6315944 * 2
def baseEnd_6315944 : Nat := 3243115058880742073753509

theorem tailTrace_6315944 : CollatzResearch.WordTrace tailWord_6315944 prefixEnd_6315944 3243115058880742073753509 := by
  unfold tailWord_6315944
  simp only [CollatzResearch.WordTrace]
  refine ⟨115180701315210520101209443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153574268420280693468279257 115180701315210520101209443)
  ·
    refine ⟨172771051972815780151814165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115180701315210520101209443 172771051972815780151814165)
    ·
      refine ⟨8098643061225739694616289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172771051972815780151814165 8098643061225739694616289)
      ·
        refine ⟨6073982295919304770962217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8098643061225739694616289 6073982295919304770962217)
        ·
          refine ⟨4555486721939478578221663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6073982295919304770962217 4555486721939478578221663)
          ·
            refine ⟨6833230082909217867332495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555486721939478578221663 6833230082909217867332495)
            ·
              refine ⟨10249845124363826800998743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833230082909217867332495 10249845124363826800998743)
              ·
                refine ⟨15374767686545740201498115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249845124363826800998743 15374767686545740201498115)
                ·
                  refine ⟨23062151529818610302247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15374767686545740201498115 23062151529818610302247173)
                  ·
                    refine ⟨4324153411840989431671345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23062151529818610302247173 4324153411840989431671345)
                    ·
                      refine ⟨3243115058880742073753509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324153411840989431671345 3243115058880742073753509)
                      ·
                        rfl

theorem cell23_6315944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6315944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315944 prefixEnd_6315944 := by exact prefixLift 6315944
  have htrace : WordTrace (prefixWord ++ tailWord_6315944) baseStart_6315944 baseEnd_6315944 := by
    simpa [prefixWord, tailWord_6315944, baseEnd_6315944] using wordTrace_append hprefix tailTrace_6315944
  have hstable : (prefixWord ++ tailWord_6315944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315944).length < 2 ^ (prefixWord ++ tailWord_6315944).sum := by decide
  have hdescent : baseEnd_6315944 < baseStart_6315944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6315966 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_6315966 : Nat := 118140960795 + 6315966 * 2 ^ 59
def prefixEnd_6315966 : Nat := 4983230072969 + 3 ^ 40 * 6315966 * 2
def baseEnd_6315966 : Nat := 3243126355455140987678407

theorem tailTrace_6315966 : CollatzResearch.WordTrace tailWord_6315966 prefixEnd_6315966 3243126355455140987678407 := by
  unfold tailWord_6315966
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795275629542667244964969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153574803357560891973146501 28795275629542667244964969)
  ·
    refine ⟨21596456722157000433723727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28795275629542667244964969 21596456722157000433723727)
    ·
      refine ⟨32394685083235500650585591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21596456722157000433723727 32394685083235500650585591)
      ·
        refine ⟨48592027624853250975878387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32394685083235500650585591 48592027624853250975878387)
        ·
          refine ⟨72888041437279876463817581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48592027624853250975878387 72888041437279876463817581)
          ·
            refine ⟨27333015538979953673931593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72888041437279876463817581 27333015538979953673931593)
            ·
              refine ⟨20499761654234965255448695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27333015538979953673931593 20499761654234965255448695)
              ·
                refine ⟨30749642481352447883173043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20499761654234965255448695 30749642481352447883173043)
                ·
                  refine ⟨46124463722028671824759565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30749642481352447883173043 46124463722028671824759565)
                  ·
                    refine ⟨17296673895760751934284837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46124463722028671824759565 17296673895760751934284837)
                    ·
                      refine ⟨3243126355455140987678407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17296673895760751934284837 3243126355455140987678407)
                      ·
                        rfl

theorem cell23_6315966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_6315966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6315966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6315966 prefixEnd_6315966 := by exact prefixLift 6315966
  have htrace : WordTrace (prefixWord ++ tailWord_6315966) baseStart_6315966 baseEnd_6315966 := by
    simpa [prefixWord, tailWord_6315966, baseEnd_6315966] using wordTrace_append hprefix tailTrace_6315966
  have hstable : (prefixWord ++ tailWord_6315966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6315966).length < 2 ^ (prefixWord ++ tailWord_6315966).sum := by decide
  have hdescent : baseEnd_6315966 < baseStart_6315966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6315966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316043 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 2, 3, 2]
def baseStart_6316043 : Nat := 118140960795 + 6316043 * 2 ^ 59
def prefixEnd_6316043 : Nat := 4983230072969 + 3 ^ 40 * 6316043 * 2
def baseEnd_6316043 : Nat := 3243165893465537186415553

theorem tailTrace_6316043 : CollatzResearch.WordTrace tailWord_6316043 prefixEnd_6316043 3243165893465537186415553 := by
  unfold tailWord_6316043
  simp only [CollatzResearch.WordTrace]
  refine ⟨230365013457062380110272783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153576675638041586740181855 230365013457062380110272783)
  ·
    refine ⟨345547520185593570165409175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230365013457062380110272783 345547520185593570165409175)
    ·
      refine ⟨518321280278390355248113763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345547520185593570165409175 518321280278390355248113763)
      ·
        refine ⟨777481920417585532872170645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518321280278390355248113763 777481920417585532872170645)
        ·
          refine ⟨36444465019574321853382999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 777481920417585532872170645 36444465019574321853382999)
          ·
            refine ⟨54666697529361482780074499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36444465019574321853382999 54666697529361482780074499)
            ·
              refine ⟨82000046294042224170111749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54666697529361482780074499 82000046294042224170111749)
              ·
                refine ⟨15375008680132917031895953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82000046294042224170111749 15375008680132917031895953)
                ·
                  refine ⟨11531256510099687773921965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15375008680132917031895953 11531256510099687773921965)
                  ·
                    refine ⟨4324221191287382915220737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11531256510099687773921965 4324221191287382915220737)
                    ·
                      refine ⟨3243165893465537186415553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324221191287382915220737 3243165893465537186415553)
                      ·
                        rfl

theorem cell23_6316043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3, 2].length) (baseStart_6316043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316043 prefixEnd_6316043 := by exact prefixLift 6316043
  have htrace : WordTrace (prefixWord ++ tailWord_6316043) baseStart_6316043 baseEnd_6316043 := by
    simpa [prefixWord, tailWord_6316043, baseEnd_6316043] using wordTrace_append hprefix tailTrace_6316043
  have hstable : (prefixWord ++ tailWord_6316043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316043).length < 2 ^ (prefixWord ++ tailWord_6316043).sum := by decide
  have hdescent : baseEnd_6316043 < baseStart_6316043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316056 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6316056 : Nat := 118140960795 + 6316056 * 2 ^ 59
def prefixEnd_6316056 : Nat := 4983230072969 + 3 ^ 40 * 6316056 * 2
def baseEnd_6316056 : Nat := 3243172568714045635552993

theorem tailTrace_6316056 : CollatzResearch.WordTrace tailWord_6316056 prefixEnd_6316056 3243172568714045635552993 := by
  unfold tailWord_6316056
  simp only [CollatzResearch.WordTrace]
  refine ⟨115182743803007641665248011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153576991737343522220330681 115182743803007641665248011)
  ·
    refine ⟨172774115704511462497872017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115182743803007641665248011 172774115704511462497872017)
    ·
      refine ⟨129580586778383596873404013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172774115704511462497872017 129580586778383596873404013)
      ·
        refine ⟨48592720041893848827526505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129580586778383596873404013 48592720041893848827526505)
        ·
          refine ⟨36444540031420386620644879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48592720041893848827526505 36444540031420386620644879)
          ·
            refine ⟨54666810047130579930967319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36444540031420386620644879 54666810047130579930967319)
            ·
              refine ⟨82000215070695869896450979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54666810047130579930967319 82000215070695869896450979)
              ·
                refine ⟨123000322606043804844676469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82000215070695869896450979 123000322606043804844676469)
                ·
                  refine ⟨11531280244316606704188419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123000322606043804844676469 11531280244316606704188419)
                  ·
                    refine ⟨17296920366474910056282629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11531280244316606704188419 17296920366474910056282629)
                    ·
                      refine ⟨3243172568714045635552993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17296920366474910056282629 3243172568714045635552993)
                      ·
                        rfl

theorem cell23_6316056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6316056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316056 prefixEnd_6316056 := by exact prefixLift 6316056
  have htrace : WordTrace (prefixWord ++ tailWord_6316056) baseStart_6316056 baseEnd_6316056 := by
    simpa [prefixWord, tailWord_6316056, baseEnd_6316056] using wordTrace_append hprefix tailTrace_6316056
  have hstable : (prefixWord ++ tailWord_6316056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316056).length < 2 ^ (prefixWord ++ tailWord_6316056).sum := by decide
  have hdescent : baseEnd_6316056 < baseStart_6316056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
