import V185TrunkScan20Chunk089

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_547946 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_547946 : Nat := 118140960795 + 547946 * 2 ^ 59
def prefixEnd_547946 : Nat := 4983230072969 + 3 ^ 40 * 547946 * 2
def baseEnd_547946 : Nat := 250097485074327459960043

theorem tailTrace_547946 : CollatzResearch.WordTrace tailWord_547946 prefixEnd_547946 250097485074327459960043 := by
  unfold tailWord_547946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4996308118223174642871923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13323488315261799047658461 4996308118223174642871923)
  ·
    refine ⟨7494462177334761964307885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4996308118223174642871923 7494462177334761964307885)
    ·
      refine ⟨2810423316500535736615457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7494462177334761964307885 2810423316500535736615457)
      ·
        refine ⟨2107817487375401802461593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810423316500535736615457 2107817487375401802461593)
        ·
          refine ⟨1580863115531551351846195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107817487375401802461593 1580863115531551351846195)
          ·
            refine ⟨2371294673297327027769293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580863115531551351846195 2371294673297327027769293)
            ·
              refine ⟨889235502486497635413485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371294673297327027769293 889235502486497635413485)
              ·
                refine ⟨333463313432436613280057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 889235502486497635413485 333463313432436613280057)
                ·
                  refine ⟨250097485074327459960043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333463313432436613280057 250097485074327459960043)
                  ·
                    rfl

theorem cell20_547946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_547946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547946 prefixEnd_547946 := by exact prefixLift 547946
  have htrace : WordTrace (prefixWord ++ tailWord_547946) baseStart_547946 baseEnd_547946 := by
    simpa [prefixWord, tailWord_547946, baseEnd_547946] using wordTrace_append hprefix tailTrace_547946
  have hstable : (prefixWord ++ tailWord_547946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547946).length < 2 ^ (prefixWord ++ tailWord_547946).sum := by decide
  have hdescent : baseEnd_547946 < baseStart_547946 := by decide
  rcases family_descends (prefixWord ++ tailWord_547946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547964 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_547964 : Nat := 118140960795 + 547964 * 2 ^ 59
def prefixEnd_547964 : Nat := 4983230072969 + 3 ^ 40 * 547964 * 2
def baseEnd_547964 : Nat := 250105700764799397359969

theorem tailTrace_547964 : CollatzResearch.WordTrace tailWord_547964 prefixEnd_547964 250105700764799397359969 := by
  unfold tailWord_547964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992944493413743822821473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13323925991218325097095297 9992944493413743822821473)
  ·
    refine ⟨7494708370060307867116105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9992944493413743822821473 7494708370060307867116105)
    ·
      refine ⟨5621031277545230900337079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7494708370060307867116105 5621031277545230900337079)
      ·
        refine ⟨8431546916317846350505619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621031277545230900337079 8431546916317846350505619)
        ·
          refine ⟨12647320374476769525758429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8431546916317846350505619 12647320374476769525758429)
          ·
            refine ⟨4742745140428788572159411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12647320374476769525758429 4742745140428788572159411)
            ·
              refine ⟨7114117710643182858239117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742745140428788572159411 7114117710643182858239117)
              ·
                refine ⟨2667794141491193571839669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7114117710643182858239117 2667794141491193571839669)
                ·
                  refine ⟨250105700764799397359969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667794141491193571839669 250105700764799397359969)
                  ·
                    rfl

theorem cell20_547964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_547964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_547964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_547964 prefixEnd_547964 := by exact prefixLift 547964
  have htrace : WordTrace (prefixWord ++ tailWord_547964) baseStart_547964 baseEnd_547964 := by
    simpa [prefixWord, tailWord_547964, baseEnd_547964] using wordTrace_append hprefix tailTrace_547964
  have hstable : (prefixWord ++ tailWord_547964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547964).length < 2 ^ (prefixWord ++ tailWord_547964).sum := by decide
  have hdescent : baseEnd_547964 < baseStart_547964 := by decide
  rcases family_descends (prefixWord ++ tailWord_547964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548050 : List Nat := [3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_548050 : Nat := 118140960795 + 548050 * 2 ^ 59
def prefixEnd_548050 : Nat := 4983230072969 + 3 ^ 40 * 548050 * 2
def baseEnd_548050 : Nat := 83381651169388440164317

theorem tailTrace_548050 : CollatzResearch.WordTrace tailWord_548050 prefixEnd_548050 83381651169388440164317 := by
  unfold tailWord_548050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997256416128981083318401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13326017109677282888849069 4997256416128981083318401)
  ·
    refine ⟨3747942312096735812488801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4997256416128981083318401 3747942312096735812488801)
    ·
      refine ⟨2810956734072551859366601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3747942312096735812488801 2810956734072551859366601)
      ·
        refine ⟨2108217550554413894524951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810956734072551859366601 2108217550554413894524951)
        ·
          refine ⟨3162326325831620841787427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108217550554413894524951 3162326325831620841787427)
          ·
            refine ⟨4743489488747431262681141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162326325831620841787427 4743489488747431262681141)
            ·
              refine ⟨444702139570071680876357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4743489488747431262681141 444702139570071680876357)
              ·
                refine ⟨83381651169388440164317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444702139570071680876357 83381651169388440164317)
                ·
                  rfl

theorem cell20_548050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_548050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548050 prefixEnd_548050 := by exact prefixLift 548050
  have htrace : WordTrace (prefixWord ++ tailWord_548050) baseStart_548050 baseEnd_548050 := by
    simpa [prefixWord, tailWord_548050, baseEnd_548050] using wordTrace_append hprefix tailTrace_548050
  have hstable : (prefixWord ++ tailWord_548050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548050).length < 2 ^ (prefixWord ++ tailWord_548050).sum := by decide
  have hdescent : baseEnd_548050 < baseStart_548050 := by decide
  rcases family_descends (prefixWord ++ tailWord_548050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548074 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_548074 : Nat := 118140960795 + 548074 * 2 ^ 59
def prefixEnd_548074 : Nat := 4983230072969 + 3 ^ 40 * 548074 * 2
def baseEnd_548074 : Nat := 250155907762127903692853

theorem tailTrace_548074 : CollatzResearch.WordTrace tailWord_548074 prefixEnd_548074 250155907762127903692853 := by
  unfold tailWord_548074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997475254107244108036819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13326600677619317621431517 4997475254107244108036819)
  ·
    refine ⟨7496212881160866162055229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4997475254107244108036819 7496212881160866162055229)
    ·
      refine ⟨2811079830435324810770711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7496212881160866162055229 2811079830435324810770711)
      ·
        refine ⟨4216619745652987216156067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811079830435324810770711 4216619745652987216156067)
        ·
          refine ⟨6324929618479480824234101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216619745652987216156067 6324929618479480824234101)
          ·
            refine ⟨592962151732451327271947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6324929618479480824234101 592962151732451327271947)
            ·
              refine ⟨889443227598676990907921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592962151732451327271947 889443227598676990907921)
              ·
                refine ⟨667082420699007743180941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889443227598676990907921 667082420699007743180941)
                ·
                  refine ⟨250155907762127903692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667082420699007743180941 250155907762127903692853)
                  ·
                    rfl

theorem cell20_548074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_548074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548074 prefixEnd_548074 := by exact prefixLift 548074
  have htrace : WordTrace (prefixWord ++ tailWord_548074) baseStart_548074 baseEnd_548074 := by
    simpa [prefixWord, tailWord_548074, baseEnd_548074] using wordTrace_append hprefix tailTrace_548074
  have hstable : (prefixWord ++ tailWord_548074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548074).length < 2 ^ (prefixWord ++ tailWord_548074).sum := by decide
  have hdescent : baseEnd_548074 < baseStart_548074 := by decide
  rcases family_descends (prefixWord ++ tailWord_548074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548147 : List Nat := [1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_548147 : Nat := 118140960795 + 548147 * 2 ^ 59
def prefixEnd_548147 : Nat := 4983230072969 + 3 ^ 40 * 548147 * 2
def baseEnd_548147 : Nat := 83396408983754698086407

theorem tailTrace_548147 : CollatzResearch.WordTrace tailWord_548147 prefixEnd_548147 83396408983754698086407 := by
  unfold tailWord_548147
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992563545164509899554695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13328375696776339933036463 19992563545164509899554695)
  ·
    refine ⟨29988845317746764849332043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19992563545164509899554695 29988845317746764849332043)
    ·
      refine ⟨44983267976620147273998065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29988845317746764849332043 44983267976620147273998065)
      ·
        refine ⟨33737450982465110455498549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44983267976620147273998065 33737450982465110455498549)
        ·
          refine ⟨3162886029606104105202989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33737450982465110455498549 3162886029606104105202989)
          ·
            refine ⟨1186082261102289039451121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3162886029606104105202989 1186082261102289039451121)
            ·
              refine ⟨889561695826716779588341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186082261102289039451121 889561695826716779588341)
              ·
                refine ⟨83396408983754698086407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 889561695826716779588341 83396408983754698086407)
                ·
                  rfl

theorem cell20_548147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_548147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548147 prefixEnd_548147 := by exact prefixLift 548147
  have htrace : WordTrace (prefixWord ++ tailWord_548147) baseStart_548147 baseEnd_548147 := by
    simpa [prefixWord, tailWord_548147, baseEnd_548147] using wordTrace_append hprefix tailTrace_548147
  have hstable : (prefixWord ++ tailWord_548147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548147).length < 2 ^ (prefixWord ++ tailWord_548147).sum := by decide
  have hdescent : baseEnd_548147 < baseStart_548147 := by decide
  rcases family_descends (prefixWord ++ tailWord_548147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548164 : List Nat := [2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_548164 : Nat := 118140960795 + 548164 * 2 ^ 59
def prefixEnd_548164 : Nat := 4983230072969 + 3 ^ 40 * 548164 * 2
def baseEnd_548164 : Nat := 83398995404829196897495

theorem tailTrace_548164 : CollatzResearch.WordTrace tailWord_548164 prefixEnd_548164 83398995404829196897495 := by
  unfold tailWord_548164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996591793051460901461773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13328789057401947868615697 9996591793051460901461773)
  ·
    refine ⟨3748721922394297838048165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9996591793051460901461773 3748721922394297838048165)
    ·
      refine ⟨702885360448930844634031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3748721922394297838048165 702885360448930844634031)
      ·
        refine ⟨1054328040673396266951047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702885360448930844634031 1054328040673396266951047)
        ·
          refine ⟨1581492061010094400426571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054328040673396266951047 1581492061010094400426571)
          ·
            refine ⟨2372238091515141600639857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581492061010094400426571 2372238091515141600639857)
            ·
              refine ⟨1779178568636356200479893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372238091515141600639857 1779178568636356200479893)
              ·
                refine ⟨83398995404829196897495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1779178568636356200479893 83398995404829196897495)
                ·
                  rfl

theorem cell20_548164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_548164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548164 prefixEnd_548164 := by exact prefixLift 548164
  have htrace : WordTrace (prefixWord ++ tailWord_548164) baseStart_548164 baseEnd_548164 := by
    simpa [prefixWord, tailWord_548164, baseEnd_548164] using wordTrace_append hprefix tailTrace_548164
  have hstable : (prefixWord ++ tailWord_548164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548164).length < 2 ^ (prefixWord ++ tailWord_548164).sum := by decide
  have hdescent : baseEnd_548164 < baseStart_548164 := by decide
  rcases family_descends (prefixWord ++ tailWord_548164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548195 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 2]
def baseStart_548195 : Nat := 118140960795 + 548195 * 2 ^ 59
def prefixEnd_548195 : Nat := 4983230072969 + 3 ^ 40 * 548195 * 2
def baseEnd_548195 : Nat := 250211135459189260659025

theorem tailTrace_548195 : CollatzResearch.WordTrace tailWord_548195 prefixEnd_548195 250211135459189260659025 := by
  unfold tailWord_548195
  simp only [CollatzResearch.WordTrace]
  refine ⟨19994314248990614097302039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13329542832660409398201359 19994314248990614097302039)
  ·
    refine ⟨29991471373485921145953059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19994314248990614097302039 29991471373485921145953059)
    ·
      refine ⟨44987207060228881718929589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29991471373485921145953059 44987207060228881718929589)
      ·
        refine ⟨4217550661896457661149649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44987207060228881718929589 4217550661896457661149649)
        ·
          refine ⟨3163162996422343245862237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4217550661896457661149649 3163162996422343245862237)
          ·
            refine ⟨1186186123658378717198339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3163162996422343245862237 1186186123658378717198339)
            ·
              refine ⟨1779279185487568075797509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186186123658378717198339 1779279185487568075797509)
              ·
                refine ⟨333614847278919014212033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1779279185487568075797509 333614847278919014212033)
                ·
                  refine ⟨250211135459189260659025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333614847278919014212033 250211135459189260659025)
                  ·
                    rfl

theorem cell20_548195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2].length) (baseStart_548195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548195 prefixEnd_548195 := by exact prefixLift 548195
  have htrace : WordTrace (prefixWord ++ tailWord_548195) baseStart_548195 baseEnd_548195 := by
    simpa [prefixWord, tailWord_548195, baseEnd_548195] using wordTrace_append hprefix tailTrace_548195
  have hstable : (prefixWord ++ tailWord_548195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548195).length < 2 ^ (prefixWord ++ tailWord_548195).sum := by decide
  have hdescent : baseEnd_548195 < baseStart_548195 := by decide
  rcases family_descends (prefixWord ++ tailWord_548195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548251 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_548251 : Nat := 118140960795 + 548251 * 2 ^ 59
def prefixEnd_548251 : Nat := 4983230072969 + 3 ^ 40 * 548251 * 2
def baseEnd_548251 : Nat := 250236695385101954792129

theorem tailTrace_548251 : CollatzResearch.WordTrace tailWord_548251 prefixEnd_548251 250236695385101954792129 := by
  unfold tailWord_548251
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996356736787735661340607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13330904491191823774227071 19996356736787735661340607)
  ·
    refine ⟨29994535105181603492010911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19996356736787735661340607 29994535105181603492010911)
    ·
      refine ⟨44991802657772405238016367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29994535105181603492010911 44991802657772405238016367)
      ·
        refine ⟨67487703986658607857024551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44991802657772405238016367 67487703986658607857024551)
        ·
          refine ⟨101231555979987911785536827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67487703986658607857024551 101231555979987911785536827)
          ·
            refine ⟨151847333969981867678305241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101231555979987911785536827 151847333969981867678305241)
            ·
              refine ⟨113885500477486400758728931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151847333969981867678305241 113885500477486400758728931)
              ·
                refine ⟨170828250716229601138093397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113885500477486400758728931 170828250716229601138093397)
                ·
                  refine ⟨250236695385101954792129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 170828250716229601138093397 250236695385101954792129)
                  ·
                    rfl

theorem cell20_548251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_548251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548251 prefixEnd_548251 := by exact prefixLift 548251
  have htrace : WordTrace (prefixWord ++ tailWord_548251) baseStart_548251 baseEnd_548251 := by
    simpa [prefixWord, tailWord_548251, baseEnd_548251] using wordTrace_append hprefix tailTrace_548251
  have hstable : (prefixWord ++ tailWord_548251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548251).length < 2 ^ (prefixWord ++ tailWord_548251).sum := by decide
  have hdescent : baseEnd_548251 < baseStart_548251 := by decide
  rcases family_descends (prefixWord ++ tailWord_548251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548268 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_548268 : Nat := 118140960795 + 548268 * 2 ^ 59
def prefixEnd_548268 : Nat := 4983230072969 + 3 ^ 40 * 548268 * 2
def baseEnd_548268 : Nat := 250244454648325451225393

theorem tailTrace_548268 : CollatzResearch.WordTrace tailWord_548268 prefixEnd_548268 250244454648325451225393 := by
  unfold tailWord_548268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998488388863073782354729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13331317851817431709806305 9998488388863073782354729)
  ·
    refine ⟨7498866291647305336766047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9998488388863073782354729 7498866291647305336766047)
    ·
      refine ⟨11248299437470958005149071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7498866291647305336766047 11248299437470958005149071)
      ·
        refine ⟨16872449156206437007723607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11248299437470958005149071 16872449156206437007723607)
        ·
          refine ⟨25308673734309655511585411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16872449156206437007723607 25308673734309655511585411)
          ·
            refine ⟨37963010601464483267378117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25308673734309655511585411 37963010601464483267378117)
            ·
              refine ⟨7118064487774590612633397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37963010601464483267378117 7118064487774590612633397)
              ·
                refine ⟨667318545728867869934381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7118064487774590612633397 667318545728867869934381)
                ·
                  refine ⟨250244454648325451225393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667318545728867869934381 250244454648325451225393)
                  ·
                    rfl

theorem cell20_548268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_548268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548268 prefixEnd_548268 := by exact prefixLift 548268
  have htrace : WordTrace (prefixWord ++ tailWord_548268) baseStart_548268 baseEnd_548268 := by
    simpa [prefixWord, tailWord_548268, baseEnd_548268] using wordTrace_append hprefix tailTrace_548268
  have hstable : (prefixWord ++ tailWord_548268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548268).length < 2 ^ (prefixWord ++ tailWord_548268).sum := by decide
  have hdescent : baseEnd_548268 < baseStart_548268 := by decide
  rcases family_descends (prefixWord ++ tailWord_548268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548323 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_548323 : Nat := 118140960795 + 548323 * 2 ^ 59
def prefixEnd_548323 : Nat := 4983230072969 + 3 ^ 40 * 548323 * 2
def baseEnd_548323 : Nat := 250269558146989704391835

theorem tailTrace_548323 : CollatzResearch.WordTrace tailWord_548323 prefixEnd_548323 250269558146989704391835 := by
  unfold tailWord_548323
  simp only [CollatzResearch.WordTrace]
  refine ⟨19998982792526891957961623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13332655195017927971974415 19998982792526891957961623)
  ·
    refine ⟨29998474188790337936942435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19998982792526891957961623 29998474188790337936942435)
    ·
      refine ⟨44997711283185506905413653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29998474188790337936942435 44997711283185506905413653)
      ·
        refine ⟨2109267716399320636191265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44997711283185506905413653 2109267716399320636191265)
        ·
          refine ⟨1581950787299490477143449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109267716399320636191265 1581950787299490477143449)
          ·
            refine ⟨1186463090474617857857587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581950787299490477143449 1186463090474617857857587)
            ·
              refine ⟨1779694635711926786786381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186463090474617857857587 1779694635711926786786381)
              ·
                refine ⟨667385488391972545044893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1779694635711926786786381 667385488391972545044893)
                ·
                  refine ⟨250269558146989704391835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667385488391972545044893 250269558146989704391835)
                  ·
                    rfl

theorem cell20_548323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_548323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548323 prefixEnd_548323 := by exact prefixLift 548323
  have htrace : WordTrace (prefixWord ++ tailWord_548323) baseStart_548323 baseEnd_548323 := by
    simpa [prefixWord, tailWord_548323, baseEnd_548323] using wordTrace_append hprefix tailTrace_548323
  have hstable : (prefixWord ++ tailWord_548323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548323).length < 2 ^ (prefixWord ++ tailWord_548323).sum := by decide
  have hdescent : baseEnd_548323 < baseStart_548323 := by decide
  rcases family_descends (prefixWord ++ tailWord_548323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548413 : List Nat := [1, 4, 1, 3, 3, 1, 7]
def baseStart_548413 : Nat := 118140960795 + 548413 * 2 ^ 59
def prefixEnd_548413 : Nat := 4983230072969 + 3 ^ 40 * 548413 * 2
def baseEnd_548413 : Nat := 27812292955483265710163

theorem tailTrace_548413 : CollatzResearch.WordTrace tailWord_548413 prefixEnd_548413 27812292955483265710163 := by
  unfold tailWord_548413
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002265362200837328737893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13334843574800558219158595 20002265362200837328737893)
  ·
    refine ⟨3750424755412656999138355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20002265362200837328737893 3750424755412656999138355)
    ·
      refine ⟨5625637133118985498707533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750424755412656999138355 5625637133118985498707533)
      ·
        refine ⟨2109613924919619562015325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5625637133118985498707533 2109613924919619562015325)
        ·
          refine ⟨791105221844857335755747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2109613924919619562015325 791105221844857335755747)
          ·
            refine ⟨1186657832767286003633621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791105221844857335755747 1186657832767286003633621)
            ·
              refine ⟨27812292955483265710163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1186657832767286003633621 27812292955483265710163)
              ·
                rfl

theorem cell20_548413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_548413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548413 prefixEnd_548413 := by exact prefixLift 548413
  have htrace : WordTrace (prefixWord ++ tailWord_548413) baseStart_548413 baseEnd_548413 := by
    simpa [prefixWord, tailWord_548413, baseEnd_548413] using wordTrace_append hprefix tailTrace_548413
  have hstable : (prefixWord ++ tailWord_548413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548413).length < 2 ^ (prefixWord ++ tailWord_548413).sum := by decide
  have hdescent : baseEnd_548413 < baseStart_548413 := by decide
  rcases family_descends (prefixWord ++ tailWord_548413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548444 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_548444 : Nat := 118140960795 + 548444 * 2 ^ 59
def prefixEnd_548444 : Nat := 4983230072969 + 3 ^ 40 * 548444 * 2
def baseEnd_548444 : Nat := 250324785844051061358007

theorem tailTrace_548444 : CollatzResearch.WordTrace tailWord_548444 prefixEnd_548444 250324785844051061358007 := by
  unfold tailWord_548444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001698012544264811558193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13335597350059019748744257 10001698012544264811558193)
  ·
    refine ⟨7501273509408198608668645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10001698012544264811558193 7501273509408198608668645)
    ·
      refine ⟨1406488783014037239125371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7501273509408198608668645 1406488783014037239125371)
      ·
        refine ⟨2109733174521055858688057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406488783014037239125371 2109733174521055858688057)
        ·
          refine ⟨1582299880890791894016043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109733174521055858688057 1582299880890791894016043)
          ·
            refine ⟨2373449821336187841024065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582299880890791894016043 2373449821336187841024065)
            ·
              refine ⟨1780087366002140880768049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373449821336187841024065 1780087366002140880768049)
              ·
                refine ⟨1335065524501605660576037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780087366002140880768049 1335065524501605660576037)
                ·
                  refine ⟨250324785844051061358007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335065524501605660576037 250324785844051061358007)
                  ·
                    rfl

theorem cell20_548444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_548444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548444 prefixEnd_548444 := by exact prefixLift 548444
  have htrace : WordTrace (prefixWord ++ tailWord_548444) baseStart_548444 baseEnd_548444 := by
    simpa [prefixWord, tailWord_548444, baseEnd_548444] using wordTrace_append hprefix tailTrace_548444
  have hstable : (prefixWord ++ tailWord_548444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548444).length < 2 ^ (prefixWord ++ tailWord_548444).sum := by decide
  have hdescent : baseEnd_548444 < baseStart_548444 := by decide
  rcases family_descends (prefixWord ++ tailWord_548444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548451 : List Nat := [1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_548451 : Nat := 118140960795 + 548451 * 2 ^ 59
def prefixEnd_548451 : Nat := 4983230072969 + 3 ^ 40 * 548451 * 2
def baseEnd_548451 : Nat := 83442660278263382708215

theorem tailTrace_548451 : CollatzResearch.WordTrace tailWord_548451 prefixEnd_548451 83442660278263382708215 := by
  unfold tailWord_548451
  simp only [CollatzResearch.WordTrace]
  refine ⟨20003651336063169818621207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13335767557375446545747471 20003651336063169818621207)
  ·
    refine ⟨30005477004094754727931811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20003651336063169818621207 30005477004094754727931811)
    ·
      refine ⟨45008215506142132091897717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30005477004094754727931811 45008215506142132091897717)
      ·
        refine ⟨4219520203700824883615411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45008215506142132091897717 4219520203700824883615411)
        ·
          refine ⟨6329280305551237325423117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219520203700824883615411 6329280305551237325423117)
          ·
            refine ⟨2373480114581713997033669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6329280305551237325423117 2373480114581713997033669)
            ·
              refine ⟨445027521484071374443813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2373480114581713997033669 445027521484071374443813)
              ·
                refine ⟨83442660278263382708215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445027521484071374443813 83442660278263382708215)
                ·
                  rfl

theorem cell20_548451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_548451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548451 prefixEnd_548451 := by exact prefixLift 548451
  have htrace : WordTrace (prefixWord ++ tailWord_548451) baseStart_548451 baseEnd_548451 := by
    simpa [prefixWord, tailWord_548451, baseEnd_548451] using wordTrace_append hprefix tailTrace_548451
  have hstable : (prefixWord ++ tailWord_548451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548451).length < 2 ^ (prefixWord ++ tailWord_548451).sum := by decide
  have hdescent : baseEnd_548451 < baseStart_548451 := by decide
  rcases family_descends (prefixWord ++ tailWord_548451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548458 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_548458 : Nat := 118140960795 + 548458 * 2 ^ 59
def prefixEnd_548458 : Nat := 4983230072969 + 3 ^ 40 * 548458 * 2
def baseEnd_548458 : Nat := 250331175825529234891283

theorem tailTrace_548458 : CollatzResearch.WordTrace tailWord_548458 prefixEnd_548458 250331175825529234891283 := by
  unfold tailWord_548458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000976661759452503531507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13335937764691873342750685 5000976661759452503531507)
  ·
    refine ⟨7501464992639178755297261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000976661759452503531507 7501464992639178755297261)
    ·
      refine ⟨2813049372239692033236473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7501464992639178755297261 2813049372239692033236473)
      ·
        refine ⟨2109787029179769024927355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813049372239692033236473 2109787029179769024927355)
        ·
          refine ⟨3164680543769653537391033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109787029179769024927355 3164680543769653537391033)
          ·
            refine ⟨2373510407827240153043275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164680543769653537391033 2373510407827240153043275)
            ·
              refine ⟨3560265611740860229564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373510407827240153043275 3560265611740860229564913)
              ·
                refine ⟨2670199208805645172173685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3560265611740860229564913 2670199208805645172173685)
                ·
                  refine ⟨250331175825529234891283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670199208805645172173685 250331175825529234891283)
                  ·
                    rfl

theorem cell20_548458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_548458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548458 prefixEnd_548458 := by exact prefixLift 548458
  have htrace : WordTrace (prefixWord ++ tailWord_548458) baseStart_548458 baseEnd_548458 := by
    simpa [prefixWord, tailWord_548458, baseEnd_548458] using wordTrace_append hprefix tailTrace_548458
  have hstable : (prefixWord ++ tailWord_548458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548458).length < 2 ^ (prefixWord ++ tailWord_548458).sum := by decide
  have hdescent : baseEnd_548458 < baseStart_548458 := by decide
  rcases family_descends (prefixWord ++ tailWord_548458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548488 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_548488 : Nat := 118140960795 + 548488 * 2 ^ 59
def prefixEnd_548488 : Nat := 4983230072969 + 3 ^ 40 * 548488 * 2
def baseEnd_548488 : Nat := 250344868642982463891161

theorem tailTrace_548488 : CollatzResearch.WordTrace tailWord_548488 prefixEnd_548488 250344868642982463891161 := by
  unfold tailWord_548488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002500418464562568859059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13336667224619416758478745 10002500418464562568859059)
  ·
    refine ⟨15003750627696843853288589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10002500418464562568859059 15003750627696843853288589)
    ·
      refine ⟨5626406485386316444983221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15003750627696843853288589 5626406485386316444983221)
      ·
        refine ⟨527475608004967166717177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5626406485386316444983221 527475608004967166717177)
        ·
          refine ⟨395606706003725375037883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527475608004967166717177 395606706003725375037883)
          ·
            refine ⟨593410059005588062556825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395606706003725375037883 593410059005588062556825)
            ·
              refine ⟨445057544254191046917619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593410059005588062556825 445057544254191046917619)
              ·
                refine ⟨667586316381286570376429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445057544254191046917619 667586316381286570376429)
                ·
                  refine ⟨250344868642982463891161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667586316381286570376429 250344868642982463891161)
                  ·
                    rfl

theorem cell20_548488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_548488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548488 prefixEnd_548488 := by exact prefixLift 548488
  have htrace : WordTrace (prefixWord ++ tailWord_548488) baseStart_548488 baseEnd_548488 := by
    simpa [prefixWord, tailWord_548488, baseEnd_548488] using wordTrace_append hprefix tailTrace_548488
  have hstable : (prefixWord ++ tailWord_548488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548488).length < 2 ^ (prefixWord ++ tailWord_548488).sum := by decide
  have hdescent : baseEnd_548488 < baseStart_548488 := by decide
  rcases family_descends (prefixWord ++ tailWord_548488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548517 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_548517 : Nat := 118140960795 + 548517 * 2 ^ 59
def prefixEnd_548517 : Nat := 4983230072969 + 3 ^ 40 * 548517 * 2
def baseEnd_548517 : Nat := 250358105033187251924375

theorem tailTrace_548517 : CollatzResearch.WordTrace tailWord_548517 prefixEnd_548517 250358105033187251924375 := by
  unfold tailWord_548517
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006058553824063090523805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337372369216042060349203 20006058553824063090523805)
  ·
    refine ⟨7502271957684023658946427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20006058553824063090523805 7502271957684023658946427)
    ·
      refine ⟨11253407936526035488419641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502271957684023658946427 11253407936526035488419641)
      ·
        refine ⟨8440055952394526616314731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11253407936526035488419641 8440055952394526616314731)
        ·
          refine ⟨12660083928591789924472097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8440055952394526616314731 12660083928591789924472097)
          ·
            refine ⟨9495062946443842443354073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12660083928591789924472097 9495062946443842443354073)
            ·
              refine ⟨7121297209832881832515555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9495062946443842443354073 7121297209832881832515555)
              ·
                refine ⟨10681945814749322748773333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7121297209832881832515555 10681945814749322748773333)
                ·
                  refine ⟨250358105033187251924375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10681945814749322748773333 250358105033187251924375)
                  ·
                    rfl

theorem cell20_548517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_548517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548517 prefixEnd_548517 := by exact prefixLift 548517
  have htrace : WordTrace (prefixWord ++ tailWord_548517) baseStart_548517 baseEnd_548517 := by
    simpa [prefixWord, tailWord_548517, baseEnd_548517] using wordTrace_append hprefix tailTrace_548517
  have hstable : (prefixWord ++ tailWord_548517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548517).length < 2 ^ (prefixWord ++ tailWord_548517).sum := by decide
  have hdescent : baseEnd_548517 < baseStart_548517 := by decide
  rcases family_descends (prefixWord ++ tailWord_548517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548533 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 2]
def baseStart_548533 : Nat := 118140960795 + 548533 * 2 ^ 59
def prefixEnd_548533 : Nat := 4983230072969 + 3 ^ 40 * 548533 * 2
def baseEnd_548533 : Nat := 250365407869162307390977

theorem tailTrace_548533 : CollatzResearch.WordTrace tailWord_548533 prefixEnd_548533 250365407869162307390977 := by
  unfold tailWord_548533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006642121766097823106253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337761414510731882070835 20006642121766097823106253)
  ·
    refine ⟨7502490795662286683664845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20006642121766097823106253 7502490795662286683664845)
    ·
      refine ⟨2813434048373357506374317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7502490795662286683664845 2813434048373357506374317)
      ·
        refine ⟨1055037768140009064890369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2813434048373357506374317 1055037768140009064890369)
        ·
          refine ⟨791278326105006798667777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055037768140009064890369 791278326105006798667777)
          ·
            refine ⟨593458744578755099000833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791278326105006798667777 593458744578755099000833)
            ·
              refine ⟨445094058434066324250625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593458744578755099000833 445094058434066324250625)
              ·
                refine ⟨333820543825549743187969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445094058434066324250625 333820543825549743187969)
                ·
                  refine ⟨250365407869162307390977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333820543825549743187969 250365407869162307390977)
                  ·
                    rfl

theorem cell20_548533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_548533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548533 prefixEnd_548533 := by exact prefixLift 548533
  have htrace : WordTrace (prefixWord ++ tailWord_548533) baseStart_548533 baseEnd_548533 := by
    simpa [prefixWord, tailWord_548533, baseEnd_548533] using wordTrace_append hprefix tailTrace_548533
  have hstable : (prefixWord ++ tailWord_548533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548533).length < 2 ^ (prefixWord ++ tailWord_548533).sum := by decide
  have hdescent : baseEnd_548533 < baseStart_548533 := by decide
  rcases family_descends (prefixWord ++ tailWord_548533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548537 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 2]
def baseStart_548537 : Nat := 118140960795 + 548537 * 2 ^ 59
def prefixEnd_548537 : Nat := 4983230072969 + 3 ^ 40 * 548537 * 2
def baseEnd_548537 : Nat := 250367233578156071257627

theorem tailTrace_548537 : CollatzResearch.WordTrace tailWord_548537 prefixEnd_548537 250367233578156071257627 := by
  unfold tailWord_548537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006788013751606506251865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337858675834404337501243 20006788013751606506251865)
  ·
    refine ⟨15005091010313704879688899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20006788013751606506251865 15005091010313704879688899)
    ·
      refine ⟨22507636515470557319533349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15005091010313704879688899 22507636515470557319533349)
      ·
        refine ⟨4220181846650729497412503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22507636515470557319533349 4220181846650729497412503)
        ·
          refine ⟨6330272769976094246118755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220181846650729497412503 6330272769976094246118755)
          ·
            refine ⟨9495409154964141369178133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330272769976094246118755 9495409154964141369178133)
            ·
              refine ⟨445097304138944126680225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9495409154964141369178133 445097304138944126680225)
              ·
                refine ⟨333822978104208095010169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445097304138944126680225 333822978104208095010169)
                ·
                  refine ⟨250367233578156071257627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333822978104208095010169 250367233578156071257627)
                  ·
                    rfl

theorem cell20_548537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_548537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548537 prefixEnd_548537 := by exact prefixLift 548537
  have htrace : WordTrace (prefixWord ++ tailWord_548537) baseStart_548537 baseEnd_548537 := by
    simpa [prefixWord, tailWord_548537, baseEnd_548537] using wordTrace_append hprefix tailTrace_548537
  have hstable : (prefixWord ++ tailWord_548537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548537).length < 2 ^ (prefixWord ++ tailWord_548537).sum := by decide
  have hdescent : baseEnd_548537 < baseStart_548537 := by decide
  rcases family_descends (prefixWord ++ tailWord_548537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548541 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_548541 : Nat := 118140960795 + 548541 * 2 ^ 59
def prefixEnd_548541 : Nat := 4983230072969 + 3 ^ 40 * 548541 * 2
def baseEnd_548541 : Nat := 250369059287149835124277

theorem tailTrace_548541 : CollatzResearch.WordTrace tailWord_548541 prefixEnd_548541 250369059287149835124277 := by
  unfold tailWord_548541
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006933905737115189397477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337955937158076792931651 20006933905737115189397477)
  ·
    refine ⟨3751300107325709098012027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20006933905737115189397477 3751300107325709098012027)
    ·
      refine ⟨5626950160988563647018041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751300107325709098012027 5626950160988563647018041)
      ·
        refine ⟨4220212620741422735263531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5626950160988563647018041 4220212620741422735263531)
        ·
          refine ⟨6330318931112134102895297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220212620741422735263531 6330318931112134102895297)
          ·
            refine ⟨4747739198334100577171473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330318931112134102895297 4747739198334100577171473)
            ·
              refine ⟨3560804398750575432878605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4747739198334100577171473 3560804398750575432878605)
              ·
                refine ⟨1335301649531465787329477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3560804398750575432878605 1335301649531465787329477)
                ·
                  refine ⟨250369059287149835124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1335301649531465787329477 250369059287149835124277)
                  ·
                    rfl

theorem cell20_548541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_548541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548541 prefixEnd_548541 := by exact prefixLift 548541
  have htrace : WordTrace (prefixWord ++ tailWord_548541) baseStart_548541 baseEnd_548541 := by
    simpa [prefixWord, tailWord_548541, baseEnd_548541] using wordTrace_append hprefix tailTrace_548541
  have hstable : (prefixWord ++ tailWord_548541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548541).length < 2 ^ (prefixWord ++ tailWord_548541).sum := by decide
  have hdescent : baseEnd_548541 < baseStart_548541 := by decide
  rcases family_descends (prefixWord ++ tailWord_548541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548589 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_548589 : Nat := 118140960795 + 548589 * 2 ^ 59
def prefixEnd_548589 : Nat := 4983230072969 + 3 ^ 40 * 548589 * 2
def baseEnd_548589 : Nat := 250390967795075001524081

theorem tailTrace_548589 : CollatzResearch.WordTrace tailWord_548589 prefixEnd_548589 250390967795075001524081 := by
  unfold tailWord_548589
  simp only [CollatzResearch.WordTrace]
  refine ⟨20008684609563219387144821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13339123073042146258096547 20008684609563219387144821)
  ·
    refine ⟨1875814182146551817544827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20008684609563219387144821 1875814182146551817544827)
    ·
      refine ⟨2813721273219827726317241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875814182146551817544827 2813721273219827726317241)
      ·
        refine ⟨2110290954914870794737931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813721273219827726317241 2110290954914870794737931)
        ·
          refine ⟨3165436432372306192106897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110290954914870794737931 3165436432372306192106897)
          ·
            refine ⟨2374077324279229644080173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3165436432372306192106897 2374077324279229644080173)
            ·
              refine ⟨890278996604711116530065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374077324279229644080173 890278996604711116530065)
              ·
                refine ⟨667709247453533337397549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890278996604711116530065 667709247453533337397549)
                ·
                  refine ⟨250390967795075001524081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667709247453533337397549 250390967795075001524081)
                  ·
                    rfl

theorem cell20_548589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_548589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548589 prefixEnd_548589 := by exact prefixLift 548589
  have htrace : WordTrace (prefixWord ++ tailWord_548589) baseStart_548589 baseEnd_548589 := by
    simpa [prefixWord, tailWord_548589, baseEnd_548589] using wordTrace_append hprefix tailTrace_548589
  have hstable : (prefixWord ++ tailWord_548589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548589).length < 2 ^ (prefixWord ++ tailWord_548589).sum := by decide
  have hdescent : baseEnd_548589 < baseStart_548589 := by decide
  rcases family_descends (prefixWord ++ tailWord_548589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548648 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_548648 : Nat := 118140960795 + 548648 * 2 ^ 59
def prefixEnd_548648 : Nat := 4983230072969 + 3 ^ 40 * 548648 * 2
def baseEnd_548648 : Nat := 250417897002733018557173

theorem tailTrace_548648 : CollatzResearch.WordTrace tailWord_548648 prefixEnd_548648 250417897002733018557173 := by
  unfold tailWord_548648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005418258174736231771299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13340557677566314975695065 10005418258174736231771299)
  ·
    refine ⟨15008127387262104347656949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10005418258174736231771299 15008127387262104347656949)
    ·
      refine ⟨1407011942555822282592839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15008127387262104347656949 1407011942555822282592839)
      ·
        refine ⟨2110517913833733423889259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407011942555822282592839 2110517913833733423889259)
        ·
          refine ⟨3165776870750600135833889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110517913833733423889259 3165776870750600135833889)
          ·
            refine ⟨2374332653062950101875417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3165776870750600135833889 2374332653062950101875417)
            ·
              refine ⟨1780749489797212576406563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374332653062950101875417 1780749489797212576406563)
              ·
                refine ⟨2671124234695818864609845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780749489797212576406563 2671124234695818864609845)
                ·
                  refine ⟨250417897002733018557173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671124234695818864609845 250417897002733018557173)
                  ·
                    rfl

theorem cell20_548648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_548648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548648 prefixEnd_548648 := by exact prefixLift 548648
  have htrace : WordTrace (prefixWord ++ tailWord_548648) baseStart_548648 baseEnd_548648 := by
    simpa [prefixWord, tailWord_548648, baseEnd_548648] using wordTrace_append hprefix tailTrace_548648
  have hstable : (prefixWord ++ tailWord_548648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548648).length < 2 ^ (prefixWord ++ tailWord_548648).sum := by decide
  have hdescent : baseEnd_548648 < baseStart_548648 := by decide
  rcases family_descends (prefixWord ++ tailWord_548648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548661 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 3]
def baseStart_548661 : Nat := 118140960795 + 548661 * 2 ^ 59
def prefixEnd_548661 : Nat := 4983230072969 + 3 ^ 40 * 548661 * 2
def baseEnd_548661 : Nat := 250423830556962751123787

theorem tailTrace_548661 : CollatzResearch.WordTrace tailWord_548661 prefixEnd_548661 250423830556962751123787 := by
  unfold tailWord_548661
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011310665302375683765837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13340873776868250455843891 20011310665302375683765837)
  ·
    refine ⟨7504241499488390881412189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20011310665302375683765837 7504241499488390881412189)
    ·
      refine ⟨2814090562308146580529571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7504241499488390881412189 2814090562308146580529571)
      ·
        refine ⟨4221135843462219870794357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814090562308146580529571 4221135843462219870794357)
        ·
          refine ⟨395731485324583112886971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4221135843462219870794357 395731485324583112886971)
          ·
            refine ⟨593597227986874669330457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395731485324583112886971 593597227986874669330457)
            ·
              refine ⟨445197920990156001997843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593597227986874669330457 445197920990156001997843)
              ·
                refine ⟨667796881485234002996765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445197920990156001997843 667796881485234002996765)
                ·
                  refine ⟨250423830556962751123787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667796881485234002996765 250423830556962751123787)
                  ·
                    rfl

theorem cell20_548661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_548661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548661 prefixEnd_548661 := by exact prefixLift 548661
  have htrace : WordTrace (prefixWord ++ tailWord_548661) baseStart_548661 baseEnd_548661 := by
    simpa [prefixWord, tailWord_548661, baseEnd_548661] using wordTrace_append hprefix tailTrace_548661
  have hstable : (prefixWord ++ tailWord_548661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548661).length < 2 ^ (prefixWord ++ tailWord_548661).sum := by decide
  have hdescent : baseEnd_548661 < baseStart_548661 := by decide
  rcases family_descends (prefixWord ++ tailWord_548661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548700 : List Nat := [2, 2, 4, 2, 10]
def baseStart_548700 : Nat := 118140960795 + 548700 * 2 ^ 59
def prefixEnd_548700 : Nat := 4983230072969 + 3 ^ 40 * 548700 * 2
def baseEnd_548700 : Nat := 3091871990366073442267

theorem tailTrace_548700 : CollatzResearch.WordTrace tailWord_548700 prefixEnd_548700 3091871990366073442267 := by
  unfold tailWord_548700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006366556080542672217777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13341822074774056896290369 10006366556080542672217777)
  ·
    refine ⟨7504774917060407004163333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10006366556080542672217777 7504774917060407004163333)
    ·
      refine ⟨1407145296948826313280625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7504774917060407004163333 1407145296948826313280625)
      ·
        refine ⟨1055358972711619734960469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1407145296948826313280625 1055358972711619734960469)
        ·
          refine ⟨3091871990366073442267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1055358972711619734960469 3091871990366073442267)
          ·
            rfl

theorem cell20_548700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 10].length) (baseStart_548700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548700 prefixEnd_548700 := by exact prefixLift 548700
  have htrace : WordTrace (prefixWord ++ tailWord_548700) baseStart_548700 baseEnd_548700 := by
    simpa [prefixWord, tailWord_548700, baseEnd_548700] using wordTrace_append hprefix tailTrace_548700
  have hstable : (prefixWord ++ tailWord_548700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548700).length < 2 ^ (prefixWord ++ tailWord_548700).sum := by decide
  have hdescent : baseEnd_548700 < baseStart_548700 := by decide
  rcases family_descends (prefixWord ++ tailWord_548700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548706 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_548706 : Nat := 118140960795 + 548706 * 2 ^ 59
def prefixEnd_548706 : Nat := 4983230072969 + 3 ^ 40 * 548706 * 2
def baseEnd_548706 : Nat := 250444369783142594623603

theorem tailTrace_548706 : CollatzResearch.WordTrace tailWord_548706 prefixEnd_548706 250444369783142594623603 := by
  unfold tailWord_548706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003237987534837092288493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13341967966759565579435981 5003237987534837092288493)
  ·
    refine ⟨1876214245325563909608185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5003237987534837092288493 1876214245325563909608185)
    ·
      refine ⟨1407160683994172932206139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876214245325563909608185 1407160683994172932206139)
      ·
        refine ⟨2110741025991259398309209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407160683994172932206139 2110741025991259398309209)
        ·
          refine ⟨1583055769493444548731907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110741025991259398309209 1583055769493444548731907)
          ·
            refine ⟨2374583654240166823097861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583055769493444548731907 2374583654240166823097861)
            ·
              refine ⟨445234435170031279330849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2374583654240166823097861 445234435170031279330849)
              ·
                refine ⟨333925826377523459498137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445234435170031279330849 333925826377523459498137)
                ·
                  refine ⟨250444369783142594623603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333925826377523459498137 250444369783142594623603)
                  ·
                    rfl

theorem cell20_548706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_548706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548706 prefixEnd_548706 := by exact prefixLift 548706
  have htrace : WordTrace (prefixWord ++ tailWord_548706) baseStart_548706 baseEnd_548706 := by
    simpa [prefixWord, tailWord_548706, baseEnd_548706] using wordTrace_append hprefix tailTrace_548706
  have hstable : (prefixWord ++ tailWord_548706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548706).length < 2 ^ (prefixWord ++ tailWord_548706).sum := by decide
  have hdescent : baseEnd_548706 < baseStart_548706 := by decide
  rcases family_descends (prefixWord ++ tailWord_548706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548745 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_548745 : Nat := 118140960795 + 548745 * 2 ^ 59
def prefixEnd_548745 : Nat := 4983230072969 + 3 ^ 40 * 548745 * 2
def baseEnd_548745 : Nat := 250462170445831792323443

theorem tailTrace_548745 : CollatzResearch.WordTrace tailWord_548745 prefixEnd_548745 250462170445831792323443 := by
  unfold tailWord_548745
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014374396998058029823689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13342916264665372019882459 20014374396998058029823689)
  ·
    refine ⟨15010780797748543522367767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20014374396998058029823689 15010780797748543522367767)
    ·
      refine ⟨22516171196622815283551651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15010780797748543522367767 22516171196622815283551651)
      ·
        refine ⟨33774256794934222925327477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22516171196622815283551651 33774256794934222925327477)
        ·
          refine ⟨3166336574525083399249451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33774256794934222925327477 3166336574525083399249451)
          ·
            refine ⟨4749504861787625098874177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166336574525083399249451 4749504861787625098874177)
            ·
              refine ⟨3562128646340718824155633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4749504861787625098874177 3562128646340718824155633)
              ·
                refine ⟨2671596484755539118116725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562128646340718824155633 2671596484755539118116725)
                ·
                  refine ⟨250462170445831792323443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671596484755539118116725 250462170445831792323443)
                  ·
                    rfl

theorem cell20_548745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_548745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548745 prefixEnd_548745 := by exact prefixLift 548745
  have htrace : WordTrace (prefixWord ++ tailWord_548745) baseStart_548745 baseEnd_548745 := by
    simpa [prefixWord, tailWord_548745, baseEnd_548745] using wordTrace_append hprefix tailTrace_548745
  have hstable : (prefixWord ++ tailWord_548745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548745).length < 2 ^ (prefixWord ++ tailWord_548745).sum := by decide
  have hdescent : baseEnd_548745 < baseStart_548745 := by decide
  rcases family_descends (prefixWord ++ tailWord_548745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548762 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_548762 : Nat := 118140960795 + 548762 * 2 ^ 59
def prefixEnd_548762 : Nat := 4983230072969 + 3 ^ 40 * 548762 * 2
def baseEnd_548762 : Nat := 250469929709055288756707

theorem tailTrace_548762 : CollatzResearch.WordTrace tailWord_548762 prefixEnd_548762 250469929709055288756707 := by
  unfold tailWord_548762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003748609484117483298135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13343329625290979955461693 5003748609484117483298135)
  ·
    refine ⟨7505622914226176224947203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003748609484117483298135 7505622914226176224947203)
    ·
      refine ⟨11258434371339264337420805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7505622914226176224947203 11258434371339264337420805)
      ·
        refine ⟨2110956444626112063266401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11258434371339264337420805 2110956444626112063266401)
        ·
          refine ⟨1583217333469584047449801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110956444626112063266401 1583217333469584047449801)
          ·
            refine ⟨1187413000102188035587351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1583217333469584047449801 1187413000102188035587351)
            ·
              refine ⟨1781119500153282053381027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187413000102188035587351 1781119500153282053381027)
              ·
                refine ⟨2671679250229923080071541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781119500153282053381027 2671679250229923080071541)
                ·
                  refine ⟨250469929709055288756707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671679250229923080071541 250469929709055288756707)
                  ·
                    rfl

theorem cell20_548762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_548762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548762 prefixEnd_548762 := by exact prefixLift 548762
  have htrace : WordTrace (prefixWord ++ tailWord_548762) baseStart_548762 baseEnd_548762 := by
    simpa [prefixWord, tailWord_548762, baseEnd_548762] using wordTrace_append hprefix tailTrace_548762
  have hstable : (prefixWord ++ tailWord_548762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548762).length < 2 ^ (prefixWord ++ tailWord_548762).sum := by decide
  have hdescent : baseEnd_548762 < baseStart_548762 := by decide
  rcases family_descends (prefixWord ++ tailWord_548762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548834 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_548834 : Nat := 118140960795 + 548834 * 2 ^ 59
def prefixEnd_548834 : Nat := 4983230072969 + 3 ^ 40 * 548834 * 2
def baseEnd_548834 : Nat := 250502792470943038356413

theorem tailTrace_548834 : CollatzResearch.WordTrace tailWord_548834 prefixEnd_548834 250502792470943038356413 := by
  unfold tailWord_548834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004405123418906557453389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13345080329117084153209037 5004405123418906557453389)
  ·
    refine ⟨1876651921282089959045021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5004405123418906557453389 1876651921282089959045021)
    ·
      refine ⟨703744470480783734641883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1876651921282089959045021 703744470480783734641883)
      ·
        refine ⟨1055616705721175601962825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703744470480783734641883 1055616705721175601962825)
        ·
          refine ⟨791712529290881701472119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055616705721175601962825 791712529290881701472119)
          ·
            refine ⟨1187568793936322552208179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791712529290881701472119 1187568793936322552208179)
            ·
              refine ⟨1781353190904483828312269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187568793936322552208179 1781353190904483828312269)
              ·
                refine ⟨668007446589181435617101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1781353190904483828312269 668007446589181435617101)
                ·
                  refine ⟨250502792470943038356413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668007446589181435617101 250502792470943038356413)
                  ·
                    rfl

theorem cell20_548834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_548834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548834 prefixEnd_548834 := by exact prefixLift 548834
  have htrace : WordTrace (prefixWord ++ tailWord_548834) baseStart_548834 baseEnd_548834 := by
    simpa [prefixWord, tailWord_548834, baseEnd_548834] using wordTrace_append hprefix tailTrace_548834
  have hstable : (prefixWord ++ tailWord_548834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548834).length < 2 ^ (prefixWord ++ tailWord_548834).sum := by decide
  have hdescent : baseEnd_548834 < baseStart_548834 := by decide
  rcases family_descends (prefixWord ++ tailWord_548834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548876 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_548876 : Nat := 118140960795 + 548876 * 2 ^ 59
def prefixEnd_548876 : Nat := 4983230072969 + 3 ^ 40 * 548876 * 2
def baseEnd_548876 : Nat := 250521962415377558956241

theorem tailTrace_548876 : CollatzResearch.WordTrace tailWord_548876 prefixEnd_548876 250521962415377558956241 := by
  unfold tailWord_548876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009576179761733701421241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13346101573015644935228321 10009576179761733701421241)
  ·
    refine ⟨7507182134821300276065931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10009576179761733701421241 7507182134821300276065931)
    ·
      refine ⟨11260773202231950414098897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507182134821300276065931 11260773202231950414098897)
      ·
        refine ⟨8445579901673962810574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11260773202231950414098897 8445579901673962810574173)
        ·
          refine ⟨3167092463127736053965315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8445579901673962810574173 3167092463127736053965315)
          ·
            refine ⟨4750638694691604080947973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167092463127736053965315 4750638694691604080947973)
            ·
              refine ⟨890744755254675765177745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4750638694691604080947973 890744755254675765177745)
              ·
                refine ⟨668058566441006823883309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890744755254675765177745 668058566441006823883309)
                ·
                  refine ⟨250521962415377558956241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668058566441006823883309 250521962415377558956241)
                  ·
                    rfl

theorem cell20_548876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_548876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548876 prefixEnd_548876 := by exact prefixLift 548876
  have htrace : WordTrace (prefixWord ++ tailWord_548876) baseStart_548876 baseEnd_548876 := by
    simpa [prefixWord, tailWord_548876, baseEnd_548876] using wordTrace_append hprefix tailTrace_548876
  have hstable : (prefixWord ++ tailWord_548876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548876).length < 2 ^ (prefixWord ++ tailWord_548876).sum := by decide
  have hdescent : baseEnd_548876 < baseStart_548876 := by decide
  rcases family_descends (prefixWord ++ tailWord_548876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548890 : List Nat := [3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_548890 : Nat := 118140960795 + 548890 * 2 ^ 59
def prefixEnd_548890 : Nat := 4983230072969 + 3 ^ 40 * 548890 * 2
def baseEnd_548890 : Nat := 83509450798951910829839

theorem tailTrace_548890 : CollatzResearch.WordTrace tailWord_548890 prefixEnd_548890 83509450798951910829839 := by
  unfold tailWord_548890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004915745368186948463031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13346441987648498529234749 5004915745368186948463031)
  ·
    refine ⟨7507373618052280422694547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004915745368186948463031 7507373618052280422694547)
    ·
      refine ⟨11261060427078420634041821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507373618052280422694547 11261060427078420634041821)
      ·
        refine ⟨4222897660154407737765683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11261060427078420634041821 4222897660154407737765683)
        ·
          refine ⟨6334346490231611606648525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222897660154407737765683 6334346490231611606648525)
          ·
            refine ⟨2375379933836854352493197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6334346490231611606648525 2375379933836854352493197)
            ·
              refine ⟨890767475188820382184949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375379933836854352493197 890767475188820382184949)
              ·
                refine ⟨83509450798951910829839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 890767475188820382184949 83509450798951910829839)
                ·
                  rfl

theorem cell20_548890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_548890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548890 prefixEnd_548890 := by exact prefixLift 548890
  have htrace : WordTrace (prefixWord ++ tailWord_548890) baseStart_548890 baseEnd_548890 := by
    simpa [prefixWord, tailWord_548890, baseEnd_548890] using wordTrace_append hprefix tailTrace_548890
  have hstable : (prefixWord ++ tailWord_548890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548890).length < 2 ^ (prefixWord ++ tailWord_548890).sum := by decide
  have hdescent : baseEnd_548890 < baseStart_548890 := by decide
  rcases family_descends (prefixWord ++ tailWord_548890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548900 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_548900 : Nat := 118140960795 + 548900 * 2 ^ 59
def prefixEnd_548900 : Nat := 4983230072969 + 3 ^ 40 * 548900 * 2
def baseEnd_548900 : Nat := 250532916669340142156143

theorem tailTrace_548900 : CollatzResearch.WordTrace tailWord_548900 prefixEnd_548900 250532916669340142156143 := by
  unfold tailWord_548900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10010013855718259750858077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13346685140957679667810769 10010013855718259750858077)
  ·
    refine ⟨3753755195894347406571779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10010013855718259750858077 3753755195894347406571779)
    ·
      refine ⟨5630632793841521109857669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3753755195894347406571779 5630632793841521109857669)
      ·
        refine ⟨1055743648845285208098313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5630632793841521109857669 1055743648845285208098313)
        ·
          refine ⟨791807736633963906073735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055743648845285208098313 791807736633963906073735)
          ·
            refine ⟨1187711604950945859110603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791807736633963906073735 1187711604950945859110603)
            ·
              refine ⟨1781567407426418788665905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187711604950945859110603 1781567407426418788665905)
              ·
                refine ⟨1336175555569814091499429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781567407426418788665905 1336175555569814091499429)
                ·
                  refine ⟨250532916669340142156143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336175555569814091499429 250532916669340142156143)
                  ·
                    rfl

theorem cell20_548900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_548900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548900 prefixEnd_548900 := by exact prefixLift 548900
  have htrace : WordTrace (prefixWord ++ tailWord_548900) baseStart_548900 baseEnd_548900 := by
    simpa [prefixWord, tailWord_548900, baseEnd_548900] using wordTrace_append hprefix tailTrace_548900
  have hstable : (prefixWord ++ tailWord_548900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548900).length < 2 ^ (prefixWord ++ tailWord_548900).sum := by decide
  have hdescent : baseEnd_548900 < baseStart_548900 := by decide
  rcases family_descends (prefixWord ++ tailWord_548900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548935 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_548935 : Nat := 118140960795 + 548935 * 2 ^ 59
def prefixEnd_548935 : Nat := 4983230072969 + 3 ^ 40 * 548935 * 2
def baseEnd_548935 : Nat := 250548891623035575989333

theorem tailTrace_548935 : CollatzResearch.WordTrace tailWord_548935 prefixEnd_548935 250548891623035575989333 := by
  unfold tailWord_548935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20021304266309720479240259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13347536177539813652826839 20021304266309720479240259)
  ·
    refine ⟨30031956399464580718860389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20021304266309720479240259 30031956399464580718860389)
    ·
      refine ⟨5630991824899608884786323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30031956399464580718860389 5630991824899608884786323)
      ·
        refine ⟨8446487737349413327179485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5630991824899608884786323 8446487737349413327179485)
        ·
          refine ⟨3167432901506029997692307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8446487737349413327179485 3167432901506029997692307)
          ·
            refine ⟨4751149352259044996538461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167432901506029997692307 4751149352259044996538461)
            ·
              refine ⟨1781681007097141873701923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4751149352259044996538461 1781681007097141873701923)
              ·
                refine ⟨2672521510645712810552885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781681007097141873701923 2672521510645712810552885)
                ·
                  refine ⟨250548891623035575989333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672521510645712810552885 250548891623035575989333)
                  ·
                    rfl

theorem cell20_548935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_548935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548935 prefixEnd_548935 := by exact prefixLift 548935
  have htrace : WordTrace (prefixWord ++ tailWord_548935) baseStart_548935 baseEnd_548935 := by
    simpa [prefixWord, tailWord_548935, baseEnd_548935] using wordTrace_append hprefix tailTrace_548935
  have hstable : (prefixWord ++ tailWord_548935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548935).length < 2 ^ (prefixWord ++ tailWord_548935).sum := by decide
  have hdescent : baseEnd_548935 < baseStart_548935 := by decide
  rcases family_descends (prefixWord ++ tailWord_548935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548958 : List Nat := [4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_548958 : Nat := 118140960795 + 548958 * 2 ^ 59
def prefixEnd_548958 : Nat := 4983230072969 + 3 ^ 40 * 548958 * 2
def baseEnd_548958 : Nat := 83519796483249906074191

theorem tailTrace_548958 : CollatzResearch.WordTrace tailWord_548958 prefixEnd_548958 83519796483249906074191 := by
  unfold tailWord_548958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502767893153299425915941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13348095430150930271551685 2502767893153299425915941)
  ·
    refine ⟨469268979966243642359239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2502767893153299425915941 469268979966243642359239)
    ·
      refine ⟨703903469949365463538859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469268979966243642359239 703903469949365463538859)
      ·
        refine ⟨1055855204924048195308289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703903469949365463538859 1055855204924048195308289)
        ·
          refine ⟨791891403693036146481217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055855204924048195308289 791891403693036146481217)
          ·
            refine ⟨593918552769777109860913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791891403693036146481217 593918552769777109860913)
            ·
              refine ⟨445438914577332832395685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593918552769777109860913 445438914577332832395685)
              ·
                refine ⟨83519796483249906074191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445438914577332832395685 83519796483249906074191)
                ·
                  rfl

theorem cell20_548958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_548958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548958 prefixEnd_548958 := by exact prefixLift 548958
  have htrace : WordTrace (prefixWord ++ tailWord_548958) baseStart_548958 baseEnd_548958 := by
    simpa [prefixWord, tailWord_548958, baseEnd_548958] using wordTrace_append hprefix tailTrace_548958
  have hstable : (prefixWord ++ tailWord_548958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548958).length < 2 ^ (prefixWord ++ tailWord_548958).sum := by decide
  have hdescent : baseEnd_548958 < baseStart_548958 := by decide
  rcases family_descends (prefixWord ++ tailWord_548958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548973 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_548973 : Nat := 118140960795 + 548973 * 2 ^ 59
def prefixEnd_548973 : Nat := 4983230072969 + 3 ^ 40 * 548973 * 2
def baseEnd_548973 : Nat := 250566235858476332722511

theorem tailTrace_548973 : CollatzResearch.WordTrace tailWord_548973 prefixEnd_548973 250566235858476332722511 := by
  unfold tailWord_548973
  simp only [CollatzResearch.WordTrace]
  refine ⟨20022690240172052969123573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13348460160114701979415715 20022690240172052969123573)
  ·
    refine ⟨1877127210016129965855335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20022690240172052969123573 1877127210016129965855335)
    ·
      refine ⟨2815690815024194948783003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877127210016129965855335 2815690815024194948783003)
      ·
        refine ⟨4223536222536292423174505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815690815024194948783003 4223536222536292423174505)
        ·
          refine ⟨3167652166902219317380879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4223536222536292423174505 3167652166902219317380879)
          ·
            refine ⟨4751478250353328976071319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167652166902219317380879 4751478250353328976071319)
            ·
              refine ⟨7127217375529993464106979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751478250353328976071319 7127217375529993464106979)
              ·
                refine ⟨10690826063294990196160469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127217375529993464106979 10690826063294990196160469)
                ·
                  refine ⟨250566235858476332722511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10690826063294990196160469 250566235858476332722511)
                  ·
                    rfl

theorem cell20_548973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_548973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548973 prefixEnd_548973 := by exact prefixLift 548973
  have htrace : WordTrace (prefixWord ++ tailWord_548973) baseStart_548973 baseEnd_548973 := by
    simpa [prefixWord, tailWord_548973, baseEnd_548973] using wordTrace_append hprefix tailTrace_548973
  have hstable : (prefixWord ++ tailWord_548973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548973).length < 2 ^ (prefixWord ++ tailWord_548973).sum := by decide
  have hdescent : baseEnd_548973 < baseStart_548973 := by decide
  rcases family_descends (prefixWord ++ tailWord_548973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548976 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_548976 : Nat := 118140960795 + 548976 * 2 ^ 59
def prefixEnd_548976 : Nat := 4983230072969 + 3 ^ 40 * 548976 * 2
def baseEnd_548976 : Nat := 250567605140221655622499

theorem tailTrace_548976 : CollatzResearch.WordTrace tailWord_548976 prefixEnd_548976 250567605140221655622499 := by
  unfold tailWord_548976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011399829580592240741391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13348533106107456320988521 10011399829580592240741391)
  ·
    refine ⟨15017099744370888361112087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011399829580592240741391 15017099744370888361112087)
    ·
      refine ⟨22525649616556332541668131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15017099744370888361112087 22525649616556332541668131)
      ·
        refine ⟨33788474424834498812502197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22525649616556332541668131 33788474424834498812502197)
        ·
          refine ⟨3167669477328234263672081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33788474424834498812502197 3167669477328234263672081)
          ·
            refine ⟨2375752107996175697754061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167669477328234263672081 2375752107996175697754061)
            ·
              refine ⟨890907040498565886657773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375752107996175697754061 890907040498565886657773)
              ·
                refine ⟨334090140186962207496665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 890907040498565886657773 334090140186962207496665)
                ·
                  refine ⟨250567605140221655622499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334090140186962207496665 250567605140221655622499)
                  ·
                    rfl

theorem cell20_548976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_548976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548976 prefixEnd_548976 := by exact prefixLift 548976
  have htrace : WordTrace (prefixWord ++ tailWord_548976) baseStart_548976 baseEnd_548976 := by
    simpa [prefixWord, tailWord_548976, baseEnd_548976] using wordTrace_append hprefix tailTrace_548976
  have hstable : (prefixWord ++ tailWord_548976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548976).length < 2 ^ (prefixWord ++ tailWord_548976).sum := by decide
  have hdescent : baseEnd_548976 < baseStart_548976 := by decide
  rcases family_descends (prefixWord ++ tailWord_548976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548993 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 4]
def baseStart_548993 : Nat := 118140960795 + 548993 * 2 ^ 59
def prefixEnd_548993 : Nat := 4983230072969 + 3 ^ 40 * 548993 * 2
def baseEnd_548993 : Nat := 250575364403445152055763

theorem tailTrace_548993 : CollatzResearch.WordTrace tailWord_548993 prefixEnd_548993 250575364403445152055763 := by
  unfold tailWord_548993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023419700099596384851633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13348946466733064256567755 20023419700099596384851633)
  ·
    refine ⟨15017564775074697288638725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20023419700099596384851633 15017564775074697288638725)
    ·
      refine ⟨2815793395326505741619761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15017564775074697288638725 2815793395326505741619761)
      ·
        refine ⟨2111845046494879306214821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815793395326505741619761 2111845046494879306214821)
        ·
          refine ⟨395970946217789869915279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2111845046494879306214821 395970946217789869915279)
          ·
            refine ⟨593956419326684804872919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395970946217789869915279 593956419326684804872919)
            ·
              refine ⟨890934628990027207309379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593956419326684804872919 890934628990027207309379)
              ·
                refine ⟨1336401943485040810964069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890934628990027207309379 1336401943485040810964069)
                ·
                  refine ⟨250575364403445152055763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336401943485040810964069 250575364403445152055763)
                  ·
                    rfl

theorem cell20_548993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_548993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548993 prefixEnd_548993 := by exact prefixLift 548993
  have htrace : WordTrace (prefixWord ++ tailWord_548993) baseStart_548993 baseEnd_548993 := by
    simpa [prefixWord, tailWord_548993, baseEnd_548993] using wordTrace_append hprefix tailTrace_548993
  have hstable : (prefixWord ++ tailWord_548993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548993).length < 2 ^ (prefixWord ++ tailWord_548993).sum := by decide
  have hdescent : baseEnd_548993 < baseStart_548993 := by decide
  rcases family_descends (prefixWord ++ tailWord_548993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548997 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_548997 : Nat := 118140960795 + 548997 * 2 ^ 59
def prefixEnd_548997 : Nat := 4983230072969 + 3 ^ 40 * 548997 * 2
def baseEnd_548997 : Nat := 250577190112438915922413

theorem tailTrace_548997 : CollatzResearch.WordTrace tailWord_548997 prefixEnd_548997 250577190112438915922413 := by
  unfold tailWord_548997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023565592085105067997245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13349043728056736711998163 20023565592085105067997245)
  ·
    refine ⟨7508837097031914400498967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20023565592085105067997245 7508837097031914400498967)
    ·
      refine ⟨11263255645547871600748451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7508837097031914400498967 11263255645547871600748451)
      ·
        refine ⟨16894883468321807401122677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11263255645547871600748451 16894883468321807401122677)
        ·
          refine ⟨1583895325155169443855251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16894883468321807401122677 1583895325155169443855251)
          ·
            refine ⟨2375842987732754165782877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583895325155169443855251 2375842987732754165782877)
            ·
              refine ⟨890941120399782812168579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375842987732754165782877 890941120399782812168579)
              ·
                refine ⟨1336411680599674218252869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890941120399782812168579 1336411680599674218252869)
                ·
                  refine ⟨250577190112438915922413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336411680599674218252869 250577190112438915922413)
                  ·
                    rfl

theorem cell20_548997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_548997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_548997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_548997 prefixEnd_548997 := by exact prefixLift 548997
  have htrace : WordTrace (prefixWord ++ tailWord_548997) baseStart_548997 baseEnd_548997 := by
    simpa [prefixWord, tailWord_548997, baseEnd_548997] using wordTrace_append hprefix tailTrace_548997
  have hstable : (prefixWord ++ tailWord_548997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548997).length < 2 ^ (prefixWord ++ tailWord_548997).sum := by decide
  have hdescent : baseEnd_548997 < baseStart_548997 := by decide
  rcases family_descends (prefixWord ++ tailWord_548997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549038 : List Nat := [4, 1, 4, 2, 2, 7]
def baseStart_549038 : Nat := 118140960795 + 549038 * 2 ^ 59
def prefixEnd_549038 : Nat := 4983230072969 + 3 ^ 40 * 549038 * 2
def baseEnd_549038 : Nat := 9281329764060185020577

theorem tailTrace_549038 : CollatzResearch.WordTrace tailWord_549038 prefixEnd_549038 9281329764060185020577 := by
  unfold tailWord_549038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503132623117071133779971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13350040656624379380159845 2503132623117071133779971)
  ·
    refine ⟨3754698934675606700669957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2503132623117071133779971 3754698934675606700669957)
    ·
      refine ⟨704006050251676256375617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3754698934675606700669957 704006050251676256375617)
      ·
        refine ⟨528004537688757192281713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704006050251676256375617 528004537688757192281713)
        ·
          refine ⟨396003403266567894211285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528004537688757192281713 396003403266567894211285)
          ·
            refine ⟨9281329764060185020577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 396003403266567894211285 9281329764060185020577)
            ·
              rfl

theorem cell20_549038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 7].length) (baseStart_549038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549038 prefixEnd_549038 := by exact prefixLift 549038
  have htrace : WordTrace (prefixWord ++ tailWord_549038) baseStart_549038 baseEnd_549038 := by
    simpa [prefixWord, tailWord_549038, baseEnd_549038] using wordTrace_append hprefix tailTrace_549038
  have hstable : (prefixWord ++ tailWord_549038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549038).length < 2 ^ (prefixWord ++ tailWord_549038).sum := by decide
  have hdescent : baseEnd_549038 < baseStart_549038 := by decide
  rcases family_descends (prefixWord ++ tailWord_549038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549118 : List Nat := [4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_549118 : Nat := 118140960795 + 549118 * 2 ^ 59
def prefixEnd_549118 : Nat := 4983230072969 + 3 ^ 40 * 549118 * 2
def baseEnd_549118 : Nat := 83544139269833424296195

theorem tailTrace_549118 : CollatzResearch.WordTrace tailWord_549118 prefixEnd_549118 83544139269833424296195 := by
  unfold tailWord_549118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503497353080842841644001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13351985883097828488768005 2503497353080842841644001)
  ·
    refine ⟨1877623014810632131233001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2503497353080842841644001 1877623014810632131233001)
    ·
      refine ⟨1408217261107974098424751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1877623014810632131233001 1408217261107974098424751)
      ·
        refine ⟨2112325891661961147637127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408217261107974098424751 2112325891661961147637127)
        ·
          refine ⟨3168488837492941721455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112325891661961147637127 3168488837492941721455691)
          ·
            refine ⟨4752733256239412582183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168488837492941721455691 4752733256239412582183537)
            ·
              refine ⟨3564549942179559436637653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752733256239412582183537 3564549942179559436637653)
              ·
                refine ⟨83544139269833424296195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3564549942179559436637653 83544139269833424296195)
                ·
                  rfl

theorem cell20_549118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_549118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549118 prefixEnd_549118 := by exact prefixLift 549118
  have htrace : WordTrace (prefixWord ++ tailWord_549118) baseStart_549118 baseEnd_549118 := by
    simpa [prefixWord, tailWord_549118, baseEnd_549118] using wordTrace_append hprefix tailTrace_549118
  have hstable : (prefixWord ++ tailWord_549118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549118).length < 2 ^ (prefixWord ++ tailWord_549118).sum := by decide
  have hdescent : baseEnd_549118 < baseStart_549118 := by decide
  rcases family_descends (prefixWord ++ tailWord_549118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549132 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_549132 : Nat := 118140960795 + 549132 * 2 ^ 59
def prefixEnd_549132 : Nat := 4983230072969 + 3 ^ 40 * 549132 * 2
def baseEnd_549132 : Nat := 250638807790978446421861

theorem tailTrace_549132 : CollatzResearch.WordTrace tailWord_549132 prefixEnd_549132 250638807790978446421861 := by
  unfold tailWord_549132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10014244723298011562080825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13352326297730682082774433 10014244723298011562080825)
  ·
    refine ⟨7510683542473508671560619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10014244723298011562080825 7510683542473508671560619)
    ·
      refine ⟨11266025313710263007340929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7510683542473508671560619 11266025313710263007340929)
      ·
        refine ⟨8449518985282697255505697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11266025313710263007340929 8449518985282697255505697)
        ·
          refine ⟨6337139238962022941629273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8449518985282697255505697 6337139238962022941629273)
          ·
            refine ⟨4752854429221517206221955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6337139238962022941629273 4752854429221517206221955)
            ·
              refine ⟨7129281643832275809332933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752854429221517206221955 7129281643832275809332933)
              ·
                refine ⟨1336740308218551714249925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7129281643832275809332933 1336740308218551714249925)
                ·
                  refine ⟨250638807790978446421861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336740308218551714249925 250638807790978446421861)
                  ·
                    rfl

theorem cell20_549132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_549132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549132 prefixEnd_549132 := by exact prefixLift 549132
  have htrace : WordTrace (prefixWord ++ tailWord_549132) baseStart_549132 baseEnd_549132 := by
    simpa [prefixWord, tailWord_549132, baseEnd_549132] using wordTrace_append hprefix tailTrace_549132
  have hstable : (prefixWord ++ tailWord_549132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549132).length < 2 ^ (prefixWord ++ tailWord_549132).sum := by decide
  have hdescent : baseEnd_549132 < baseStart_549132 := by decide
  rcases family_descends (prefixWord ++ tailWord_549132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549156 : List Nat := [2, 3, 1, 3, 1, 4, 6]
def baseStart_549156 : Nat := 118140960795 + 549156 * 2 ^ 59
def prefixEnd_549156 : Nat := 4983230072969 + 3 ^ 40 * 549156 * 2
def baseEnd_549156 : Nat := 27849973560549003291307

theorem tailTrace_549156 : CollatzResearch.WordTrace tailWord_549156 prefixEnd_549156 27849973560549003291307 := by
  unfold tailWord_549156
  simp only [CollatzResearch.WordTrace]
  refine ⟨10014682399254537611517661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13352909865672716815356881 10014682399254537611517661)
  ·
    refine ⟨3755505899720451604319123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10014682399254537611517661 3755505899720451604319123)
    ·
      refine ⟨5633258849580677406478685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755505899720451604319123 5633258849580677406478685)
      ·
        refine ⟨2112472068592754027429507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5633258849580677406478685 2112472068592754027429507)
        ·
          refine ⟨3168708102889131041144261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112472068592754027429507 3168708102889131041144261)
          ·
            refine ⟨594132769291712070214549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3168708102889131041144261 594132769291712070214549)
            ·
              refine ⟨27849973560549003291307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 594132769291712070214549 27849973560549003291307)
              ·
                rfl

theorem cell20_549156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_549156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549156 prefixEnd_549156 := by exact prefixLift 549156
  have htrace : WordTrace (prefixWord ++ tailWord_549156) baseStart_549156 baseEnd_549156 := by
    simpa [prefixWord, tailWord_549156, baseEnd_549156] using wordTrace_append hprefix tailTrace_549156
  have hstable : (prefixWord ++ tailWord_549156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549156).length < 2 ^ (prefixWord ++ tailWord_549156).sum := by decide
  have hdescent : baseEnd_549156 < baseStart_549156 := by decide
  rcases family_descends (prefixWord ++ tailWord_549156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549162 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_549162 : Nat := 118140960795 + 549162 * 2 ^ 59
def prefixEnd_549162 : Nat := 4983230072969 + 3 ^ 40 * 549162 * 2
def baseEnd_549162 : Nat := 250652500608431675421739

theorem tailTrace_549162 : CollatzResearch.WordTrace tailWord_549162 prefixEnd_549162 250652500608431675421739 := by
  unfold tailWord_549162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007395909121834561938435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13353055757658225498502493 5007395909121834561938435)
  ·
    refine ⟨7511093863682751842907653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007395909121834561938435 7511093863682751842907653)
    ·
      refine ⟨1408330099440515970545185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7511093863682751842907653 1408330099440515970545185)
      ·
        refine ⟨1056247574580386977908889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408330099440515970545185 1056247574580386977908889)
        ·
          refine ⟨792185680935290233431667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056247574580386977908889 792185680935290233431667)
          ·
            refine ⟨1188278521402935350147501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792185680935290233431667 1188278521402935350147501)
            ·
              refine ⟨445604445526100756305313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1188278521402935350147501 445604445526100756305313)
              ·
                refine ⟨334203334144575567228985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445604445526100756305313 334203334144575567228985)
                ·
                  refine ⟨250652500608431675421739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334203334144575567228985 250652500608431675421739)
                  ·
                    rfl

theorem cell20_549162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_549162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549162 prefixEnd_549162 := by exact prefixLift 549162
  have htrace : WordTrace (prefixWord ++ tailWord_549162) baseStart_549162 baseEnd_549162 := by
    simpa [prefixWord, tailWord_549162, baseEnd_549162] using wordTrace_append hprefix tailTrace_549162
  have hstable : (prefixWord ++ tailWord_549162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549162).length < 2 ^ (prefixWord ++ tailWord_549162).sum := by decide
  have hdescent : baseEnd_549162 < baseStart_549162 := by decide
  rcases family_descends (prefixWord ++ tailWord_549162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549184 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_549184 : Nat := 118140960795 + 549184 * 2 ^ 59
def prefixEnd_549184 : Nat := 4983230072969 + 3 ^ 40 * 549184 * 2
def baseEnd_549184 : Nat := 250662542007897376688315

theorem tailTrace_549184 : CollatzResearch.WordTrace tailWord_549184 prefixEnd_549184 250662542007897376688315 := by
  unfold tailWord_549184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015193021203818002527303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13353590694938424003369737 10015193021203818002527303)
  ·
    refine ⟨15022789531805727003790955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015193021203818002527303 15022789531805727003790955)
    ·
      refine ⟨22534184297708590505686433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15022789531805727003790955 22534184297708590505686433)
      ·
        refine ⟨16900638223281442879264825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22534184297708590505686433 16900638223281442879264825)
        ·
          refine ⟨12675478667461082159448619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16900638223281442879264825 12675478667461082159448619)
          ·
            refine ⟨19013218001191623239172929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12675478667461082159448619 19013218001191623239172929)
            ·
              refine ⟨14259913500893717429379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19013218001191623239172929 14259913500893717429379697)
              ·
                refine ⟨10694935125670288072034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14259913500893717429379697 10694935125670288072034773)
                ·
                  refine ⟨250662542007897376688315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10694935125670288072034773 250662542007897376688315)
                  ·
                    rfl

theorem cell20_549184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_549184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549184 prefixEnd_549184 := by exact prefixLift 549184
  have htrace : WordTrace (prefixWord ++ tailWord_549184) baseStart_549184 baseEnd_549184 := by
    simpa [prefixWord, tailWord_549184, baseEnd_549184] using wordTrace_append hprefix tailTrace_549184
  have hstable : (prefixWord ++ tailWord_549184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549184).length < 2 ^ (prefixWord ++ tailWord_549184).sum := by decide
  have hdescent : baseEnd_549184 < baseStart_549184 := by decide
  rcases family_descends (prefixWord ++ tailWord_549184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549218 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_549218 : Nat := 118140960795 + 549218 * 2 ^ 59
def prefixEnd_549218 : Nat := 4983230072969 + 3 ^ 40 * 549218 * 2
def baseEnd_549218 : Nat := 250678060534344369554843

theorem tailTrace_549218 : CollatzResearch.WordTrace tailWord_549218 prefixEnd_549218 250678060534344369554843 := by
  unfold tailWord_549218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007906531071114952948077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13354417416189639874528205 5007906531071114952948077)
  ·
    refine ⟨1877964949151668107355529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5007906531071114952948077 1877964949151668107355529)
    ·
      refine ⟨1408473711863751080516647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1877964949151668107355529 1408473711863751080516647)
      ·
        refine ⟨2112710567795626620774971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408473711863751080516647 2112710567795626620774971)
        ·
          refine ⟨3169065851693439931162457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112710567795626620774971 3169065851693439931162457)
          ·
            refine ⟨2376799388770079948371843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3169065851693439931162457 2376799388770079948371843)
            ·
              refine ⟨3565199083155119922557765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376799388770079948371843 3565199083155119922557765)
              ·
                refine ⟨668474828091584985479581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3565199083155119922557765 668474828091584985479581)
                ·
                  refine ⟨250678060534344369554843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668474828091584985479581 250678060534344369554843)
                  ·
                    rfl

theorem cell20_549218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_549218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549218 prefixEnd_549218 := by exact prefixLift 549218
  have htrace : WordTrace (prefixWord ++ tailWord_549218) baseStart_549218 baseEnd_549218 := by
    simpa [prefixWord, tailWord_549218, baseEnd_549218] using wordTrace_append hprefix tailTrace_549218
  have hstable : (prefixWord ++ tailWord_549218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549218).length < 2 ^ (prefixWord ++ tailWord_549218).sum := by decide
  have hdescent : baseEnd_549218 < baseStart_549218 := by decide
  rcases family_descends (prefixWord ++ tailWord_549218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549221 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 2]
def baseStart_549221 : Nat := 118140960795 + 549221 * 2 ^ 59
def prefixEnd_549221 : Nat := 4983230072969 + 3 ^ 40 * 549221 * 2
def baseEnd_549221 : Nat := 250679429816089692454831

theorem tailTrace_549221 : CollatzResearch.WordTrace tailWord_549221 prefixEnd_549221 250679429816089692454831 := by
  unfold tailWord_549221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031735543273591324151517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354490362182394216101011 20031735543273591324151517)
  ·
    refine ⟨7511900828727596746556819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20031735543273591324151517 7511900828727596746556819)
    ·
      refine ⟨11267851243091395119835229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511900828727596746556819 11267851243091395119835229)
      ·
        refine ⟨4225444216159273169938211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11267851243091395119835229 4225444216159273169938211)
        ·
          refine ⟨6338166324238909754907317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225444216159273169938211 6338166324238909754907317)
          ·
            refine ⟨594203092897397789522561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6338166324238909754907317 594203092897397789522561)
            ·
              refine ⟨445652319673048342141921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594203092897397789522561 445652319673048342141921)
              ·
                refine ⟨334239239754786256606441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445652319673048342141921 334239239754786256606441)
                ·
                  refine ⟨250679429816089692454831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334239239754786256606441 250679429816089692454831)
                  ·
                    rfl

theorem cell20_549221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_549221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549221 prefixEnd_549221 := by exact prefixLift 549221
  have htrace : WordTrace (prefixWord ++ tailWord_549221) baseStart_549221 baseEnd_549221 := by
    simpa [prefixWord, tailWord_549221, baseEnd_549221] using wordTrace_append hprefix tailTrace_549221
  have hstable : (prefixWord ++ tailWord_549221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549221).length < 2 ^ (prefixWord ++ tailWord_549221).sum := by decide
  have hdescent : baseEnd_549221 < baseStart_549221 := by decide
  rcases family_descends (prefixWord ++ tailWord_549221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549225 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 2]
def baseStart_549225 : Nat := 118140960795 + 549225 * 2 ^ 59
def prefixEnd_549225 : Nat := 4983230072969 + 3 ^ 40 * 549225 * 2
def baseEnd_549225 : Nat := 250681255525083456321481

theorem tailTrace_549225 : CollatzResearch.WordTrace tailWord_549225 prefixEnd_549225 250681255525083456321481 := by
  unfold tailWord_549225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031881435259100007297129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354587623506066671531419 20031881435259100007297129)
  ·
    refine ⟨15023911076444325005472847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20031881435259100007297129 15023911076444325005472847)
    ·
      refine ⟨22535866614666487508209271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15023911076444325005472847 22535866614666487508209271)
      ·
        refine ⟨33803799921999731262313907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22535866614666487508209271 33803799921999731262313907)
        ·
          refine ⟨50705699882999596893470861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33803799921999731262313907 50705699882999596893470861)
          ·
            refine ⟨19014637456124848835051573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50705699882999596893470861 19014637456124848835051573)
            ·
              refine ⟨1782622261511704578286085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19014637456124848835051573 1782622261511704578286085)
              ·
                refine ⟨334241674033444608428641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1782622261511704578286085 334241674033444608428641)
                ·
                  refine ⟨250681255525083456321481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334241674033444608428641 250681255525083456321481)
                  ·
                    rfl

theorem cell20_549225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_549225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549225 prefixEnd_549225 := by exact prefixLift 549225
  have htrace : WordTrace (prefixWord ++ tailWord_549225) baseStart_549225 baseEnd_549225 := by
    simpa [prefixWord, tailWord_549225, baseEnd_549225] using wordTrace_append hprefix tailTrace_549225
  have hstable : (prefixWord ++ tailWord_549225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549225).length < 2 ^ (prefixWord ++ tailWord_549225).sum := by decide
  have hdescent : baseEnd_549225 < baseStart_549225 := by decide
  rcases family_descends (prefixWord ++ tailWord_549225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549232 : List Nat := [2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_549232 : Nat := 118140960795 + 549232 * 2 ^ 59
def prefixEnd_549232 : Nat := 4983230072969 + 3 ^ 40 * 549232 * 2
def baseEnd_549232 : Nat := 83561483505274181029373

theorem tailTrace_549232 : CollatzResearch.WordTrace tailWord_549232 prefixEnd_549232 83561483505274181029373 := by
  unfold tailWord_549232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016068373116870101400975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13354757830822493468534633 10016068373116870101400975)
  ·
    refine ⟨15024102559675305152101463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10016068373116870101400975 15024102559675305152101463)
    ·
      refine ⟨22536153839512957728152195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024102559675305152101463 22536153839512957728152195)
      ·
        refine ⟨33804230759269436592228293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22536153839512957728152195 33804230759269436592228293)
        ·
          refine ⟨6338293267363019361042805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33804230759269436592228293 6338293267363019361042805)
          ·
            refine ⟨594214993815283065097763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6338293267363019361042805 594214993815283065097763)
            ·
              refine ⟨891322490722924597646645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594214993815283065097763 891322490722924597646645)
              ·
                refine ⟨83561483505274181029373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 891322490722924597646645 83561483505274181029373)
                ·
                  rfl

theorem cell20_549232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_549232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549232 prefixEnd_549232 := by exact prefixLift 549232
  have htrace : WordTrace (prefixWord ++ tailWord_549232) baseStart_549232 baseEnd_549232 := by
    simpa [prefixWord, tailWord_549232, baseEnd_549232] using wordTrace_append hprefix tailTrace_549232
  have hstable : (prefixWord ++ tailWord_549232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549232).length < 2 ^ (prefixWord ++ tailWord_549232).sum := by decide
  have hdescent : baseEnd_549232 < baseStart_549232 := by decide
  rcases family_descends (prefixWord ++ tailWord_549232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549249 : List Nat := [1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_549249 : Nat := 118140960795 + 549249 * 2 ^ 59
def prefixEnd_549249 : Nat := 4983230072969 + 3 ^ 40 * 549249 * 2
def baseEnd_549249 : Nat := 83564069926348679840461

theorem tailTrace_549249 : CollatzResearch.WordTrace tailWord_549249 prefixEnd_549249 83564069926348679840461 := by
  unfold tailWord_549249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032756787172152106170801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13355171191448101404113867 20032756787172152106170801)
  ·
    refine ⟨15024567590379114079628101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20032756787172152106170801 15024567590379114079628101)
    ·
      refine ⟨2817106423196083889930269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15024567590379114079628101 2817106423196083889930269)
      ·
        refine ⟨1056414908698531458723851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2817106423196083889930269 1056414908698531458723851)
        ·
          refine ⟨1584622363047797188085777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056414908698531458723851 1584622363047797188085777)
          ·
            refine ⟨1188466772285847891064333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584622363047797188085777 1188466772285847891064333)
            ·
              refine ⟨445675039607192959149125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1188466772285847891064333 445675039607192959149125)
              ·
                refine ⟨83564069926348679840461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445675039607192959149125 83564069926348679840461)
                ·
                  rfl

theorem cell20_549249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_549249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549249 prefixEnd_549249 := by exact prefixLift 549249
  have htrace : WordTrace (prefixWord ++ tailWord_549249) baseStart_549249 baseEnd_549249 := by
    simpa [prefixWord, tailWord_549249, baseEnd_549249] using wordTrace_append hprefix tailTrace_549249
  have hstable : (prefixWord ++ tailWord_549249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549249).length < 2 ^ (prefixWord ++ tailWord_549249).sum := by decide
  have hdescent : baseEnd_549249 < baseStart_549249 := by decide
  rcases family_descends (prefixWord ++ tailWord_549249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549284 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_549284 : Nat := 118140960795 + 549284 * 2 ^ 59
def prefixEnd_549284 : Nat := 4983230072969 + 3 ^ 40 * 549284 * 2
def baseEnd_549284 : Nat := 250708184732741473354573

theorem tailTrace_549284 : CollatzResearch.WordTrace tailWord_549284 prefixEnd_549284 250708184732741473354573 := by
  unfold tailWord_549284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017016671022676541847453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13356022228030235389129937 10017016671022676541847453)
  ·
    refine ⟨3756381251633503703192795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10017016671022676541847453 3756381251633503703192795)
    ·
      refine ⟨5634571877450255554789193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3756381251633503703192795 5634571877450255554789193)
      ·
        refine ⟨4225928908087691666091895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5634571877450255554789193 4225928908087691666091895)
        ·
          refine ⟨6338893362131537499137843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225928908087691666091895 6338893362131537499137843)
          ·
            refine ⟨9508340043197306248706765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338893362131537499137843 9508340043197306248706765)
            ·
              refine ⟨3565627516198989843265037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9508340043197306248706765 3565627516198989843265037)
              ·
                refine ⟨1337110318574621191224389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565627516198989843265037 1337110318574621191224389)
                ·
                  refine ⟨250708184732741473354573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337110318574621191224389 250708184732741473354573)
                  ·
                    rfl

theorem cell20_549284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_549284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549284 prefixEnd_549284 := by exact prefixLift 549284
  have htrace : WordTrace (prefixWord ++ tailWord_549284) baseStart_549284 baseEnd_549284 := by
    simpa [prefixWord, tailWord_549284, baseEnd_549284] using wordTrace_append hprefix tailTrace_549284
  have hstable : (prefixWord ++ tailWord_549284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549284).length < 2 ^ (prefixWord ++ tailWord_549284).sum := by decide
  have hdescent : baseEnd_549284 < baseStart_549284 := by decide
  rcases family_descends (prefixWord ++ tailWord_549284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549300 : List Nat := [2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_549300 : Nat := 118140960795 + 549300 * 2 ^ 59
def prefixEnd_549300 : Nat := 4983230072969 + 3 ^ 40 * 549300 * 2
def baseEnd_549300 : Nat := 83571829189572176273725

theorem tailTrace_549300 : CollatzResearch.WordTrace tailWord_549300 prefixEnd_549300 83571829189572176273725 := by
  unfold tailWord_549300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017308454993693908138677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13356411273324925210851569 10017308454993693908138677)
  ·
    refine ⟨939122667655658803888001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10017308454993693908138677 939122667655658803888001)
    ·
      refine ⟨704342000741744102916001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939122667655658803888001 704342000741744102916001)
      ·
        refine ⟨528256500556308077187001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704342000741744102916001 528256500556308077187001)
        ·
          refine ⟨396192375417231057890251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528256500556308077187001 396192375417231057890251)
          ·
            refine ⟨594288563125846586835377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396192375417231057890251 594288563125846586835377)
            ·
              refine ⟨445716422344384940126533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594288563125846586835377 445716422344384940126533)
              ·
                refine ⟨83571829189572176273725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445716422344384940126533 83571829189572176273725)
                ·
                  rfl

theorem cell20_549300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_549300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549300 prefixEnd_549300 := by exact prefixLift 549300
  have htrace : WordTrace (prefixWord ++ tailWord_549300) baseStart_549300 baseEnd_549300 := by
    simpa [prefixWord, tailWord_549300, baseEnd_549300] using wordTrace_append hprefix tailTrace_549300
  have hstable : (prefixWord ++ tailWord_549300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549300).length < 2 ^ (prefixWord ++ tailWord_549300).sum := by decide
  have hdescent : baseEnd_549300 < baseStart_549300 := by decide
  rcases family_descends (prefixWord ++ tailWord_549300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549308 : List Nat := [2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_549308 : Nat := 118140960795 + 549308 * 2 ^ 59
def prefixEnd_549308 : Nat := 4983230072969 + 3 ^ 40 * 549308 * 2
def baseEnd_549308 : Nat := 83573046328901352184825

theorem tailTrace_549308 : CollatzResearch.WordTrace tailWord_549308 prefixEnd_549308 83573046328901352184825 := by
  unfold tailWord_549308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017454346979202591284289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13356605795972270121712385 10017454346979202591284289)
  ·
    refine ⟨7513090760234401943463217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10017454346979202591284289 7513090760234401943463217)
    ·
      refine ⟨5634818070175801457597413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7513090760234401943463217 5634818070175801457597413)
      ·
        refine ⟨1056528388157962773299515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5634818070175801457597413 1056528388157962773299515)
        ·
          refine ⟨1584792582236944159949273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056528388157962773299515 1584792582236944159949273)
          ·
            refine ⟨1188594436677708119961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584792582236944159949273 1188594436677708119961955)
            ·
              refine ⟨1782891655016562179942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188594436677708119961955 1782891655016562179942933)
              ·
                refine ⟨83573046328901352184825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1782891655016562179942933 83573046328901352184825)
                ·
                  rfl

theorem cell20_549308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_549308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549308 prefixEnd_549308 := by exact prefixLift 549308
  have htrace : WordTrace (prefixWord ++ tailWord_549308) baseStart_549308 baseEnd_549308 := by
    simpa [prefixWord, tailWord_549308, baseEnd_549308] using wordTrace_append hprefix tailTrace_549308
  have hstable : (prefixWord ++ tailWord_549308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549308).length < 2 ^ (prefixWord ++ tailWord_549308).sum := by decide
  have hdescent : baseEnd_549308 < baseStart_549308 := by decide
  rcases family_descends (prefixWord ++ tailWord_549308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549428 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_549428 : Nat := 118140960795 + 549428 * 2 ^ 59
def prefixEnd_549428 : Nat := 4983230072969 + 3 ^ 40 * 549428 * 2
def baseEnd_549428 : Nat := 250773910256516972553985

theorem tailTrace_549428 : CollatzResearch.WordTrace tailWord_549428 prefixEnd_549428 250773910256516972553985 := by
  unfold tailWord_549428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019642726761832838468469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13359523635682443784624625 10019642726761832838468469)
  ·
    refine ⟨939341505633921828606419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10019642726761832838468469 939341505633921828606419)
    ·
      refine ⟨1409012258450882742909629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939341505633921828606419 1409012258450882742909629)
      ·
        refine ⟨528379596919081028591111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409012258450882742909629 528379596919081028591111)
        ·
          refine ⟨792569395378621542886667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528379596919081028591111 792569395378621542886667)
          ·
            refine ⟨1188854093067932314330001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792569395378621542886667 1188854093067932314330001)
            ·
              refine ⟨891640569800949235747501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188854093067932314330001 891640569800949235747501)
              ·
                refine ⟨334365213675355963405313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891640569800949235747501 334365213675355963405313)
                ·
                  refine ⟨250773910256516972553985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334365213675355963405313 250773910256516972553985)
                  ·
                    rfl

theorem cell20_549428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_549428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549428 prefixEnd_549428 := by exact prefixLift 549428
  have htrace : WordTrace (prefixWord ++ tailWord_549428) baseStart_549428 baseEnd_549428 := by
    simpa [prefixWord, tailWord_549428, baseEnd_549428] using wordTrace_append hprefix tailTrace_549428
  have hstable : (prefixWord ++ tailWord_549428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549428).length < 2 ^ (prefixWord ++ tailWord_549428).sum := by decide
  have hdescent : baseEnd_549428 < baseStart_549428 := by decide
  rcases family_descends (prefixWord ++ tailWord_549428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549453 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_549453 : Nat := 118140960795 + 549453 * 2 ^ 59
def prefixEnd_549453 : Nat := 4983230072969 + 3 ^ 40 * 549453 * 2
def baseEnd_549453 : Nat := 250785320937727996720549

theorem tailTrace_549453 : CollatzResearch.WordTrace tailWord_549453 prefixEnd_549453 250785320937727996720549 := by
  unfold tailWord_549453
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040197278433094946597013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13360131518955396631064675 20040197278433094946597013)
  ·
    refine ⟨939384247426551325621735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20040197278433094946597013 939384247426551325621735)
    ·
      refine ⟨1409076371139826988432603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939384247426551325621735 1409076371139826988432603)
      ·
        refine ⟨2113614556709740482648905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409076371139826988432603 2113614556709740482648905)
        ·
          refine ⟨1585210917532305361986679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113614556709740482648905 1585210917532305361986679)
          ·
            refine ⟨2377816376298458042980019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585210917532305361986679 2377816376298458042980019)
            ·
              refine ⟨3566724564447687064470029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377816376298458042980019 3566724564447687064470029)
              ·
                refine ⟨1337521711667882649176261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3566724564447687064470029 1337521711667882649176261)
                ·
                  refine ⟨250785320937727996720549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337521711667882649176261 250785320937727996720549)
                  ·
                    rfl

theorem cell20_549453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_549453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549453 prefixEnd_549453 := by exact prefixLift 549453
  have htrace : WordTrace (prefixWord ++ tailWord_549453) baseStart_549453 baseEnd_549453 := by
    simpa [prefixWord, tailWord_549453, baseEnd_549453] using wordTrace_append hprefix tailTrace_549453
  have hstable : (prefixWord ++ tailWord_549453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549453).length < 2 ^ (prefixWord ++ tailWord_549453).sum := by decide
  have hdescent : baseEnd_549453 < baseStart_549453 := by decide
  rcases family_descends (prefixWord ++ tailWord_549453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549477 : List Nat := [1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_549477 : Nat := 118140960795 + 549477 * 2 ^ 59
def prefixEnd_549477 : Nat := 4983230072969 + 3 ^ 40 * 549477 * 2
def baseEnd_549477 : Nat := 83598758397230193306817

theorem tailTrace_549477 : CollatzResearch.WordTrace tailWord_549477 prefixEnd_549477 83598758397230193306817 := by
  unfold tailWord_549477
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041072630346147045470685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13360715086897431363647123 20041072630346147045470685)
  ·
    refine ⟨7515402236379805142051507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20041072630346147045470685 7515402236379805142051507)
    ·
      refine ⟨11273103354569707713077261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7515402236379805142051507 11273103354569707713077261)
      ·
        refine ⟨4227413757963640392403973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11273103354569707713077261 4227413757963640392403973)
        ·
          refine ⟨792640079618182573575745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4227413757963640392403973 792640079618182573575745)
          ·
            refine ⟨594480059713636930181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792640079618182573575745 594480059713636930181809)
            ·
              refine ⟨445860044785227697636357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594480059713636930181809 445860044785227697636357)
              ·
                refine ⟨83598758397230193306817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445860044785227697636357 83598758397230193306817)
                ·
                  rfl

theorem cell20_549477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_549477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549477 prefixEnd_549477 := by exact prefixLift 549477
  have htrace : WordTrace (prefixWord ++ tailWord_549477) baseStart_549477 baseEnd_549477 := by
    simpa [prefixWord, tailWord_549477, baseEnd_549477] using wordTrace_append hprefix tailTrace_549477
  have hstable : (prefixWord ++ tailWord_549477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549477).length < 2 ^ (prefixWord ++ tailWord_549477).sum := by decide
  have hdescent : baseEnd_549477 < baseStart_549477 := by decide
  rcases family_descends (prefixWord ++ tailWord_549477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549495 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_549495 : Nat := 118140960795 + 549495 * 2 ^ 59
def prefixEnd_549495 : Nat := 4983230072969 + 3 ^ 40 * 549495 * 2
def baseEnd_549495 : Nat := 250804490882162517320377

theorem tailTrace_549495 : CollatzResearch.WordTrace tailWord_549495 prefixEnd_549495 250804490882162517320377 := by
  unfold tailWord_549495
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041729144280936119625939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13361152762853957413083959 20041729144280936119625939)
  ·
    refine ⟨30062593716421404179438909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20041729144280936119625939 30062593716421404179438909)
    ·
      refine ⟨11273472643658026567289591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30062593716421404179438909 11273472643658026567289591)
      ·
        refine ⟨16910208965487039850934387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11273472643658026567289591 16910208965487039850934387)
        ·
          refine ⟨25365313448230559776401581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16910208965487039850934387 25365313448230559776401581)
          ·
            refine ⟨9511992543086459916150593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25365313448230559776401581 9511992543086459916150593)
            ·
              refine ⟨7133994407314844937112945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511992543086459916150593 7133994407314844937112945)
              ·
                refine ⟨5350495805486133702834709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7133994407314844937112945 5350495805486133702834709)
                ·
                  refine ⟨250804490882162517320377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5350495805486133702834709 250804490882162517320377)
                  ·
                    rfl

theorem cell20_549495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_549495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549495 prefixEnd_549495 := by exact prefixLift 549495
  have htrace : WordTrace (prefixWord ++ tailWord_549495) baseStart_549495 baseEnd_549495 := by
    simpa [prefixWord, tailWord_549495, baseEnd_549495] using wordTrace_append hprefix tailTrace_549495
  have hstable : (prefixWord ++ tailWord_549495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549495).length < 2 ^ (prefixWord ++ tailWord_549495).sum := by decide
  have hdescent : baseEnd_549495 < baseStart_549495 := by decide
  rcases family_descends (prefixWord ++ tailWord_549495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549505 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_549505 : Nat := 118140960795 + 549505 * 2 ^ 59
def prefixEnd_549505 : Nat := 4983230072969 + 3 ^ 40 * 549505 * 2
def baseEnd_549505 : Nat := 250809055154646926987003

theorem tailTrace_549505 : CollatzResearch.WordTrace tailWord_549505 prefixEnd_549505 250809055154646926987003 := by
  unfold tailWord_549505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20042093874244707827489969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13361395916163138551659979 20042093874244707827489969)
  ·
    refine ⟨15031570405683530870617477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20042093874244707827489969 15031570405683530870617477)
    ·
      refine ⟨2818419451065662038240777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15031570405683530870617477 2818419451065662038240777)
      ·
        refine ⟨2113814588299246528680583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2818419451065662038240777 2113814588299246528680583)
        ·
          refine ⟨3170721882448869793020875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113814588299246528680583 3170721882448869793020875)
          ·
            refine ⟨4756082823673304689531313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170721882448869793020875 4756082823673304689531313)
            ·
              refine ⟨3567062117754978517148485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4756082823673304689531313 3567062117754978517148485)
              ·
                refine ⟨668824147079058471965341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3567062117754978517148485 668824147079058471965341)
                ·
                  refine ⟨250809055154646926987003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668824147079058471965341 250809055154646926987003)
                  ·
                    rfl

theorem cell20_549505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_549505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549505 prefixEnd_549505 := by exact prefixLift 549505
  have htrace : WordTrace (prefixWord ++ tailWord_549505) baseStart_549505 baseEnd_549505 := by
    simpa [prefixWord, tailWord_549505, baseEnd_549505] using wordTrace_append hprefix tailTrace_549505
  have hstable : (prefixWord ++ tailWord_549505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549505).length < 2 ^ (prefixWord ++ tailWord_549505).sum := by decide
  have hdescent : baseEnd_549505 < baseStart_549505 := by decide
  rcases family_descends (prefixWord ++ tailWord_549505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549522 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_549522 : Nat := 118140960795 + 549522 * 2 ^ 59
def prefixEnd_549522 : Nat := 4983230072969 + 3 ^ 40 * 549522 * 2
def baseEnd_549522 : Nat := 250816814417870423420267

theorem tailTrace_549522 : CollatzResearch.WordTrace tailWord_549522 prefixEnd_549522 250816814417870423420267 := by
  unfold tailWord_549522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010678478795779932714705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13361809276788746487239213 5010678478795779932714705)
  ·
    refine ⟨3758008859096834949536029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5010678478795779932714705 3758008859096834949536029)
    ·
      refine ⟨1409253322161313106076011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3758008859096834949536029 1409253322161313106076011)
      ·
        refine ⟨2113879983241969659114017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409253322161313106076011 2113879983241969659114017)
        ·
          refine ⟨1585409987431477244335513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113879983241969659114017 1585409987431477244335513)
          ·
            refine ⟨1189057490573607933251635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585409987431477244335513 1189057490573607933251635)
            ·
              refine ⟨1783586235860411899877453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189057490573607933251635 1783586235860411899877453)
              ·
                refine ⟨668844838447654462454045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783586235860411899877453 668844838447654462454045)
                ·
                  refine ⟨250816814417870423420267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668844838447654462454045 250816814417870423420267)
                  ·
                    rfl

theorem cell20_549522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_549522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549522 prefixEnd_549522 := by exact prefixLift 549522
  have htrace : WordTrace (prefixWord ++ tailWord_549522) baseStart_549522 baseEnd_549522 := by
    simpa [prefixWord, tailWord_549522, baseEnd_549522] using wordTrace_append hprefix tailTrace_549522
  have hstable : (prefixWord ++ tailWord_549522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549522).length < 2 ^ (prefixWord ++ tailWord_549522).sum := by decide
  have hdescent : baseEnd_549522 < baseStart_549522 := by decide
  rcases family_descends (prefixWord ++ tailWord_549522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549557 : List Nat := [1, 3, 3, 3, 1, 9]
def baseStart_549557 : Nat := 118140960795 + 549557 * 2 ^ 59
def prefixEnd_549557 : Nat := 4983230072969 + 3 ^ 40 * 549557 * 2
def baseEnd_549557 : Nat := 9290103310057994713091

theorem tailTrace_549557 : CollatzResearch.WordTrace tailWord_549557 prefixEnd_549557 9290103310057994713091 := by
  unfold tailWord_549557
  simp only [CollatzResearch.WordTrace]
  refine ⟨20043990470056320708382925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13362660313370880472255283 20043990470056320708382925)
  ·
    refine ⟨7516496426271120265643597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20043990470056320708382925 7516496426271120265643597)
    ·
      refine ⟨2818686159851670099616349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7516496426271120265643597 2818686159851670099616349)
      ·
        refine ⟨1057007309944376287356131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2818686159851670099616349 1057007309944376287356131)
        ·
          refine ⟨1585510964916564431034197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057007309944376287356131 1585510964916564431034197)
          ·
            refine ⟨9290103310057994713091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1585510964916564431034197 9290103310057994713091)
            ·
              rfl

theorem cell20_549557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_549557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549557 prefixEnd_549557 := by exact prefixLift 549557
  have htrace : WordTrace (prefixWord ++ tailWord_549557) baseStart_549557 baseEnd_549557 := by
    simpa [prefixWord, tailWord_549557, baseEnd_549557] using wordTrace_append hprefix tailTrace_549557
  have hstable : (prefixWord ++ tailWord_549557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549557).length < 2 ^ (prefixWord ++ tailWord_549557).sum := by decide
  have hdescent : baseEnd_549557 < baseStart_549557 := by decide
  rcases family_descends (prefixWord ++ tailWord_549557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549567 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 2]
def baseStart_549567 : Nat := 118140960795 + 549567 * 2 ^ 59
def prefixEnd_549567 : Nat := 4983230072969 + 3 ^ 40 * 549567 * 2
def baseEnd_549567 : Nat := 250837353644050266920083

theorem tailTrace_549567 : CollatzResearch.WordTrace tailWord_549567 prefixEnd_549567 250837353644050266920083 := by
  unfold tailWord_549567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20044355200020092416246955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13362903466680061610831303 20044355200020092416246955)
  ·
    refine ⟨30066532800030138624370433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20044355200020092416246955 30066532800030138624370433)
    ·
      refine ⟨22549899600022603968277825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30066532800030138624370433 22549899600022603968277825)
      ·
        refine ⟨16912424700016952976208369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22549899600022603968277825 16912424700016952976208369)
        ·
          refine ⟨12684318525012714732156277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16912424700016952976208369 12684318525012714732156277)
          ·
            refine ⟨1189154861719942006139651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12684318525012714732156277 1189154861719942006139651)
            ·
              refine ⟨1783732292579913009209477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189154861719942006139651 1783732292579913009209477)
              ·
                refine ⟨334449804858733689226777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1783732292579913009209477 334449804858733689226777)
                ·
                  refine ⟨250837353644050266920083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334449804858733689226777 250837353644050266920083)
                  ·
                    rfl

theorem cell20_549567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2].length) (baseStart_549567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549567 prefixEnd_549567 := by exact prefixLift 549567
  have htrace : WordTrace (prefixWord ++ tailWord_549567) baseStart_549567 baseEnd_549567 := by
    simpa [prefixWord, tailWord_549567, baseEnd_549567] using wordTrace_append hprefix tailTrace_549567
  have hstable : (prefixWord ++ tailWord_549567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549567).length < 2 ^ (prefixWord ++ tailWord_549567).sum := by decide
  have hdescent : baseEnd_549567 < baseStart_549567 := by decide
  rcases family_descends (prefixWord ++ tailWord_549567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549605 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 2]
def baseStart_549605 : Nat := 118140960795 + 549605 * 2 ^ 59
def prefixEnd_549605 : Nat := 4983230072969 + 3 ^ 40 * 549605 * 2
def baseEnd_549605 : Nat := 250854697879491023653261

theorem tailTrace_549605 : CollatzResearch.WordTrace tailWord_549605 prefixEnd_549605 250854697879491023653261 := by
  unfold tailWord_549605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20045741173882424906130269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13363827449254949937420179 20045741173882424906130269)
  ·
    refine ⟨7517152940205909339798851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20045741173882424906130269 7517152940205909339798851)
    ·
      refine ⟨11275729410308864009698277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517152940205909339798851 11275729410308864009698277)
      ·
        refine ⟨2114199264432912001818427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11275729410308864009698277 2114199264432912001818427)
        ·
          refine ⟨3171298896649368002727641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114199264432912001818427 3171298896649368002727641)
          ·
            refine ⟨2378474172487026002045731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171298896649368002727641 2378474172487026002045731)
            ·
              refine ⟨3567711258730539003068597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378474172487026002045731 3567711258730539003068597)
              ·
                refine ⟨334472930505988031537681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3567711258730539003068597 334472930505988031537681)
                ·
                  refine ⟨250854697879491023653261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334472930505988031537681 250854697879491023653261)
                  ·
                    rfl

theorem cell20_549605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_549605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549605 prefixEnd_549605 := by exact prefixLift 549605
  have htrace : WordTrace (prefixWord ++ tailWord_549605) baseStart_549605 baseEnd_549605 := by
    simpa [prefixWord, tailWord_549605, baseEnd_549605] using wordTrace_append hprefix tailTrace_549605
  have hstable : (prefixWord ++ tailWord_549605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549605).length < 2 ^ (prefixWord ++ tailWord_549605).sum := by decide
  have hdescent : baseEnd_549605 < baseStart_549605 := by decide
  rcases family_descends (prefixWord ++ tailWord_549605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549616 : List Nat := [2, 1, 1, 1, 3, 1, 11]
def baseStart_549616 : Nat := 118140960795 + 549616 * 2 ^ 59
def prefixEnd_549616 : Nat := 4983230072969 + 3 ^ 40 * 549616 * 2
def baseEnd_549616 : Nat := 27873302064358208254061

theorem tailTrace_549616 : CollatzResearch.WordTrace tailWord_549616 prefixEnd_549616 27873302064358208254061 := by
  unfold tailWord_549616
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023071188421286892390351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13364094917895049189853801 10023071188421286892390351)
  ·
    refine ⟨15034606782631930338585527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10023071188421286892390351 15034606782631930338585527)
    ·
      refine ⟨22551910173947895507878291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15034606782631930338585527 22551910173947895507878291)
      ·
        refine ⟨33827865260921843261817437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22551910173947895507878291 33827865260921843261817437)
        ·
          refine ⟨12685449472845691223181539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33827865260921843261817437 12685449472845691223181539)
          ·
            refine ⟨19028174209268536834772309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12685449472845691223181539 19028174209268536834772309)
            ·
              refine ⟨27873302064358208254061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19028174209268536834772309 27873302064358208254061)
              ·
                rfl

theorem cell20_549616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_549616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549616 prefixEnd_549616 := by exact prefixLift 549616
  have htrace : WordTrace (prefixWord ++ tailWord_549616) baseStart_549616 baseEnd_549616 := by
    simpa [prefixWord, tailWord_549616, baseEnd_549616] using wordTrace_append hprefix tailTrace_549616
  have hstable : (prefixWord ++ tailWord_549616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549616).length < 2 ^ (prefixWord ++ tailWord_549616).sum := by decide
  have hdescent : baseEnd_549616 < baseStart_549616 := by decide
  rcases family_descends (prefixWord ++ tailWord_549616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549636 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_549636 : Nat := 118140960795 + 549636 * 2 ^ 59
def prefixEnd_549636 : Nat := 4983230072969 + 3 ^ 40 * 549636 * 2
def baseEnd_549636 : Nat := 250868847124192693619801

theorem tailTrace_549636 : CollatzResearch.WordTrace tailWord_549636 prefixEnd_549636 250868847124192693619801 := by
  unfold tailWord_549636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023435918385058600254381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13364581224513411467005841 10023435918385058600254381)
  ·
    refine ⟨3758788469394396975095393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10023435918385058600254381 3758788469394396975095393)
    ·
      refine ⟨2819091352045797731321545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3758788469394396975095393 2819091352045797731321545)
      ·
        refine ⟨2114318514034348298491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819091352045797731321545 2114318514034348298491159)
        ·
          refine ⟨3171477771051522447736739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114318514034348298491159 3171477771051522447736739)
          ·
            refine ⟨4757216656577283671605109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171477771051522447736739 4757216656577283671605109)
            ·
              refine ⟨445989061554120344212979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4757216656577283671605109 445989061554120344212979)
              ·
                refine ⟨668983592331180516319469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445989061554120344212979 668983592331180516319469)
                ·
                  refine ⟨250868847124192693619801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668983592331180516319469 250868847124192693619801)
                  ·
                    rfl

theorem cell20_549636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_549636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549636 prefixEnd_549636 := by exact prefixLift 549636
  have htrace : WordTrace (prefixWord ++ tailWord_549636) baseStart_549636 baseEnd_549636 := by
    simpa [prefixWord, tailWord_549636, baseEnd_549636] using wordTrace_append hprefix tailTrace_549636
  have hstable : (prefixWord ++ tailWord_549636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549636).length < 2 ^ (prefixWord ++ tailWord_549636).sum := by decide
  have hdescent : baseEnd_549636 < baseStart_549636 := by decide
  rcases family_descends (prefixWord ++ tailWord_549636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549647 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_549647 : Nat := 118140960795 + 549647 * 2 ^ 59
def prefixEnd_549647 : Nat := 4983230072969 + 3 ^ 40 * 549647 * 2
def baseEnd_549647 : Nat := 250873867823925544253089

theorem tailTrace_549647 : CollatzResearch.WordTrace tailWord_549647 prefixEnd_549647 250873867823925544253089 := by
  unfold tailWord_549647
  simp only [CollatzResearch.WordTrace]
  refine ⟨20047273039730266079159195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13364848693153510719439463 20047273039730266079159195)
  ·
    refine ⟨30070909559595399118738793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20047273039730266079159195 30070909559595399118738793)
    ·
      refine ⟨22553182169696549339054095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30070909559595399118738793 22553182169696549339054095)
      ·
        refine ⟨33829773254544824008581143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22553182169696549339054095 33829773254544824008581143)
        ·
          refine ⟨50744659881817236012871715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33829773254544824008581143 50744659881817236012871715)
          ·
            refine ⟨76116989822725854019307573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50744659881817236012871715 76116989822725854019307573)
            ·
              refine ⟨7135967795880548814310085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76116989822725854019307573 7135967795880548814310085)
              ·
                refine ⟨1337993961727602902683141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7135967795880548814310085 1337993961727602902683141)
                ·
                  refine ⟨250873867823925544253089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1337993961727602902683141 250873867823925544253089)
                  ·
                    rfl

theorem cell20_549647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_549647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549647 prefixEnd_549647 := by exact prefixLift 549647
  have htrace : WordTrace (prefixWord ++ tailWord_549647) baseStart_549647 baseEnd_549647 := by
    simpa [prefixWord, tailWord_549647, baseEnd_549647] using wordTrace_append hprefix tailTrace_549647
  have hstable : (prefixWord ++ tailWord_549647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549647).length < 2 ^ (prefixWord ++ tailWord_549647).sum := by decide
  have hdescent : baseEnd_549647 < baseStart_549647 := by decide
  rcases family_descends (prefixWord ++ tailWord_549647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549660 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_549660 : Nat := 118140960795 + 549660 * 2 ^ 59
def prefixEnd_549660 : Nat := 4983230072969 + 3 ^ 40 * 549660 * 2
def baseEnd_549660 : Nat := 250879801378155276819703

theorem tailTrace_549660 : CollatzResearch.WordTrace tailWord_549660 prefixEnd_549660 250879801378155276819703 := by
  unfold tailWord_549660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023873594341584649691217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13365164792455446199588289 10023873594341584649691217)
  ·
    refine ⟨7517905195756188487268413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10023873594341584649691217 7517905195756188487268413)
    ·
      refine ⟨2819214448408570682725655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7517905195756188487268413 2819214448408570682725655)
      ·
        refine ⟨4228821672612856024088483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819214448408570682725655 4228821672612856024088483)
        ·
          refine ⟨6343232508919284036132725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228821672612856024088483 6343232508919284036132725)
          ·
            refine ⟨594678047711182878387443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6343232508919284036132725 594678047711182878387443)
            ·
              refine ⟨892017071566774317581165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594678047711182878387443 892017071566774317581165)
              ·
                refine ⟨334506401837540369092937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 892017071566774317581165 334506401837540369092937)
                ·
                  refine ⟨250879801378155276819703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334506401837540369092937 250879801378155276819703)
                  ·
                    rfl

theorem cell20_549660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_549660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549660 prefixEnd_549660 := by exact prefixLift 549660
  have htrace : WordTrace (prefixWord ++ tailWord_549660) baseStart_549660 baseEnd_549660 := by
    simpa [prefixWord, tailWord_549660, baseEnd_549660] using wordTrace_append hprefix tailTrace_549660
  have hstable : (prefixWord ++ tailWord_549660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549660).length < 2 ^ (prefixWord ++ tailWord_549660).sum := by decide
  have hdescent : baseEnd_549660 < baseStart_549660 := by decide
  rcases family_descends (prefixWord ++ tailWord_549660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549677 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_549677 : Nat := 118140960795 + 549677 * 2 ^ 59
def prefixEnd_549677 : Nat := 4983230072969 + 3 ^ 40 * 549677 * 2
def baseEnd_549677 : Nat := 250887560641378773252967

theorem tailTrace_549677 : CollatzResearch.WordTrace tailWord_549677 prefixEnd_549677 250887560641378773252967 := by
  unfold tailWord_549677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048367229621581202751285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13365578153081054135167523 20048367229621581202751285)
  ·
    refine ⟨1879534427777023237757933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20048367229621581202751285 1879534427777023237757933)
    ·
      refine ⟨704825410416383714159225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1879534427777023237757933 704825410416383714159225)
      ·
        refine ⟨528619057812287785619419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704825410416383714159225 528619057812287785619419)
        ·
          refine ⟨792928586718431678429129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528619057812287785619419 792928586718431678429129)
          ·
            refine ⟨594696440038823758821847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792928586718431678429129 594696440038823758821847)
            ·
              refine ⟨892044660058235638232771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594696440038823758821847 892044660058235638232771)
              ·
                refine ⟨1338066990087353457349157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892044660058235638232771 1338066990087353457349157)
                ·
                  refine ⟨250887560641378773252967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338066990087353457349157 250887560641378773252967)
                  ·
                    rfl

theorem cell20_549677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_549677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549677 prefixEnd_549677 := by exact prefixLift 549677
  have htrace : WordTrace (prefixWord ++ tailWord_549677) baseStart_549677 baseEnd_549677 := by
    simpa [prefixWord, tailWord_549677, baseEnd_549677] using wordTrace_append hprefix tailTrace_549677
  have hstable : (prefixWord ++ tailWord_549677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549677).length < 2 ^ (prefixWord ++ tailWord_549677).sum := by decide
  have hdescent : baseEnd_549677 < baseStart_549677 := by decide
  rcases family_descends (prefixWord ++ tailWord_549677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549695 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_549695 : Nat := 118140960795 + 549695 * 2 ^ 59
def prefixEnd_549695 : Nat := 4983230072969 + 3 ^ 40 * 549695 * 2
def baseEnd_549695 : Nat := 250895776331850710652893

theorem tailTrace_549695 : CollatzResearch.WordTrace tailWord_549695 prefixEnd_549695 250895776331850710652893 := by
  unfold tailWord_549695
  simp only [CollatzResearch.WordTrace]
  refine ⟨20049023743556370276906539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13366015829037580184604359 20049023743556370276906539)
  ·
    refine ⟨30073535615334555415359809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20049023743556370276906539 30073535615334555415359809)
    ·
      refine ⟨22555151711500916561519857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30073535615334555415359809 22555151711500916561519857)
      ·
        refine ⟨16916363783625687421139893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22555151711500916561519857 16916363783625687421139893)
        ·
          refine ⟨1585909104714908195731865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16916363783625687421139893 1585909104714908195731865)
          ·
            refine ⟨1189431828536181146798899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585909104714908195731865 1189431828536181146798899)
            ·
              refine ⟨1784147742804271720198349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189431828536181146798899 1784147742804271720198349)
              ·
                refine ⟨669055403551601895074381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784147742804271720198349 669055403551601895074381)
                ·
                  refine ⟨250895776331850710652893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669055403551601895074381 250895776331850710652893)
                  ·
                    rfl

theorem cell20_549695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_549695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549695 prefixEnd_549695 := by exact prefixLift 549695
  have htrace : WordTrace (prefixWord ++ tailWord_549695) baseStart_549695 baseEnd_549695 := by
    simpa [prefixWord, tailWord_549695, baseEnd_549695] using wordTrace_append hprefix tailTrace_549695
  have hstable : (prefixWord ++ tailWord_549695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549695).length < 2 ^ (prefixWord ++ tailWord_549695).sum := by decide
  have hdescent : baseEnd_549695 < baseStart_549695 := by decide
  rcases family_descends (prefixWord ++ tailWord_549695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549736 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_549736 : Nat := 118140960795 + 549736 * 2 ^ 59
def prefixEnd_549736 : Nat := 4983230072969 + 3 ^ 40 * 549736 * 2
def baseEnd_549736 : Nat := 250914489849036790286059

theorem tailTrace_549736 : CollatzResearch.WordTrace tailWord_549736 prefixEnd_549736 250914489849036790286059 := by
  unfold tailWord_549736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025259568203917139574531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13367012757605222852766041 10025259568203917139574531)
  ·
    refine ⟨15037889352305875709361797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10025259568203917139574531 15037889352305875709361797)
    ·
      refine ⟨2819604253557351695505337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15037889352305875709361797 2819604253557351695505337)
      ·
        refine ⟨2114703190168013771629003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819604253557351695505337 2114703190168013771629003)
        ·
          refine ⟨3172054785252020657443505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114703190168013771629003 3172054785252020657443505)
          ·
            refine ⟨2379041088939015493082629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3172054785252020657443505 2379041088939015493082629)
            ·
              refine ⟨446070204176065404952993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2379041088939015493082629 446070204176065404952993)
              ·
                refine ⟨334552653132049053714745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446070204176065404952993 334552653132049053714745)
                ·
                  refine ⟨250914489849036790286059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334552653132049053714745 250914489849036790286059)
                  ·
                    rfl

theorem cell20_549736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_549736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549736 prefixEnd_549736 := by exact prefixLift 549736
  have htrace : WordTrace (prefixWord ++ tailWord_549736) baseStart_549736 baseEnd_549736 := by
    simpa [prefixWord, tailWord_549736, baseEnd_549736] using wordTrace_append hprefix tailTrace_549736
  have hstable : (prefixWord ++ tailWord_549736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549736).length < 2 ^ (prefixWord ++ tailWord_549736).sum := by decide
  have hdescent : baseEnd_549736 < baseStart_549736 := by decide
  rcases family_descends (prefixWord ++ tailWord_549736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549750 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_549750 : Nat := 118140960795 + 549750 * 2 ^ 59
def prefixEnd_549750 : Nat := 4983230072969 + 3 ^ 40 * 549750 * 2
def baseEnd_549750 : Nat := 250920879830514963819335

theorem tailTrace_549750 : CollatzResearch.WordTrace tailWord_549750 prefixEnd_549750 250920879830514963819335 := by
  unfold tailWord_549750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253189359897319666884919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13367353172238076446772469 1253189359897319666884919)
  ·
    refine ⟨1879784039845979500327379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253189359897319666884919 1879784039845979500327379)
    ·
      refine ⟨2819676059768969250491069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879784039845979500327379 2819676059768969250491069)
      ·
        refine ⟨1057378522413363468934151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2819676059768969250491069 1057378522413363468934151)
        ·
          refine ⟨1586067783620045203401227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057378522413363468934151 1586067783620045203401227)
          ·
            refine ⟨2379101675430067805101841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586067783620045203401227 2379101675430067805101841)
            ·
              refine ⟨1784326256572550853826381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379101675430067805101841 1784326256572550853826381)
              ·
                refine ⟨669122346214706570184893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784326256572550853826381 669122346214706570184893)
                ·
                  refine ⟨250920879830514963819335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669122346214706570184893 250920879830514963819335)
                  ·
                    rfl

theorem cell20_549750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_549750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549750 prefixEnd_549750 := by exact prefixLift 549750
  have htrace : WordTrace (prefixWord ++ tailWord_549750) baseStart_549750 baseEnd_549750 := by
    simpa [prefixWord, tailWord_549750, baseEnd_549750] using wordTrace_append hprefix tailTrace_549750
  have hstable : (prefixWord ++ tailWord_549750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549750).length < 2 ^ (prefixWord ++ tailWord_549750).sum := by decide
  have hdescent : baseEnd_549750 < baseStart_549750 := by decide
  rcases family_descends (prefixWord ++ tailWord_549750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549850 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_549850 : Nat := 118140960795 + 549850 * 2 ^ 59
def prefixEnd_549850 : Nat := 4983230072969 + 3 ^ 40 * 549850 * 2
def baseEnd_549850 : Nat := 250966522555359060485593

theorem tailTrace_549850 : CollatzResearch.WordTrace tailWord_549850 prefixEnd_549850 250966522555359060485593 := by
  unfold tailWord_549850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013669264498707937199751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13369784705329887832532669 5013669264498707937199751)
  ·
    refine ⟨7520503896748061905799627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013669264498707937199751 7520503896748061905799627)
    ·
      refine ⟨11280755845122092858699441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520503896748061905799627 11280755845122092858699441)
      ·
        refine ⟨8460566883841569644024581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11280755845122092858699441 8460566883841569644024581)
        ·
          refine ⟨1586356290720294308254609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8460566883841569644024581 1586356290720294308254609)
          ·
            refine ⟨1189767218040220731190957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586356290720294308254609 1189767218040220731190957)
            ·
              refine ⟨446162706765082774196609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1189767218040220731190957 446162706765082774196609)
              ·
                refine ⟨334622030073812080647457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446162706765082774196609 334622030073812080647457)
                ·
                  refine ⟨250966522555359060485593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334622030073812080647457 250966522555359060485593)
                  ·
                    rfl

theorem cell20_549850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_549850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549850 prefixEnd_549850 := by exact prefixLift 549850
  have htrace : WordTrace (prefixWord ++ tailWord_549850) baseStart_549850 baseEnd_549850 := by
    simpa [prefixWord, tailWord_549850, baseEnd_549850] using wordTrace_append hprefix tailTrace_549850
  have hstable : (prefixWord ++ tailWord_549850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549850).length < 2 ^ (prefixWord ++ tailWord_549850).sum := by decide
  have hdescent : baseEnd_549850 < baseStart_549850 := by decide
  rcases family_descends (prefixWord ++ tailWord_549850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549909 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 2]
def baseStart_549909 : Nat := 118140960795 + 549909 * 2 ^ 59
def prefixEnd_549909 : Nat := 4983230072969 + 3 ^ 40 * 549909 * 2
def baseEnd_549909 : Nat := 250993451763017077518685

theorem tailTrace_549909 : CollatzResearch.WordTrace tailWord_549909 prefixEnd_549909 250993451763017077518685 := by
  unfold tailWord_549909
  simp only [CollatzResearch.WordTrace]
  refine ⟨20056828964781084825196781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13371219309854056550131187 20056828964781084825196781)
  ·
    refine ⟨7521310861792906809448793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20056828964781084825196781 7521310861792906809448793)
    ·
      refine ⟨5640983146344680107086595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7521310861792906809448793 5640983146344680107086595)
      ·
        refine ⟨8461474719517020160629893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640983146344680107086595 8461474719517020160629893)
        ·
          refine ⟨1586526509909441280118105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8461474719517020160629893 1586526509909441280118105)
          ·
            refine ⟨1189894882432080960088579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586526509909441280118105 1189894882432080960088579)
            ·
              refine ⟨1784842323648121440132869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189894882432080960088579 1784842323648121440132869)
              ·
                refine ⟨334657935684022770024913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1784842323648121440132869 334657935684022770024913)
                ·
                  refine ⟨250993451763017077518685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334657935684022770024913 250993451763017077518685)
                  ·
                    rfl

theorem cell20_549909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_549909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549909 prefixEnd_549909 := by exact prefixLift 549909
  have htrace : WordTrace (prefixWord ++ tailWord_549909) baseStart_549909 baseEnd_549909 := by
    simpa [prefixWord, tailWord_549909, baseEnd_549909] using wordTrace_append hprefix tailTrace_549909
  have hstable : (prefixWord ++ tailWord_549909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549909).length < 2 ^ (prefixWord ++ tailWord_549909).sum := by decide
  have hdescent : baseEnd_549909 < baseStart_549909 := by decide
  rcases family_descends (prefixWord ++ tailWord_549909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549916 : List Nat := [2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_549916 : Nat := 118140960795 + 549916 * 2 ^ 59
def prefixEnd_549916 : Nat := 4983230072969 + 3 ^ 40 * 549916 * 2
def baseEnd_549916 : Nat := 83665548917918721428441

theorem tailTrace_549916 : CollatzResearch.WordTrace tailWord_549916 prefixEnd_549916 83665548917918721428441 := by
  unfold tailWord_549916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028542137877862510350801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13371389517170483347134401 10028542137877862510350801)
  ·
    refine ⟨7521406603408396882763101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10028542137877862510350801 7521406603408396882763101)
    ·
      refine ⟨2820527476278148831036163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7521406603408396882763101 2820527476278148831036163)
      ·
        refine ⟨4230791214417223246554245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820527476278148831036163 4230791214417223246554245)
        ·
          refine ⟨793273352703229358728921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4230791214417223246554245 793273352703229358728921)
          ·
            refine ⟨594955014527422019046691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793273352703229358728921 594955014527422019046691)
            ·
              refine ⟨892432521791133028570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594955014527422019046691 892432521791133028570037)
              ·
                refine ⟨83665548917918721428441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 892432521791133028570037 83665548917918721428441)
                ·
                  rfl

theorem cell20_549916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_549916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549916 prefixEnd_549916 := by exact prefixLift 549916
  have htrace : WordTrace (prefixWord ++ tailWord_549916) baseStart_549916 baseEnd_549916 := by
    simpa [prefixWord, tailWord_549916, baseEnd_549916] using wordTrace_append hprefix tailTrace_549916
  have hstable : (prefixWord ++ tailWord_549916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549916).length < 2 ^ (prefixWord ++ tailWord_549916).sum := by decide
  have hdescent : baseEnd_549916 < baseStart_549916 := by decide
  rcases family_descends (prefixWord ++ tailWord_549916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549937 : List Nat := [1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_549937 : Nat := 118140960795 + 549937 * 2 ^ 59
def prefixEnd_549937 : Nat := 4983230072969 + 3 ^ 40 * 549937 * 2
def baseEnd_549937 : Nat := 83668743908657808195079

theorem tailTrace_549937 : CollatzResearch.WordTrace tailWord_549937 prefixEnd_549937 83668743908657808195079 := by
  unfold tailWord_549937
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057850208679645607216065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13371900139119763738144043 20057850208679645607216065)
  ·
    refine ⟨15043387656509734205412049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20057850208679645607216065 15043387656509734205412049)
    ·
      refine ⟨11282540742382300654059037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15043387656509734205412049 11282540742382300654059037)
      ·
        refine ⟨4230952778393362745272139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11282540742382300654059037 4230952778393362745272139)
        ·
          refine ⟨6346429167590044117908209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230952778393362745272139 6346429167590044117908209)
          ·
            refine ⟨4759821875692533088431157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6346429167590044117908209 4759821875692533088431157)
            ·
              refine ⟨446233300846174977040421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4759821875692533088431157 446233300846174977040421)
              ·
                refine ⟨83668743908657808195079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446233300846174977040421 83668743908657808195079)
                ·
                  rfl

theorem cell20_549937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_549937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549937 prefixEnd_549937 := by exact prefixLift 549937
  have htrace : WordTrace (prefixWord ++ tailWord_549937) baseStart_549937 baseEnd_549937 := by
    simpa [prefixWord, tailWord_549937, baseEnd_549937] using wordTrace_append hprefix tailTrace_549937
  have hstable : (prefixWord ++ tailWord_549937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549937).length < 2 ^ (prefixWord ++ tailWord_549937).sum := by decide
  have hdescent : baseEnd_549937 < baseStart_549937 := by decide
  rcases family_descends (prefixWord ++ tailWord_549937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549974 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_549974 : Nat := 118140960795 + 549974 * 2 ^ 59
def prefixEnd_549974 : Nat := 4983230072969 + 3 ^ 40 * 549974 * 2
def baseEnd_549974 : Nat := 251023119534165740351753

theorem tailTrace_549974 : CollatzResearch.WordTrace tailWord_549974 prefixEnd_549974 251023119534165740351753 := by
  unfold tailWord_549974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253699981846600057894561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13372799806363733950875317 1253699981846600057894561)
  ·
    refine ⟨940274986384950043420921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253699981846600057894561 940274986384950043420921)
    ·
      refine ⟨705206239788712532565691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 940274986384950043420921 705206239788712532565691)
      ·
        refine ⟨1057809359683068798848537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705206239788712532565691 1057809359683068798848537)
        ·
          refine ⟨793357019762301599136403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057809359683068798848537 793357019762301599136403)
          ·
            refine ⟨1190035529643452398704605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793357019762301599136403 1190035529643452398704605)
            ·
              refine ⟨446263323616294649514227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190035529643452398704605 446263323616294649514227)
              ·
                refine ⟨669394985424441974271341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446263323616294649514227 669394985424441974271341)
                ·
                  refine ⟨251023119534165740351753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669394985424441974271341 251023119534165740351753)
                  ·
                    rfl

theorem cell20_549974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_549974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549974 prefixEnd_549974 := by exact prefixLift 549974
  have htrace : WordTrace (prefixWord ++ tailWord_549974) baseStart_549974 baseEnd_549974 := by
    simpa [prefixWord, tailWord_549974, baseEnd_549974] using wordTrace_append hprefix tailTrace_549974
  have hstable : (prefixWord ++ tailWord_549974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549974).length < 2 ^ (prefixWord ++ tailWord_549974).sum := by decide
  have hdescent : baseEnd_549974 < baseStart_549974 := by decide
  rcases family_descends (prefixWord ++ tailWord_549974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549989 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_549989 : Nat := 118140960795 + 549989 * 2 ^ 59
def prefixEnd_549989 : Nat := 4983230072969 + 3 ^ 40 * 549989 * 2
def baseEnd_549989 : Nat := 251029965942892354851691

theorem tailTrace_549989 : CollatzResearch.WordTrace tailWord_549989 prefixEnd_549989 251029965942892354851691 := by
  unfold tailWord_549989
  simp only [CollatzResearch.WordTrace]
  refine ⟨20059746804491258488109021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13373164536327505658739347 20059746804491258488109021)
  ·
    refine ⟨7522405051684221933040883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20059746804491258488109021 7522405051684221933040883)
    ·
      refine ⟨11283607577526332899561325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522405051684221933040883 11283607577526332899561325)
      ·
        refine ⟨4231352841572374837335497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11283607577526332899561325 4231352841572374837335497)
        ·
          refine ⟨3173514631179281128001623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231352841572374837335497 3173514631179281128001623)
          ·
            refine ⟨4760271946768921692002435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173514631179281128001623 4760271946768921692002435)
            ·
              refine ⟨7140407920153382538003653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760271946768921692002435 7140407920153382538003653)
              ·
                refine ⟨1338826485028759225875685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7140407920153382538003653 1338826485028759225875685)
                ·
                  refine ⟨251029965942892354851691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338826485028759225875685 251029965942892354851691)
                  ·
                    rfl

theorem cell20_549989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_549989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549989 prefixEnd_549989 := by exact prefixLift 549989
  have htrace : WordTrace (prefixWord ++ tailWord_549989) baseStart_549989 baseEnd_549989 := by
    simpa [prefixWord, tailWord_549989, baseEnd_549989] using wordTrace_append hprefix tailTrace_549989
  have hstable : (prefixWord ++ tailWord_549989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549989).length < 2 ^ (prefixWord ++ tailWord_549989).sum := by decide
  have hdescent : baseEnd_549989 < baseStart_549989 := by decide
  rcases family_descends (prefixWord ++ tailWord_549989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549992 : List Nat := [2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_549992 : Nat := 118140960795 + 549992 * 2 ^ 59
def prefixEnd_549992 : Nat := 4983230072969 + 3 ^ 40 * 549992 * 2
def baseEnd_549992 : Nat := 83677111741545892583893

theorem tailTrace_549992 : CollatzResearch.WordTrace tailWord_549992 prefixEnd_549992 83677111741545892583893 := by
  unfold tailWord_549992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029928111740195000234115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13373237482320260000312153 10029928111740195000234115)
  ·
    refine ⟨15044892167610292500351173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10029928111740195000234115 15044892167610292500351173)
    ·
      refine ⟨2820917281426929843815845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15044892167610292500351173 2820917281426929843815845)
      ·
        refine ⟨528921990267549345715471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2820917281426929843815845 528921990267549345715471)
        ·
          refine ⟨793382985401324018573207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528921990267549345715471 793382985401324018573207)
          ·
            refine ⟨1190074478101986027859811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793382985401324018573207 1190074478101986027859811)
            ·
              refine ⟨1785111717152979041789717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190074478101986027859811 1785111717152979041789717)
              ·
                refine ⟨83677111741545892583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1785111717152979041789717 83677111741545892583893)
                ·
                  rfl

theorem cell20_549992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_549992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549992 prefixEnd_549992 := by exact prefixLift 549992
  have htrace : WordTrace (prefixWord ++ tailWord_549992) baseStart_549992 baseEnd_549992 := by
    simpa [prefixWord, tailWord_549992, baseEnd_549992] using wordTrace_append hprefix tailTrace_549992
  have hstable : (prefixWord ++ tailWord_549992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549992).length < 2 ^ (prefixWord ++ tailWord_549992).sum := by decide
  have hdescent : baseEnd_549992 < baseStart_549992 := by decide
  rcases family_descends (prefixWord ++ tailWord_549992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549996 : List Nat := [2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_549996 : Nat := 118140960795 + 549996 * 2 ^ 59
def prefixEnd_549996 : Nat := 4983230072969 + 3 ^ 40 * 549996 * 2
def baseEnd_549996 : Nat := 83677720311210480539443

theorem tailTrace_549996 : CollatzResearch.WordTrace tailWord_549996 prefixEnd_549996 83677720311210480539443 := by
  unfold tailWord_549996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030001057732949341806921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13373334743643932455742561 10030001057732949341806921)
  ·
    refine ⟨7522500793299712006355191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10030001057732949341806921 7522500793299712006355191)
    ·
      refine ⟨11283751189949568009532787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522500793299712006355191 11283751189949568009532787)
      ·
        refine ⟨16925626784924352014299181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283751189949568009532787 16925626784924352014299181)
        ·
          refine ⟨6347110044346632005362193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16925626784924352014299181 6347110044346632005362193)
          ·
            refine ⟨4760332533259974004021645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347110044346632005362193 4760332533259974004021645)
            ·
              refine ⟨1785124699972490251508117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4760332533259974004021645 1785124699972490251508117)
              ·
                refine ⟨83677720311210480539443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1785124699972490251508117 83677720311210480539443)
                ·
                  rfl

theorem cell20_549996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_549996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_549996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_549996 prefixEnd_549996 := by exact prefixLift 549996
  have htrace : WordTrace (prefixWord ++ tailWord_549996) baseStart_549996 baseEnd_549996 := by
    simpa [prefixWord, tailWord_549996, baseEnd_549996] using wordTrace_append hprefix tailTrace_549996
  have hstable : (prefixWord ++ tailWord_549996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549996).length < 2 ^ (prefixWord ++ tailWord_549996).sum := by decide
  have hdescent : baseEnd_549996 < baseStart_549996 := by decide
  rcases family_descends (prefixWord ++ tailWord_549996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550020 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_550020 : Nat := 118140960795 + 550020 * 2 ^ 59
def prefixEnd_550020 : Nat := 4983230072969 + 3 ^ 40 * 550020 * 2
def baseEnd_550020 : Nat := 251044115187594024818231

theorem tailTrace_550020 : CollatzResearch.WordTrace tailWord_550020 prefixEnd_550020 251044115187594024818231 := by
  unfold tailWord_550020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030438733689475391243757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13373918311585967188325009 10030438733689475391243757)
  ·
    refine ⟨3761414525133553271716409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10030438733689475391243757 3761414525133553271716409)
    ·
      refine ⟨2821060893850164953787307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3761414525133553271716409 2821060893850164953787307)
      ·
        refine ⟨4231591340775247430680961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821060893850164953787307 4231591340775247430680961)
        ·
          refine ⟨3173693505581435573010721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231591340775247430680961 3173693505581435573010721)
          ·
            refine ⟨2380270129186076679758041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3173693505581435573010721 2380270129186076679758041)
            ·
              refine ⟨1785202596889557509818531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380270129186076679758041 1785202596889557509818531)
              ·
                refine ⟨2677803895334336264727797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785202596889557509818531 2677803895334336264727797)
                ·
                  refine ⟨251044115187594024818231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677803895334336264727797 251044115187594024818231)
                  ·
                    rfl

theorem cell20_550020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_550020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550020 prefixEnd_550020 := by exact prefixLift 550020
  have htrace : WordTrace (prefixWord ++ tailWord_550020) baseStart_550020 baseEnd_550020 := by
    simpa [prefixWord, tailWord_550020, baseEnd_550020] using wordTrace_append hprefix tailTrace_550020
  have hstable : (prefixWord ++ tailWord_550020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550020).length < 2 ^ (prefixWord ++ tailWord_550020).sum := by decide
  have hdescent : baseEnd_550020 < baseStart_550020 := by decide
  rcases family_descends (prefixWord ++ tailWord_550020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550078 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_550078 : Nat := 118140960795 + 550078 * 2 ^ 59
def prefixEnd_550078 : Nat := 4983230072969 + 3 ^ 40 * 550078 * 2
def baseEnd_550078 : Nat := 251070587968003600884661

theorem tailTrace_550078 : CollatzResearch.WordTrace tailWord_550078 prefixEnd_550078 251070587968003600884661 := by
  unfold tailWord_550078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507874112646103336012361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13375328600779217792065925 2507874112646103336012361)
  ·
    refine ⟨1880905584484577502009271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2507874112646103336012361 1880905584484577502009271)
    ·
      refine ⟨2821358376726866253013907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880905584484577502009271 2821358376726866253013907)
      ·
        refine ⟨4232037565090299379520861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821358376726866253013907 4232037565090299379520861)
        ·
          refine ⟨1587014086908862267320323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4232037565090299379520861 1587014086908862267320323)
          ·
            refine ⟨2380521130363293400980485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587014086908862267320323 2380521130363293400980485)
            ·
              refine ⟨446347711943117512683841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2380521130363293400980485 446347711943117512683841)
              ·
                refine ⟨334760783957338134512881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446347711943117512683841 334760783957338134512881)
                ·
                  refine ⟨251070587968003600884661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334760783957338134512881 251070587968003600884661)
                  ·
                    rfl

theorem cell20_550078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_550078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550078 prefixEnd_550078 := by exact prefixLift 550078
  have htrace : WordTrace (prefixWord ++ tailWord_550078) baseStart_550078 baseEnd_550078 := by
    simpa [prefixWord, tailWord_550078, baseEnd_550078] using wordTrace_append hprefix tailTrace_550078
  have hstable : (prefixWord ++ tailWord_550078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550078).length < 2 ^ (prefixWord ++ tailWord_550078).sum := by decide
  have hdescent : baseEnd_550078 < baseStart_550078 := by decide
  rcases family_descends (prefixWord ++ tailWord_550078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550079 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_550079 : Nat := 118140960795 + 550079 * 2 ^ 59
def prefixEnd_550079 : Nat := 4983230072969 + 3 ^ 40 * 550079 * 2
def baseEnd_550079 : Nat := 251071044395252041851323

theorem tailTrace_550079 : CollatzResearch.WordTrace tailWord_550079 prefixEnd_550079 251071044395252041851323 := by
  unfold tailWord_550079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20063029374165203858885291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13375352916110135905923527 20063029374165203858885291)
  ·
    refine ⟨30094544061247805788327937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20063029374165203858885291 30094544061247805788327937)
    ·
      refine ⟨22570908045935854341245953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30094544061247805788327937 22570908045935854341245953)
      ·
        refine ⟨16928181034451890755934465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22570908045935854341245953 16928181034451890755934465)
        ·
          refine ⟨12696135775838918066950849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16928181034451890755934465 12696135775838918066950849)
          ·
            refine ⟨9522101831879188550213137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12696135775838918066950849 9522101831879188550213137)
            ·
              refine ⟨7141576373909391412659853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9522101831879188550213137 7141576373909391412659853)
              ·
                refine ⟨2678091140216021779747445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7141576373909391412659853 2678091140216021779747445)
                ·
                  refine ⟨251071044395252041851323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678091140216021779747445 251071044395252041851323)
                  ·
                    rfl

theorem cell20_550079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_550079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550079 prefixEnd_550079 := by exact prefixLift 550079
  have htrace : WordTrace (prefixWord ++ tailWord_550079) baseStart_550079 baseEnd_550079 := by
    simpa [prefixWord, tailWord_550079, baseEnd_550079] using wordTrace_append hprefix tailTrace_550079
  have hstable : (prefixWord ++ tailWord_550079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550079).length < 2 ^ (prefixWord ++ tailWord_550079).sum := by decide
  have hdescent : baseEnd_550079 < baseStart_550079 := by decide
  rcases family_descends (prefixWord ++ tailWord_550079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550130 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_550130 : Nat := 118140960795 + 550130 * 2 ^ 59
def prefixEnd_550130 : Nat := 4983230072969 + 3 ^ 40 * 550130 * 2
def baseEnd_550130 : Nat := 251094322184922531151115

theorem tailTrace_550130 : CollatzResearch.WordTrace tailWord_550130 prefixEnd_550130 251094322184922531151115 := by
  unfold tailWord_550130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016222374245109892247961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13376592997986959712661229 5016222374245109892247961)
  ·
    refine ⟨3762166780683832419185971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5016222374245109892247961 3762166780683832419185971)
    ·
      refine ⟨5643250171025748628778957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3762166780683832419185971 5643250171025748628778957)
      ·
        refine ⟨2116218814134655735792109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5643250171025748628778957 2116218814134655735792109)
        ·
          refine ⟨793582055300495900922041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2116218814134655735792109 793582055300495900922041)
          ·
            refine ⟨595186541475371925691531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793582055300495900922041 595186541475371925691531)
            ·
              refine ⟨892779812213057888537297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595186541475371925691531 892779812213057888537297)
              ·
                refine ⟨669584859159793416402973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892779812213057888537297 669584859159793416402973)
                ·
                  refine ⟨251094322184922531151115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669584859159793416402973 251094322184922531151115)
                  ·
                    rfl

theorem cell20_550130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_550130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550130 prefixEnd_550130 := by exact prefixLift 550130
  have htrace : WordTrace (prefixWord ++ tailWord_550130) baseStart_550130 baseEnd_550130 := by
    simpa [prefixWord, tailWord_550130, baseEnd_550130] using wordTrace_append hprefix tailTrace_550130
  have hstable : (prefixWord ++ tailWord_550130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550130).length < 2 ^ (prefixWord ++ tailWord_550130).sum := by decide
  have hdescent : baseEnd_550130 < baseStart_550130 := by decide
  rcases family_descends (prefixWord ++ tailWord_550130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550189 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_550189 : Nat := 118140960795 + 550189 * 2 ^ 59
def prefixEnd_550189 : Nat := 4983230072969 + 3 ^ 40 * 550189 * 2
def baseEnd_550189 : Nat := 251121251392580548184207

theorem tailTrace_550189 : CollatzResearch.WordTrace tailWord_550189 prefixEnd_550189 251121251392580548184207 := by
  unfold tailWord_550189
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067041403766692645389621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13378027602511128430259747 20067041403766692645389621)
  ·
    refine ⟨1881285131603127435505277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20067041403766692645389621 1881285131603127435505277)
    ·
      refine ⟨705481924351172788314479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1881285131603127435505277 705481924351172788314479)
      ·
        refine ⟨1058222886526759182471719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705481924351172788314479 1058222886526759182471719)
        ·
          refine ⟨1587334329790138773707579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058222886526759182471719 1587334329790138773707579)
          ·
            refine ⟨2381001494685208160561369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587334329790138773707579 2381001494685208160561369)
            ·
              refine ⟨1785751121013906120421027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381001494685208160561369 1785751121013906120421027)
              ·
                refine ⟨2678626681520859180631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785751121013906120421027 2678626681520859180631541)
                ·
                  refine ⟨251121251392580548184207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678626681520859180631541 251121251392580548184207)
                  ·
                    rfl

theorem cell20_550189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_550189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550189 prefixEnd_550189 := by exact prefixLift 550189
  have htrace : WordTrace (prefixWord ++ tailWord_550189) baseStart_550189 baseEnd_550189 := by
    simpa [prefixWord, tailWord_550189, baseEnd_550189] using wordTrace_append hprefix tailTrace_550189
  have hstable : (prefixWord ++ tailWord_550189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550189).length < 2 ^ (prefixWord ++ tailWord_550189).sum := by decide
  have hdescent : baseEnd_550189 < baseStart_550189 := by decide
  rcases family_descends (prefixWord ++ tailWord_550189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550237 : List Nat := [1, 4, 5, 1, 2, 7]
def baseStart_550237 : Nat := 118140960795 + 550237 * 2 ^ 59
def prefixEnd_550237 : Nat := 4983230072969 + 3 ^ 40 * 550237 * 2
def baseEnd_550237 : Nat := 9301598514833544984593

theorem tailTrace_550237 : CollatzResearch.WordTrace tailWord_550237 prefixEnd_550237 9301598514833544984593 := by
  unfold tailWord_550237
  simp only [CollatzResearch.WordTrace]
  refine ⟨20068792107592796843136965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13379194738395197895424643 20068792107592796843136965)
  ·
    refine ⟨3762898520173649408088181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20068792107592796843136965 3762898520173649408088181)
    ·
      refine ⟨352771736266279632008267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3762898520173649408088181 352771736266279632008267)
      ·
        refine ⟨529157604399419448012401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352771736266279632008267 529157604399419448012401)
        ·
          refine ⟨396868203299564586009301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529157604399419448012401 396868203299564586009301)
          ·
            refine ⟨9301598514833544984593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 396868203299564586009301 9301598514833544984593)
            ·
              rfl

theorem cell20_550237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 7].length) (baseStart_550237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550237 prefixEnd_550237 := by exact prefixLift 550237
  have htrace : WordTrace (prefixWord ++ tailWord_550237) baseStart_550237 baseEnd_550237 := by
    simpa [prefixWord, tailWord_550237, baseEnd_550237] using wordTrace_append hprefix tailTrace_550237
  have hstable : (prefixWord ++ tailWord_550237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550237).length < 2 ^ (prefixWord ++ tailWord_550237).sum := by decide
  have hdescent : baseEnd_550237 < baseStart_550237 := by decide
  rcases family_descends (prefixWord ++ tailWord_550237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550247 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 2]
def baseStart_550247 : Nat := 118140960795 + 550247 * 2 ^ 59
def prefixEnd_550247 : Nat := 4983230072969 + 3 ^ 40 * 550247 * 2
def baseEnd_550247 : Nat := 251147724172990124250637

theorem tailTrace_550247 : CollatzResearch.WordTrace tailWord_550247 prefixEnd_550247 251147724172990124250637 := by
  unfold tailWord_550247
  simp only [CollatzResearch.WordTrace]
  refine ⟨20069156837556568551000995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13379437891704379034000663 20069156837556568551000995)
  ·
    refine ⟨30103735256334852826501493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20069156837556568551000995 30103735256334852826501493)
    ·
      refine ⟨2822225180281392452484515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30103735256334852826501493 2822225180281392452484515)
      ·
        refine ⟨4233337770422088678726773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822225180281392452484515 4233337770422088678726773)
        ·
          refine ⟨396875415977070813630635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4233337770422088678726773 396875415977070813630635)
          ·
            refine ⟨595313123965606220445953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396875415977070813630635 595313123965606220445953)
            ·
              refine ⟨446484842974204665334465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595313123965606220445953 446484842974204665334465)
              ·
                refine ⟨334863632230653499000849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446484842974204665334465 334863632230653499000849)
                ·
                  refine ⟨251147724172990124250637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334863632230653499000849 251147724172990124250637)
                  ·
                    rfl

theorem cell20_550247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2].length) (baseStart_550247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550247 prefixEnd_550247 := by exact prefixLift 550247
  have htrace : WordTrace (prefixWord ++ tailWord_550247) baseStart_550247 baseEnd_550247 := by
    simpa [prefixWord, tailWord_550247, baseEnd_550247] using wordTrace_append hprefix tailTrace_550247
  have hstable : (prefixWord ++ tailWord_550247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550247).length < 2 ^ (prefixWord ++ tailWord_550247).sum := by decide
  have hdescent : baseEnd_550247 < baseStart_550247 := by decide
  rcases family_descends (prefixWord ++ tailWord_550247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550279 : List Nat := [1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_550279 : Nat := 118140960795 + 550279 * 2 ^ 59
def prefixEnd_550279 : Nat := 4983230072969 + 3 ^ 40 * 550279 * 2
def baseEnd_550279 : Nat := 83720776614980078394613

theorem tailTrace_550279 : CollatzResearch.WordTrace tailWord_550279 prefixEnd_550279 83720776614980078394613 := by
  unfold tailWord_550279
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070323973440638016165891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13380215982293758677443927 20070323973440638016165891)
  ·
    refine ⟨30105485960160957024248837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20070323973440638016165891 30105485960160957024248837)
    ·
      refine ⟨5644778617530179442046657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30105485960160957024248837 5644778617530179442046657)
      ·
        refine ⟨4233583963147634581534993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5644778617530179442046657 4233583963147634581534993)
        ·
          refine ⟨3175187972360725936151245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4233583963147634581534993 3175187972360725936151245)
          ·
            refine ⟨1190695489635272226056717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3175187972360725936151245 1190695489635272226056717)
            ·
              refine ⟨446510808613227084771269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190695489635272226056717 446510808613227084771269)
              ·
                refine ⟨83720776614980078394613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446510808613227084771269 83720776614980078394613)
                ·
                  rfl

theorem cell20_550279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_550279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550279 prefixEnd_550279 := by exact prefixLift 550279
  have htrace : WordTrace (prefixWord ++ tailWord_550279) baseStart_550279 baseEnd_550279 := by
    simpa [prefixWord, tailWord_550279, baseEnd_550279] using wordTrace_append hprefix tailTrace_550279
  have hstable : (prefixWord ++ tailWord_550279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550279).length < 2 ^ (prefixWord ++ tailWord_550279).sum := by decide
  have hdescent : baseEnd_550279 < baseStart_550279 := by decide
  rcases family_descends (prefixWord ++ tailWord_550279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550303 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_550303 : Nat := 118140960795 + 550303 * 2 ^ 59
def prefixEnd_550303 : Nat := 4983230072969 + 3 ^ 40 * 550303 * 2
def baseEnd_550303 : Nat := 251173284098902818383741

theorem tailTrace_550303 : CollatzResearch.WordTrace tailWord_550303 prefixEnd_550303 251173284098902818383741 := by
  unfold tailWord_550303
  simp only [CollatzResearch.WordTrace]
  refine ⟨20071199325353690115039563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13380799550235793410026375 20071199325353690115039563)
  ·
    refine ⟨30106798988030535172559345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20071199325353690115039563 30106798988030535172559345)
    ·
      refine ⟨22580099241022901379419509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30106798988030535172559345 22580099241022901379419509)
      ·
        refine ⟨2116884303845897004320579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22580099241022901379419509 2116884303845897004320579)
        ·
          refine ⟨3175326455768845506480869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116884303845897004320579 3175326455768845506480869)
          ·
            refine ⟨595373710456658532465163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3175326455768845506480869 595373710456658532465163)
            ·
              refine ⟨893060565684987798697745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595373710456658532465163 893060565684987798697745)
              ·
                refine ⟨669795424263740849023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893060565684987798697745 669795424263740849023309)
                ·
                  refine ⟨251173284098902818383741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669795424263740849023309 251173284098902818383741)
                  ·
                    rfl

theorem cell20_550303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_550303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550303 prefixEnd_550303 := by exact prefixLift 550303
  have htrace : WordTrace (prefixWord ++ tailWord_550303) baseStart_550303 baseEnd_550303 := by
    simpa [prefixWord, tailWord_550303, baseEnd_550303] using wordTrace_append hprefix tailTrace_550303
  have hstable : (prefixWord ++ tailWord_550303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550303).length < 2 ^ (prefixWord ++ tailWord_550303).sum := by decide
  have hdescent : baseEnd_550303 < baseStart_550303 := by decide
  rcases family_descends (prefixWord ++ tailWord_550303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550307 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_550307 : Nat := 118140960795 + 550307 * 2 ^ 59
def prefixEnd_550307 : Nat := 4983230072969 + 3 ^ 40 * 550307 * 2
def baseEnd_550307 : Nat := 251175109807896582250391

theorem tailTrace_550307 : CollatzResearch.WordTrace tailWord_550307 prefixEnd_550307 251175109807896582250391 := by
  unfold tailWord_550307
  simp only [CollatzResearch.WordTrace]
  refine ⟨20071345217339198798185175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13380896811559465865456783 20071345217339198798185175)
  ·
    refine ⟨30107017826008798197277763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20071345217339198798185175 30107017826008798197277763)
    ·
      refine ⟨45160526739013197295916645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30107017826008798197277763 45160526739013197295916645)
      ·
        refine ⟨8467598763564974492984371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45160526739013197295916645 8467598763564974492984371)
        ·
          refine ⟨12701398145347461739476557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467598763564974492984371 12701398145347461739476557)
          ·
            refine ⟨4763024304505298152303709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12701398145347461739476557 4763024304505298152303709)
            ·
              refine ⟨1786134114189486807113891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4763024304505298152303709 1786134114189486807113891)
              ·
                refine ⟨2679201171284230210670837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786134114189486807113891 2679201171284230210670837)
                ·
                  refine ⟨251175109807896582250391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2679201171284230210670837 251175109807896582250391)
                  ·
                    rfl

theorem cell20_550307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_550307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550307 prefixEnd_550307 := by exact prefixLift 550307
  have htrace : WordTrace (prefixWord ++ tailWord_550307) baseStart_550307 baseEnd_550307 := by
    simpa [prefixWord, tailWord_550307, baseEnd_550307] using wordTrace_append hprefix tailTrace_550307
  have hstable : (prefixWord ++ tailWord_550307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550307).length < 2 ^ (prefixWord ++ tailWord_550307).sum := by decide
  have hdescent : baseEnd_550307 < baseStart_550307 := by decide
  rcases family_descends (prefixWord ++ tailWord_550307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550369 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_550369 : Nat := 118140960795 + 550369 * 2 ^ 59
def prefixEnd_550369 : Nat := 4983230072969 + 3 ^ 40 * 550369 * 2
def baseEnd_550369 : Nat := 251203408297299922183471

theorem tailTrace_550369 : CollatzResearch.WordTrace tailWord_550369 prefixEnd_550369 251203408297299922183471 := by
  unfold tailWord_550369
  simp only [CollatzResearch.WordTrace]
  refine ⟨20073606543114583386942161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13382404362076388924628107 20073606543114583386942161)
  ·
    refine ⟨15055204907335937540206621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20073606543114583386942161 15055204907335937540206621)
    ·
      refine ⟨5645701840250976577577483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15055204907335937540206621 5645701840250976577577483)
      ·
        refine ⟨8468552760376464866366225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645701840250976577577483 8468552760376464866366225)
        ·
          refine ⟨6351414570282348649774669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8468552760376464866366225 6351414570282348649774669)
          ·
            refine ⟨2381780463855880743665501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6351414570282348649774669 2381780463855880743665501)
            ·
              refine ⟨893167673945955278874563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2381780463855880743665501 893167673945955278874563)
              ·
                refine ⟨1339751510918932918311845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893167673945955278874563 1339751510918932918311845)
                ·
                  refine ⟨251203408297299922183471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1339751510918932918311845 251203408297299922183471)
                  ·
                    rfl

theorem cell20_550369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_550369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550369 prefixEnd_550369 := by exact prefixLift 550369
  have htrace : WordTrace (prefixWord ++ tailWord_550369) baseStart_550369 baseEnd_550369 := by
    simpa [prefixWord, tailWord_550369, baseEnd_550369] using wordTrace_append hprefix tailTrace_550369
  have hstable : (prefixWord ++ tailWord_550369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550369).length < 2 ^ (prefixWord ++ tailWord_550369).sum := by decide
  have hdescent : baseEnd_550369 < baseStart_550369 := by decide
  rcases family_descends (prefixWord ++ tailWord_550369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550376 : List Nat := [2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_550376 : Nat := 118140960795 + 550376 * 2 ^ 59
def prefixEnd_550376 : Nat := 4983230072969 + 3 ^ 40 * 550376 * 2
def baseEnd_550376 : Nat := 83735534429346336316703

theorem tailTrace_550376 : CollatzResearch.WordTrace tailWord_550376 prefixEnd_550376 83735534429346336316703 := by
  unfold tailWord_550376
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036930927044611791223491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13382574569392815721631321 10036930927044611791223491)
  ·
    refine ⟨15055396390566917686835237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036930927044611791223491 15055396390566917686835237)
    ·
      refine ⟨2822886823231297066281607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15055396390566917686835237 2822886823231297066281607)
      ·
        refine ⟨4234330234846945599422411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822886823231297066281607 4234330234846945599422411)
        ·
          refine ⟨6351495352270418399133617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234330234846945599422411 6351495352270418399133617)
          ·
            refine ⟨4763621514202813799350213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6351495352270418399133617 4763621514202813799350213)
            ·
              refine ⟨893179033913027587378165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4763621514202813799350213 893179033913027587378165)
              ·
                refine ⟨83735534429346336316703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893179033913027587378165 83735534429346336316703)
                ·
                  rfl

theorem cell20_550376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_550376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550376 prefixEnd_550376 := by exact prefixLift 550376
  have htrace : WordTrace (prefixWord ++ tailWord_550376) baseStart_550376 baseEnd_550376 := by
    simpa [prefixWord, tailWord_550376, baseEnd_550376] using wordTrace_append hprefix tailTrace_550376
  have hstable : (prefixWord ++ tailWord_550376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550376).length < 2 ^ (prefixWord ++ tailWord_550376).sum := by decide
  have hdescent : baseEnd_550376 < baseStart_550376 := by decide
  rcases family_descends (prefixWord ++ tailWord_550376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550413 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_550413 : Nat := 118140960795 + 550413 * 2 ^ 59
def prefixEnd_550413 : Nat := 4983230072969 + 3 ^ 40 * 550413 * 2
def baseEnd_550413 : Nat := 251223491096231324716625

theorem tailTrace_550413 : CollatzResearch.WordTrace tailWord_550413 prefixEnd_550413 251223491096231324716625 := by
  unfold tailWord_550413
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075211354955178901543893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13383474236636785934362595 20075211354955178901543893)
  ·
    refine ⟨470512766131762005504935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20075211354955178901543893 470512766131762005504935)
    ·
      refine ⟨705769149197643008257403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470512766131762005504935 705769149197643008257403)
      ·
        refine ⟨1058653723796464512386105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705769149197643008257403 1058653723796464512386105)
        ·
          refine ⟨793990292847348384289579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058653723796464512386105 793990292847348384289579)
          ·
            refine ⟨1190985439271022576434369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793990292847348384289579 1190985439271022576434369)
            ·
              refine ⟨893239079453266932325777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190985439271022576434369 893239079453266932325777)
              ·
                refine ⟨669929309589950199244333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893239079453266932325777 669929309589950199244333)
                ·
                  refine ⟨251223491096231324716625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669929309589950199244333 251223491096231324716625)
                  ·
                    rfl

theorem cell20_550413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_550413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550413 prefixEnd_550413 := by exact prefixLift 550413
  have htrace : WordTrace (prefixWord ++ tailWord_550413) baseStart_550413 baseEnd_550413 := by
    simpa [prefixWord, tailWord_550413, baseEnd_550413] using wordTrace_append hprefix tailTrace_550413
  have hstable : (prefixWord ++ tailWord_550413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550413).length < 2 ^ (prefixWord ++ tailWord_550413).sum := by decide
  have hdescent : baseEnd_550413 < baseStart_550413 := by decide
  rcases family_descends (prefixWord ++ tailWord_550413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550414 : List Nat := [4, 1, 1, 2, 4, 8]
def baseStart_550414 : Nat := 118140960795 + 550414 * 2 ^ 59
def prefixEnd_550414 : Nat := 4983230072969 + 3 ^ 40 * 550414 * 2
def baseEnd_550414 : Nat := 9304590649017769099381

theorem tailTrace_550414 : CollatzResearch.WordTrace tailWord_550414 prefixEnd_550414 9304590649017769099381 := by
  unfold tailWord_550414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509405978493944509041287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13383498551967704048220197 2509405978493944509041287)
  ·
    refine ⟨3764108967740916763561931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2509405978493944509041287 3764108967740916763561931)
    ·
      refine ⟨5646163451611375145342897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764108967740916763561931 5646163451611375145342897)
      ·
        refine ⟨4234622588708531359007173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646163451611375145342897 4234622588708531359007173)
        ·
          refine ⟨793991735382849629813845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4234622588708531359007173 793991735382849629813845)
          ·
            refine ⟨9304590649017769099381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 793991735382849629813845 9304590649017769099381)
            ·
              rfl

theorem cell20_550414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 8].length) (baseStart_550414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550414 prefixEnd_550414 := by exact prefixLift 550414
  have htrace : WordTrace (prefixWord ++ tailWord_550414) baseStart_550414 baseEnd_550414 := by
    simpa [prefixWord, tailWord_550414, baseEnd_550414] using wordTrace_append hprefix tailTrace_550414
  have hstable : (prefixWord ++ tailWord_550414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550414).length < 2 ^ (prefixWord ++ tailWord_550414).sum := by decide
  have hdescent : baseEnd_550414 < baseStart_550414 := by decide
  rcases family_descends (prefixWord ++ tailWord_550414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550420 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_550420 : Nat := 118140960795 + 550420 * 2 ^ 59
def prefixEnd_550420 : Nat := 4983230072969 + 3 ^ 40 * 550420 * 2
def baseEnd_550420 : Nat := 251226686086970411483263

theorem tailTrace_550420 : CollatzResearch.WordTrace tailWord_550420 prefixEnd_550420 251226686086970411483263 := by
  unfold tailWord_550420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10037733332964909548524357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13383644443953212731365809 10037733332964909548524357)
  ·
    refine ⟨1882074999930920540348317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10037733332964909548524357 1882074999930920540348317)
    ·
      refine ⟨705778124974095202630619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1882074999930920540348317 705778124974095202630619)
      ·
        refine ⟨1058667187461142803945929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705778124974095202630619 1058667187461142803945929)
        ·
          refine ⟨794000390595857102959447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058667187461142803945929 794000390595857102959447)
          ·
            refine ⟨1191000585893785654439171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794000390595857102959447 1191000585893785654439171)
            ·
              refine ⟨1786500878840678481658757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191000585893785654439171 1786500878840678481658757)
              ·
                refine ⟨334968914782627215311017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1786500878840678481658757 334968914782627215311017)
                ·
                  refine ⟨251226686086970411483263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334968914782627215311017 251226686086970411483263)
                  ·
                    rfl

theorem cell20_550420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_550420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550420 prefixEnd_550420 := by exact prefixLift 550420
  have htrace : WordTrace (prefixWord ++ tailWord_550420) baseStart_550420 baseEnd_550420 := by
    simpa [prefixWord, tailWord_550420, baseEnd_550420] using wordTrace_append hprefix tailTrace_550420
  have hstable : (prefixWord ++ tailWord_550420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550420).length < 2 ^ (prefixWord ++ tailWord_550420).sum := by decide
  have hdescent : baseEnd_550420 < baseStart_550420 := by decide
  rcases family_descends (prefixWord ++ tailWord_550420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550476 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_550476 : Nat := 118140960795 + 550476 * 2 ^ 59
def prefixEnd_550476 : Nat := 4983230072969 + 3 ^ 40 * 550476 * 2
def baseEnd_550476 : Nat := 251252246012883105616367

theorem tailTrace_550476 : CollatzResearch.WordTrace tailWord_550476 prefixEnd_550476 251252246012883105616367 := by
  unfold tailWord_550476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038754576863470330543641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13385006102484627107391521 10038754576863470330543641)
  ·
    refine ⟨7529065932647602747907731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10038754576863470330543641 7529065932647602747907731)
    ·
      refine ⟨11293598898971404121861597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529065932647602747907731 11293598898971404121861597)
      ·
        refine ⟨4235099587114276545698099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11293598898971404121861597 4235099587114276545698099)
        ·
          refine ⟨6352649380671414818547149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235099587114276545698099 6352649380671414818547149)
          ·
            refine ⟨2382243517751780556955181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6352649380671414818547149 2382243517751780556955181)
            ·
              refine ⟨893341319156917708858193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382243517751780556955181 893341319156917708858193)
              ·
                refine ⟨670005989367688281643645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893341319156917708858193 670005989367688281643645)
                ·
                  refine ⟨251252246012883105616367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670005989367688281643645 251252246012883105616367)
                  ·
                    rfl

theorem cell20_550476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_550476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550476 prefixEnd_550476 := by exact prefixLift 550476
  have htrace : WordTrace (prefixWord ++ tailWord_550476) baseStart_550476 baseEnd_550476 := by
    simpa [prefixWord, tailWord_550476, baseEnd_550476] using wordTrace_append hprefix tailTrace_550476
  have hstable : (prefixWord ++ tailWord_550476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550476).length < 2 ^ (prefixWord ++ tailWord_550476).sum := by decide
  have hdescent : baseEnd_550476 < baseStart_550476 := by decide
  rcases family_descends (prefixWord ++ tailWord_550476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550517 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 2]
def baseStart_550517 : Nat := 118140960795 + 550517 * 2 ^ 59
def prefixEnd_550517 : Nat := 4983230072969 + 3 ^ 40 * 550517 * 2
def baseEnd_550517 : Nat := 251270959530069185249533

theorem tailTrace_550517 : CollatzResearch.WordTrace tailWord_550517 prefixEnd_550517 251270959530069185249533 := by
  unfold tailWord_550517
  simp only [CollatzResearch.WordTrace]
  refine ⟨20079004546578404663329805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13386003031052269775553203 20079004546578404663329805)
  ·
    refine ⟨7529626704966901748748677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20079004546578404663329805 7529626704966901748748677)
    ·
      refine ⟨1411805007181294077890377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7529626704966901748748677 1411805007181294077890377)
      ·
        refine ⟨1058853755385970558417783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411805007181294077890377 1058853755385970558417783)
        ·
          refine ⟨1588280633078955837626675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058853755385970558417783 1588280633078955837626675)
          ·
            refine ⟨2382420949618433756440013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588280633078955837626675 2382420949618433756440013)
            ·
              refine ⟨893407856106912658665005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382420949618433756440013 893407856106912658665005)
              ·
                refine ⟨335027946040092246999377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893407856106912658665005 335027946040092246999377)
                ·
                  refine ⟨251270959530069185249533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335027946040092246999377 251270959530069185249533)
                  ·
                    rfl

theorem cell20_550517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_550517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550517 prefixEnd_550517 := by exact prefixLift 550517
  have htrace : WordTrace (prefixWord ++ tailWord_550517) baseStart_550517 baseEnd_550517 := by
    simpa [prefixWord, tailWord_550517, baseEnd_550517] using wordTrace_append hprefix tailTrace_550517
  have hstable : (prefixWord ++ tailWord_550517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550517).length < 2 ^ (prefixWord ++ tailWord_550517).sum := by decide
  have hdescent : baseEnd_550517 < baseStart_550517 := by decide
  rcases family_descends (prefixWord ++ tailWord_550517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550535 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_550535 : Nat := 118140960795 + 550535 * 2 ^ 59
def prefixEnd_550535 : Nat := 4983230072969 + 3 ^ 40 * 550535 * 2
def baseEnd_550535 : Nat := 251279175220541122649459

theorem tailTrace_550535 : CollatzResearch.WordTrace tailWord_550535 prefixEnd_550535 251279175220541122649459 := by
  unfold tailWord_550535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20079661060513193737485059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13386440707008795824990039 20079661060513193737485059)
  ·
    refine ⟨30119491590769790606227589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20079661060513193737485059 30119491590769790606227589)
    ·
      refine ⟨5647404673269335738667673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30119491590769790606227589 5647404673269335738667673)
      ·
        refine ⟨4235553504952001804000755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5647404673269335738667673 4235553504952001804000755)
        ·
          refine ⟨6353330257428002706001133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235553504952001804000755 6353330257428002706001133)
          ·
            refine ⟨2382498846535501014750425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6353330257428002706001133 2382498846535501014750425)
            ·
              refine ⟨1786874134901625761062819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382498846535501014750425 1786874134901625761062819)
              ·
                refine ⟨2680311202352438641594229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786874134901625761062819 2680311202352438641594229)
                ·
                  refine ⟨251279175220541122649459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2680311202352438641594229 251279175220541122649459)
                  ·
                    rfl

theorem cell20_550535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_550535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550535 prefixEnd_550535 := by exact prefixLift 550535
  have htrace : WordTrace (prefixWord ++ tailWord_550535) baseStart_550535 baseEnd_550535 := by
    simpa [prefixWord, tailWord_550535, baseEnd_550535] using wordTrace_append hprefix tailTrace_550535
  have hstable : (prefixWord ++ tailWord_550535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550535).length < 2 ^ (prefixWord ++ tailWord_550535).sum := by decide
  have hdescent : baseEnd_550535 < baseStart_550535 := by decide
  rcases family_descends (prefixWord ++ tailWord_550535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550538 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_550538 : Nat := 118140960795 + 550538 * 2 ^ 59
def prefixEnd_550538 : Nat := 4983230072969 + 3 ^ 40 * 550538 * 2
def baseEnd_550538 : Nat := 251280544502286445549447

theorem tailTrace_550538 : CollatzResearch.WordTrace tailWord_550538 prefixEnd_550538 251280544502286445549447 := by
  unfold tailWord_550538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019942619875581312461067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13386513653001550166562845 5019942619875581312461067)
  ·
    refine ⟨7529913929813371968691601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019942619875581312461067 7529913929813371968691601)
    ·
      refine ⟨5647435447360028976518701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7529913929813371968691601 5647435447360028976518701)
      ·
        refine ⟨2117788292760010866194513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5647435447360028976518701 2117788292760010866194513)
        ·
          refine ⟨1588341219570008149645885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117788292760010866194513 1588341219570008149645885)
          ·
            refine ⟨595627957338753056117207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1588341219570008149645885 595627957338753056117207)
            ·
              refine ⟨893441936008129584175811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595627957338753056117207 893441936008129584175811)
              ·
                refine ⟨1340162904012194376263717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893441936008129584175811 1340162904012194376263717)
                ·
                  refine ⟨251280544502286445549447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340162904012194376263717 251280544502286445549447)
                  ·
                    rfl

theorem cell20_550538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_550538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550538 prefixEnd_550538 := by exact prefixLift 550538
  have htrace : WordTrace (prefixWord ++ tailWord_550538) baseStart_550538 baseEnd_550538 := by
    simpa [prefixWord, tailWord_550538, baseEnd_550538] using wordTrace_append hprefix tailTrace_550538
  have hstable : (prefixWord ++ tailWord_550538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550538).length < 2 ^ (prefixWord ++ tailWord_550538).sum := by decide
  have hdescent : baseEnd_550538 < baseStart_550538 := by decide
  rcases family_descends (prefixWord ++ tailWord_550538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550552 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_550552 : Nat := 118140960795 + 550552 * 2 ^ 59
def prefixEnd_550552 : Nat := 4983230072969 + 3 ^ 40 * 550552 * 2
def baseEnd_550552 : Nat := 251286934483764619082723

theorem tailTrace_550552 : CollatzResearch.WordTrace tailWord_550552 prefixEnd_550552 251286934483764619082723 := by
  unfold tailWord_550552
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040140550725802820426955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13386854067634403760569273 10040140550725802820426955)
  ·
    refine ⟨15060210826088704230640433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040140550725802820426955 15060210826088704230640433)
    ·
      refine ⟨11295158119566528172980325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15060210826088704230640433 11295158119566528172980325)
      ·
        refine ⟨2117842147418724032433811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11295158119566528172980325 2117842147418724032433811)
        ·
          refine ⟨3176763221128086048650717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117842147418724032433811 3176763221128086048650717)
          ·
            refine ⟨1191286207923032268244019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3176763221128086048650717 1191286207923032268244019)
            ·
              refine ⟨1786929311884548402366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191286207923032268244019 1786929311884548402366029)
              ·
                refine ⟨670098491956705650887261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1786929311884548402366029 670098491956705650887261)
                ·
                  refine ⟨251286934483764619082723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670098491956705650887261 251286934483764619082723)
                  ·
                    rfl

theorem cell20_550552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_550552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550552 prefixEnd_550552 := by exact prefixLift 550552
  have htrace : WordTrace (prefixWord ++ tailWord_550552) baseStart_550552 baseEnd_550552 := by
    simpa [prefixWord, tailWord_550552, baseEnd_550552] using wordTrace_append hprefix tailTrace_550552
  have hstable : (prefixWord ++ tailWord_550552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550552).length < 2 ^ (prefixWord ++ tailWord_550552).sum := by decide
  have hdescent : baseEnd_550552 < baseStart_550552 := by decide
  rcases family_descends (prefixWord ++ tailWord_550552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550590 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_550590 : Nat := 118140960795 + 550590 * 2 ^ 59
def prefixEnd_550590 : Nat := 4983230072969 + 3 ^ 40 * 550590 * 2
def baseEnd_550590 : Nat := 251304278719205375815901

theorem tailTrace_550590 : CollatzResearch.WordTrace tailWord_550590 prefixEnd_550590 251304278719205375815901 := by
  unfold tailWord_550590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510208384414242266342153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13387778050209292087158149 2510208384414242266342153)
  ·
    refine ⟨1882656288310681699756615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2510208384414242266342153 1882656288310681699756615)
    ·
      refine ⟨2823984432466022549634923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882656288310681699756615 2823984432466022549634923)
      ·
        refine ⟨4235976648699033824452385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823984432466022549634923 4235976648699033824452385)
        ·
          refine ⟨3176982486524275368339289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4235976648699033824452385 3176982486524275368339289)
          ·
            refine ⟨2382736864893206526254467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176982486524275368339289 2382736864893206526254467)
            ·
              refine ⟨3574105297339809789381701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382736864893206526254467 3574105297339809789381701)
              ·
                refine ⟨670144743251214335509069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3574105297339809789381701 670144743251214335509069)
                ·
                  refine ⟨251304278719205375815901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670144743251214335509069 251304278719205375815901)
                  ·
                    rfl

theorem cell20_550590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_550590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550590 prefixEnd_550590 := by exact prefixLift 550590
  have htrace : WordTrace (prefixWord ++ tailWord_550590) baseStart_550590 baseEnd_550590 := by
    simpa [prefixWord, tailWord_550590, baseEnd_550590] using wordTrace_append hprefix tailTrace_550590
  have hstable : (prefixWord ++ tailWord_550590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550590).length < 2 ^ (prefixWord ++ tailWord_550590).sum := by decide
  have hdescent : baseEnd_550590 < baseStart_550590 := by decide
  rcases family_descends (prefixWord ++ tailWord_550590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550597 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 2]
def baseStart_550597 : Nat := 118140960795 + 550597 * 2 ^ 59
def prefixEnd_550597 : Nat := 4983230072969 + 3 ^ 40 * 550597 * 2
def baseEnd_550597 : Nat := 251307473709944462582539

theorem tailTrace_550597 : CollatzResearch.WordTrace tailWord_550597 prefixEnd_550597 251307473709944462582539 := by
  unfold tailWord_550597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081922386288578326242045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13387948257525718884161363 20081922386288578326242045)
  ·
    refine ⟨7530720894858216872340767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20081922386288578326242045 7530720894858216872340767)
    ·
      refine ⟨11296081342287325308511151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7530720894858216872340767 11296081342287325308511151)
      ·
        refine ⟨16944122013430987962766727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11296081342287325308511151 16944122013430987962766727)
        ·
          refine ⟨25416183020146481944150091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16944122013430987962766727 25416183020146481944150091)
          ·
            refine ⟨38124274530219722916225137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25416183020146481944150091 38124274530219722916225137)
            ·
              refine ⟨28593205897664792187168853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38124274530219722916225137 28593205897664792187168853)
              ·
                refine ⟨335076631613259283443385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28593205897664792187168853 335076631613259283443385)
                ·
                  refine ⟨251307473709944462582539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335076631613259283443385 251307473709944462582539)
                  ·
                    rfl

theorem cell20_550597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_550597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550597 prefixEnd_550597 := by exact prefixLift 550597
  have htrace : WordTrace (prefixWord ++ tailWord_550597) baseStart_550597 baseEnd_550597 := by
    simpa [prefixWord, tailWord_550597, baseEnd_550597] using wordTrace_append hprefix tailTrace_550597
  have hstable : (prefixWord ++ tailWord_550597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550597).length < 2 ^ (prefixWord ++ tailWord_550597).sum := by decide
  have hdescent : baseEnd_550597 < baseStart_550597 := by decide
  rcases family_descends (prefixWord ++ tailWord_550597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550618 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_550618 : Nat := 118140960795 + 550618 * 2 ^ 59
def prefixEnd_550618 : Nat := 4983230072969 + 3 ^ 40 * 550618 * 2
def baseEnd_550618 : Nat := 251317058682161722882453

theorem tailTrace_550618 : CollatzResearch.WordTrace tailWord_550618 prefixEnd_550618 251317058682161722882453 := by
  unfold tailWord_550618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020672079803124728189127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13388458879474999275171005 5020672079803124728189127)
  ·
    refine ⟨7531008119704687092283691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5020672079803124728189127 7531008119704687092283691)
    ·
      refine ⟨11296512179557030638425537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7531008119704687092283691 11296512179557030638425537)
      ·
        refine ⟨8472384134667772978819153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11296512179557030638425537 8472384134667772978819153)
        ·
          refine ⟨6354288101000829734114365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8472384134667772978819153 6354288101000829734114365)
          ·
            refine ⟨2382858037875311150292887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6354288101000829734114365 2382858037875311150292887)
            ·
              refine ⟨3574287056812966725439331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382858037875311150292887 3574287056812966725439331)
              ·
                refine ⟨5361430585219450088158997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574287056812966725439331 5361430585219450088158997)
                ·
                  refine ⟨251317058682161722882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5361430585219450088158997 251317058682161722882453)
                  ·
                    rfl

theorem cell20_550618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_550618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550618 prefixEnd_550618 := by exact prefixLift 550618
  have htrace : WordTrace (prefixWord ++ tailWord_550618) baseStart_550618 baseEnd_550618 := by
    simpa [prefixWord, tailWord_550618, baseEnd_550618] using wordTrace_append hprefix tailTrace_550618
  have hstable : (prefixWord ++ tailWord_550618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550618).length < 2 ^ (prefixWord ++ tailWord_550618).sum := by decide
  have hdescent : baseEnd_550618 < baseStart_550618 := by decide
  rcases family_descends (prefixWord ++ tailWord_550618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550635 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 2]
def baseStart_550635 : Nat := 118140960795 + 550635 * 2 ^ 59
def prefixEnd_550635 : Nat := 4983230072969 + 3 ^ 40 * 550635 * 2
def baseEnd_550635 : Nat := 251324817945385219315717

theorem tailTrace_550635 : CollatzResearch.WordTrace tailWord_550635 prefixEnd_550635 251324817945385219315717 := by
  unfold tailWord_550635
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083308360150910816125359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13388872240100607210750239 20083308360150910816125359)
  ·
    refine ⟨30124962540226366224188039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20083308360150910816125359 30124962540226366224188039)
    ·
      refine ⟨45187443810339549336282059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30124962540226366224188039 45187443810339549336282059)
      ·
        refine ⟨67781165715509324004423089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45187443810339549336282059 67781165715509324004423089)
        ·
          refine ⟨50835874286631993003317317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67781165715509324004423089 50835874286631993003317317)
          ·
            refine ⟨9531726428743498688121997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50835874286631993003317317 9531726428743498688121997)
            ·
              refine ⟨3574397410778812008045749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9531726428743498688121997 3574397410778812008045749)
              ·
                refine ⟨335099757260513625754289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3574397410778812008045749 335099757260513625754289)
                ·
                  refine ⟨251324817945385219315717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335099757260513625754289 251324817945385219315717)
                  ·
                    rfl

theorem cell20_550635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2].length) (baseStart_550635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550635 prefixEnd_550635 := by exact prefixLift 550635
  have htrace : WordTrace (prefixWord ++ tailWord_550635) baseStart_550635 baseEnd_550635 := by
    simpa [prefixWord, tailWord_550635, baseEnd_550635] using wordTrace_append hprefix tailTrace_550635
  have hstable : (prefixWord ++ tailWord_550635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550635).length < 2 ^ (prefixWord ++ tailWord_550635).sum := by decide
  have hdescent : baseEnd_550635 < baseStart_550635 := by decide
  rcases family_descends (prefixWord ++ tailWord_550635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550680 : List Nat := [2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_550680 : Nat := 118140960795 + 550680 * 2 ^ 59
def prefixEnd_550680 : Nat := 4983230072969 + 3 ^ 40 * 550680 * 2
def baseEnd_550680 : Nat := 83781785723855020938511

theorem tailTrace_550680 : CollatzResearch.WordTrace tailWord_550680 prefixEnd_550680 83781785723855020938511 := by
  unfold tailWord_550680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042474822493941750756747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13389966429991922334342329 10042474822493941750756747)
  ·
    refine ⟨15063712233740912626135121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042474822493941750756747 15063712233740912626135121)
    ·
      refine ⟨11297784175305684469601341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15063712233740912626135121 11297784175305684469601341)
      ·
        refine ⟨4236669065739631676100503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11297784175305684469601341 4236669065739631676100503)
        ·
          refine ⟨6355003598609447514150755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236669065739631676100503 6355003598609447514150755)
          ·
            refine ⟨9532505397914171271226133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355003598609447514150755 9532505397914171271226133)
            ·
              refine ⟨446836190527226778338725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9532505397914171271226133 446836190527226778338725)
              ·
                refine ⟨83781785723855020938511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446836190527226778338725 83781785723855020938511)
                ·
                  rfl

theorem cell20_550680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_550680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550680 prefixEnd_550680 := by exact prefixLift 550680
  have htrace : WordTrace (prefixWord ++ tailWord_550680) baseStart_550680 baseEnd_550680 := by
    simpa [prefixWord, tailWord_550680, baseEnd_550680] using wordTrace_append hprefix tailTrace_550680
  have hstable : (prefixWord ++ tailWord_550680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550680).length < 2 ^ (prefixWord ++ tailWord_550680).sum := by decide
  have hdescent : baseEnd_550680 < baseStart_550680 := by decide
  rcases family_descends (prefixWord ++ tailWord_550680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550707 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 2]
def baseStart_550707 : Nat := 118140960795 + 550707 * 2 ^ 59
def prefixEnd_550707 : Nat := 4983230072969 + 3 ^ 40 * 550707 * 2
def baseEnd_550707 : Nat := 251357680707272968915423

theorem tailTrace_550707 : CollatzResearch.WordTrace tailWord_550707 prefixEnd_550707 251357680707272968915423 := by
  unfold tailWord_550707
  simp only [CollatzResearch.WordTrace]
  refine ⟨20085934415890067112746375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13390622943926711408497583 20085934415890067112746375)
  ·
    refine ⟨30128901623835100669119563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20085934415890067112746375 30128901623835100669119563)
    ·
      refine ⟨45193352435752651003679345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30128901623835100669119563 45193352435752651003679345)
      ·
        refine ⟨33895014326814488252759509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45193352435752651003679345 33895014326814488252759509)
        ·
          refine ⟨794414398284714568424051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33895014326814488252759509 794414398284714568424051)
          ·
            refine ⟨1191621597427071852636077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794414398284714568424051 1191621597427071852636077)
            ·
              refine ⟨446858099035151944738529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1191621597427071852636077 446858099035151944738529)
              ·
                refine ⟨335143574276363958553897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446858099035151944738529 335143574276363958553897)
                ·
                  refine ⟨251357680707272968915423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335143574276363958553897 251357680707272968915423)
                  ·
                    rfl

theorem cell20_550707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2].length) (baseStart_550707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550707 prefixEnd_550707 := by exact prefixLift 550707
  have htrace : WordTrace (prefixWord ++ tailWord_550707) baseStart_550707 baseEnd_550707 := by
    simpa [prefixWord, tailWord_550707, baseEnd_550707] using wordTrace_append hprefix tailTrace_550707
  have hstable : (prefixWord ++ tailWord_550707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550707).length < 2 ^ (prefixWord ++ tailWord_550707).sum := by decide
  have hdescent : baseEnd_550707 < baseStart_550707 := by decide
  rcases family_descends (prefixWord ++ tailWord_550707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550718 : List Nat := [4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_550718 : Nat := 118140960795 + 550718 * 2 ^ 59
def prefixEnd_550718 : Nat := 4983230072969 + 3 ^ 40 * 550718 * 2
def baseEnd_550718 : Nat := 83787567135668606516237

theorem tailTrace_550718 : CollatzResearch.WordTrace tailWord_550718 prefixEnd_550718 83787567135668606516237 := by
  unfold tailWord_550718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510791952356276998924601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13390890412566810660931205 2510791952356276998924601)
  ·
    refine ⟨1883093964267207749193451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2510791952356276998924601 1883093964267207749193451)
    ·
      refine ⟨2824640946400811623790177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883093964267207749193451 2824640946400811623790177)
      ·
        refine ⟨2118480709800608717842633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824640946400811623790177 2118480709800608717842633)
        ·
          refine ⟨1588860532350456538381975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118480709800608717842633 1588860532350456538381975)
          ·
            refine ⟨2383290798525684807572963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588860532350456538381975 2383290798525684807572963)
            ·
              refine ⟨3574936197788527211359445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383290798525684807572963 3574936197788527211359445)
              ·
                refine ⟨83787567135668606516237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3574936197788527211359445 83787567135668606516237)
                ·
                  rfl

theorem cell20_550718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_550718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550718 prefixEnd_550718 := by exact prefixLift 550718
  have htrace : WordTrace (prefixWord ++ tailWord_550718) baseStart_550718 baseEnd_550718 := by
    simpa [prefixWord, tailWord_550718, baseEnd_550718] using wordTrace_append hprefix tailTrace_550718
  have hstable : (prefixWord ++ tailWord_550718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550718).length < 2 ^ (prefixWord ++ tailWord_550718).sum := by decide
  have hdescent : baseEnd_550718 < baseStart_550718 := by decide
  rcases family_descends (prefixWord ++ tailWord_550718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550725 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_550725 : Nat := 118140960795 + 550725 * 2 ^ 59
def prefixEnd_550725 : Nat := 4983230072969 + 3 ^ 40 * 550725 * 2
def baseEnd_550725 : Nat := 251365896397744906315349

theorem tailTrace_550725 : CollatzResearch.WordTrace tailWord_550725 prefixEnd_550725 251365896397744906315349 := by
  unfold tailWord_550725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20086590929824856186901629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13391060619883237457934419 20086590929824856186901629)
  ·
    refine ⟨7532471598684321070088111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20086590929824856186901629 7532471598684321070088111)
    ·
      refine ⟨11298707398026481605132167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7532471598684321070088111 11298707398026481605132167)
      ·
        refine ⟨16948061097039722407698251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11298707398026481605132167 16948061097039722407698251)
        ·
          refine ⟨25422091645559583611547377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16948061097039722407698251 25422091645559583611547377)
          ·
            refine ⟨19066568734169687708660533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25422091645559583611547377 19066568734169687708660533)
            ·
              refine ⟨1787490818828408222686925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19066568734169687708660533 1787490818828408222686925)
              ·
                refine ⟨670309057060653083507597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787490818828408222686925 670309057060653083507597)
                ·
                  refine ⟨251365896397744906315349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670309057060653083507597 251365896397744906315349)
                  ·
                    rfl

theorem cell20_550725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_550725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550725 prefixEnd_550725 := by exact prefixLift 550725
  have htrace : WordTrace (prefixWord ++ tailWord_550725) baseStart_550725 baseEnd_550725 := by
    simpa [prefixWord, tailWord_550725, baseEnd_550725] using wordTrace_append hprefix tailTrace_550725
  have hstable : (prefixWord ++ tailWord_550725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550725).length < 2 ^ (prefixWord ++ tailWord_550725).sum := by decide
  have hdescent : baseEnd_550725 < baseStart_550725 := by decide
  rcases family_descends (prefixWord ++ tailWord_550725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550756 : List Nat := [2, 3, 1, 1, 6, 7]
def baseStart_550756 : Nat := 118140960795 + 550756 * 2 ^ 59
def prefixEnd_550756 : Nat := 4983230072969 + 3 ^ 40 * 550756 * 2
def baseEnd_550756 : Nat := 9310372060831354677107

theorem tailTrace_550756 : CollatzResearch.WordTrace tailWord_550756 prefixEnd_550756 9310372060831354677107 := by
  unfold tailWord_550756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043860796356274240640061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13391814395141698987520081 10043860796356274240640061)
  ·
    refine ⟨3766447798633602840240023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10043860796356274240640061 3766447798633602840240023)
    ·
      refine ⟨5649671697950404260360035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766447798633602840240023 5649671697950404260360035)
      ·
        refine ⟨8474507546925606390540053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649671697950404260360035 8474507546925606390540053)
        ·
          refine ⟨397242541262137799556565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8474507546925606390540053 397242541262137799556565)
          ·
            refine ⟨9310372060831354677107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 397242541262137799556565 9310372060831354677107)
            ·
              rfl

theorem cell20_550756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 7].length) (baseStart_550756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550756 prefixEnd_550756 := by exact prefixLift 550756
  have htrace : WordTrace (prefixWord ++ tailWord_550756) baseStart_550756 baseEnd_550756 := by
    simpa [prefixWord, tailWord_550756, baseEnd_550756] using wordTrace_append hprefix tailTrace_550756
  have hstable : (prefixWord ++ tailWord_550756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550756).length < 2 ^ (prefixWord ++ tailWord_550756).sum := by decide
  have hdescent : baseEnd_550756 < baseStart_550756 := by decide
  rcases family_descends (prefixWord ++ tailWord_550756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550770 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_550770 : Nat := 118140960795 + 550770 * 2 ^ 59
def prefixEnd_550770 : Nat := 4983230072969 + 3 ^ 40 * 550770 * 2
def baseEnd_550770 : Nat := 251386435623924749815165

theorem tailTrace_550770 : CollatzResearch.WordTrace tailWord_550770 prefixEnd_550770 251386435623924749815165 := by
  unfold tailWord_550770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022058053665457218072441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13392154809774552581526509 5022058053665457218072441)
  ·
    refine ⟨3766543540249092913554331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5022058053665457218072441 3766543540249092913554331)
    ·
      refine ⟨5649815310373639370331497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766543540249092913554331 5649815310373639370331497)
      ·
        refine ⟨4237361482780229527748623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5649815310373639370331497 4237361482780229527748623)
        ·
          refine ⟨6356042224170344291622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237361482780229527748623 6356042224170344291622935)
          ·
            refine ⟨9534063336255516437434403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356042224170344291622935 9534063336255516437434403)
            ·
              refine ⟨14301095004383274656151605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534063336255516437434403 14301095004383274656151605)
              ·
                refine ⟨1340727656660931999014213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14301095004383274656151605 1340727656660931999014213)
                ·
                  refine ⟨251386435623924749815165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340727656660931999014213 251386435623924749815165)
                  ·
                    rfl

theorem cell20_550770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_550770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550770 prefixEnd_550770 := by exact prefixLift 550770
  have htrace : WordTrace (prefixWord ++ tailWord_550770) baseStart_550770 baseEnd_550770 := by
    simpa [prefixWord, tailWord_550770, baseEnd_550770] using wordTrace_append hprefix tailTrace_550770
  have hstable : (prefixWord ++ tailWord_550770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550770).length < 2 ^ (prefixWord ++ tailWord_550770).sum := by decide
  have hdescent : baseEnd_550770 < baseStart_550770 := by decide
  rcases family_descends (prefixWord ++ tailWord_550770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550804 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_550804 : Nat := 118140960795 + 550804 * 2 ^ 59
def prefixEnd_550804 : Nat := 4983230072969 + 3 ^ 40 * 550804 * 2
def baseEnd_550804 : Nat := 251401954150371742681693

theorem tailTrace_550804 : CollatzResearch.WordTrace tailWord_550804 prefixEnd_550804 251401954150371742681693 := by
  unfold tailWord_550804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044736148269326339513733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13392981531025768452684977 10044736148269326339513733)
  ·
    refine ⟨1883388027800498688658825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10044736148269326339513733 1883388027800498688658825)
    ·
      refine ⟨1412541020850374016494119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1883388027800498688658825 1412541020850374016494119)
      ·
        refine ⟨2118811531275561024741179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412541020850374016494119 2118811531275561024741179)
        ·
          refine ⟨3178217296913341537111769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118811531275561024741179 3178217296913341537111769)
          ·
            refine ⟨2383662972685006152833827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178217296913341537111769 2383662972685006152833827)
            ·
              refine ⟨3575494459027509229250741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383662972685006152833827 3575494459027509229250741)
              ·
                refine ⟨335202605533828990242257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3575494459027509229250741 335202605533828990242257)
                ·
                  refine ⟨251401954150371742681693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335202605533828990242257 251401954150371742681693)
                  ·
                    rfl

theorem cell20_550804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_550804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550804 prefixEnd_550804 := by exact prefixLift 550804
  have htrace : WordTrace (prefixWord ++ tailWord_550804) baseStart_550804 baseEnd_550804 := by
    simpa [prefixWord, tailWord_550804, baseEnd_550804] using wordTrace_append hprefix tailTrace_550804
  have hstable : (prefixWord ++ tailWord_550804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550804).length < 2 ^ (prefixWord ++ tailWord_550804).sum := by decide
  have hdescent : baseEnd_550804 < baseStart_550804 := by decide
  rcases family_descends (prefixWord ++ tailWord_550804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550818 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_550818 : Nat := 118140960795 + 550818 * 2 ^ 59
def prefixEnd_550818 : Nat := 4983230072969 + 3 ^ 40 * 550818 * 2
def baseEnd_550818 : Nat := 251408344131849916214969

theorem tailTrace_550818 : CollatzResearch.WordTrace tailWord_550818 prefixEnd_550818 251408344131849916214969 := by
  unfold tailWord_550818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022495729621983267509277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13393321945658622046691405 5022495729621983267509277)
  ·
    refine ⟨1883435898608243725315979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5022495729621983267509277 1883435898608243725315979)
    ·
      refine ⟨2825153847912365587973969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883435898608243725315979 2825153847912365587973969)
      ·
        refine ⟨2118865385934274190980477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825153847912365587973969 2118865385934274190980477)
        ·
          refine ⟨794574519725352821617679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118865385934274190980477 794574519725352821617679)
          ·
            refine ⟨1191861779588029232426519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794574519725352821617679 1191861779588029232426519)
            ·
              refine ⟨1787792669382043848639779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191861779588029232426519 1787792669382043848639779)
              ·
                refine ⟨2681689004073065772959669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787792669382043848639779 2681689004073065772959669)
                ·
                  refine ⟨251408344131849916214969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2681689004073065772959669 251408344131849916214969)
                  ·
                    rfl

theorem cell20_550818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_550818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550818 prefixEnd_550818 := by exact prefixLift 550818
  have htrace : WordTrace (prefixWord ++ tailWord_550818) baseStart_550818 baseEnd_550818 := by
    simpa [prefixWord, tailWord_550818, baseEnd_550818] using wordTrace_append hprefix tailTrace_550818
  have hstable : (prefixWord ++ tailWord_550818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550818).length < 2 ^ (prefixWord ++ tailWord_550818).sum := by decide
  have hdescent : baseEnd_550818 < baseStart_550818 := by decide
  rcases family_descends (prefixWord ++ tailWord_550818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550876 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_550876 : Nat := 118140960795 + 550876 * 2 ^ 59
def prefixEnd_550876 : Nat := 4983230072969 + 3 ^ 40 * 550876 * 2
def baseEnd_550876 : Nat := 251434816912259492281399

theorem tailTrace_550876 : CollatzResearch.WordTrace tailWord_550876 prefixEnd_550876 251434816912259492281399 := by
  unfold tailWord_550876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046049176138904487824241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13394732234851872650432321 10046049176138904487824241)
  ·
    refine ⟨7534536882104178365868181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10046049176138904487824241 7534536882104178365868181)
    ·
      refine ⟨353181416348633360900071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7534536882104178365868181 353181416348633360900071)
      ·
        refine ⟨529772124522950041350107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353181416348633360900071 529772124522950041350107)
        ·
          refine ⟨794658186784425062025161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529772124522950041350107 794658186784425062025161)
          ·
            refine ⟨595993640088318796518871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794658186784425062025161 595993640088318796518871)
            ·
              refine ⟨893990460132478194778307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595993640088318796518871 893990460132478194778307)
              ·
                refine ⟨1340985690198717292167461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893990460132478194778307 1340985690198717292167461)
                ·
                  refine ⟨251434816912259492281399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340985690198717292167461 251434816912259492281399)
                  ·
                    rfl

theorem cell20_550876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_550876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550876 prefixEnd_550876 := by exact prefixLift 550876
  have htrace : WordTrace (prefixWord ++ tailWord_550876) baseStart_550876 baseEnd_550876 := by
    simpa [prefixWord, tailWord_550876, baseEnd_550876] using wordTrace_append hprefix tailTrace_550876
  have hstable : (prefixWord ++ tailWord_550876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550876).length < 2 ^ (prefixWord ++ tailWord_550876).sum := by decide
  have hdescent : baseEnd_550876 < baseStart_550876 := by decide
  rcases family_descends (prefixWord ++ tailWord_550876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550894 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_550894 : Nat := 118140960795 + 550894 * 2 ^ 59
def prefixEnd_550894 : Nat := 4983230072969 + 3 ^ 40 * 550894 * 2
def baseEnd_550894 : Nat := 251443032602731429681325

theorem tailTrace_550894 : CollatzResearch.WordTrace tailWord_550894 prefixEnd_550894 251443032602731429681325 := by
  unfold tailWord_550894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511594358276574756225467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13395169910808398699869157 2511594358276574756225467)
  ·
    refine ⟨3767391537414862134338201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511594358276574756225467 3767391537414862134338201)
    ·
      refine ⟨2825543653061146600753651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3767391537414862134338201 2825543653061146600753651)
      ·
        refine ⟨4238315479591719901130477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825543653061146600753651 4238315479591719901130477)
        ·
          refine ⟨1589368304846894962923929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4238315479591719901130477 1589368304846894962923929)
          ·
            refine ⟨1192026228635171222192947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589368304846894962923929 1192026228635171222192947)
            ·
              refine ⟨1788039342952756833289421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192026228635171222192947 1788039342952756833289421)
              ·
                refine ⟨670514753607283812483533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1788039342952756833289421 670514753607283812483533)
                ·
                  refine ⟨251443032602731429681325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670514753607283812483533 251443032602731429681325)
                  ·
                    rfl

theorem cell20_550894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_550894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550894 prefixEnd_550894 := by exact prefixLift 550894
  have htrace : WordTrace (prefixWord ++ tailWord_550894) baseStart_550894 baseEnd_550894 := by
    simpa [prefixWord, tailWord_550894, baseEnd_550894] using wordTrace_append hprefix tailTrace_550894
  have hstable : (prefixWord ++ tailWord_550894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550894).length < 2 ^ (prefixWord ++ tailWord_550894).sum := by decide
  have hdescent : baseEnd_550894 < baseStart_550894 := by decide
  rcases family_descends (prefixWord ++ tailWord_550894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550925 : List Nat := [1, 7, 1, 2, 9]
def baseStart_550925 : Nat := 118140960795 + 550925 * 2 ^ 59
def prefixEnd_550925 : Nat := 4983230072969 + 3 ^ 40 * 550925 * 2
def baseEnd_550925 : Nat := 3104409652437445674665

theorem tailTrace_550925 : CollatzResearch.WordTrace tailWord_550925 prefixEnd_550925 3104409652437445674665 := by
  unfold tailWord_550925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20093885529100290344182229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13395923686066860229454819 20093885529100290344182229)
  ·
    refine ⟨470950442088288054941771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20093885529100290344182229 470950442088288054941771)
    ·
      refine ⟨706425663132432082412657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470950442088288054941771 706425663132432082412657)
      ·
        refine ⟨529819247349324061809493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706425663132432082412657 529819247349324061809493)
        ·
          refine ⟨3104409652437445674665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 529819247349324061809493 3104409652437445674665)
          ·
            rfl

theorem cell20_550925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 9].length) (baseStart_550925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550925 prefixEnd_550925 := by exact prefixLift 550925
  have htrace : WordTrace (prefixWord ++ tailWord_550925) baseStart_550925 baseEnd_550925 := by
    simpa [prefixWord, tailWord_550925, baseEnd_550925] using wordTrace_append hprefix tailTrace_550925
  have hstable : (prefixWord ++ tailWord_550925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550925).length < 2 ^ (prefixWord ++ tailWord_550925).sum := by decide
  have hdescent : baseEnd_550925 < baseStart_550925 := by decide
  rcases family_descends (prefixWord ++ tailWord_550925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550960 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_550960 : Nat := 118140960795 + 550960 * 2 ^ 59
def prefixEnd_550960 : Nat := 4983230072969 + 3 ^ 40 * 550960 * 2
def baseEnd_550960 : Nat := 251473156801128533481055

theorem tailTrace_550960 : CollatzResearch.WordTrace tailWord_550960 prefixEnd_550960 251473156801128533481055 := by
  unfold tailWord_550960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047581041986745660853167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13396774722648994214470889 10047581041986745660853167)
  ·
    refine ⟨15071371562980118491279751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10047581041986745660853167 15071371562980118491279751)
    ·
      refine ⟨22607057344470177736919627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15071371562980118491279751 22607057344470177736919627)
      ·
        refine ⟨33910586016705266605379441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22607057344470177736919627 33910586016705266605379441)
        ·
          refine ⟨25432939512528949954034581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33910586016705266605379441 25432939512528949954034581)
          ·
            refine ⟨1192169039649794529095371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25432939512528949954034581 1192169039649794529095371)
            ·
              refine ⟨1788253559474691793643057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192169039649794529095371 1788253559474691793643057)
              ·
                refine ⟨1341190169606018845232293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788253559474691793643057 1341190169606018845232293)
                ·
                  refine ⟨251473156801128533481055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341190169606018845232293 251473156801128533481055)
                  ·
                    rfl

theorem cell20_550960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_550960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550960 prefixEnd_550960 := by exact prefixLift 550960
  have htrace : WordTrace (prefixWord ++ tailWord_550960) baseStart_550960 baseEnd_550960 := by
    simpa [prefixWord, tailWord_550960, baseEnd_550960] using wordTrace_append hprefix tailTrace_550960
  have hstable : (prefixWord ++ tailWord_550960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550960).length < 2 ^ (prefixWord ++ tailWord_550960).sum := by decide
  have hdescent : baseEnd_550960 < baseStart_550960 := by decide
  rcases family_descends (prefixWord ++ tailWord_550960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550981 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_550981 : Nat := 118140960795 + 550981 * 2 ^ 59
def prefixEnd_550981 : Nat := 4983230072969 + 3 ^ 40 * 550981 * 2
def baseEnd_550981 : Nat := 251482741773345793780969

theorem tailTrace_550981 : CollatzResearch.WordTrace tailWord_550981 prefixEnd_550981 251482741773345793780969 := by
  unfold tailWord_550981
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095928016897411908220797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13397285344598274605480531 20095928016897411908220797)
  ·
    refine ⟨7535973006336529465582799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20095928016897411908220797 7535973006336529465582799)
    ·
      refine ⟨11303959509504794198374199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7535973006336529465582799 11303959509504794198374199)
      ·
        refine ⟨16955939264257191297561299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11303959509504794198374199 16955939264257191297561299)
        ·
          refine ⟨25433908896385786946341949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16955939264257191297561299 25433908896385786946341949)
          ·
            refine ⟨9537715836144670104878231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25433908896385786946341949 9537715836144670104878231)
            ·
              refine ⟨14306573754217005157317347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537715836144670104878231 14306573754217005157317347)
              ·
                refine ⟨21459860631325507735976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306573754217005157317347 21459860631325507735976021)
                ·
                  refine ⟨251482741773345793780969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21459860631325507735976021 251482741773345793780969)
                  ·
                    rfl

theorem cell20_550981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_550981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_550981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_550981 prefixEnd_550981 := by exact prefixLift 550981
  have htrace : WordTrace (prefixWord ++ tailWord_550981) baseStart_550981 baseEnd_550981 := by
    simpa [prefixWord, tailWord_550981, baseEnd_550981] using wordTrace_append hprefix tailTrace_550981
  have hstable : (prefixWord ++ tailWord_550981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550981).length < 2 ^ (prefixWord ++ tailWord_550981).sum := by decide
  have hdescent : baseEnd_550981 < baseStart_550981 := by decide
  rcases family_descends (prefixWord ++ tailWord_550981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551008 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_551008 : Nat := 118140960795 + 551008 * 2 ^ 59
def prefixEnd_551008 : Nat := 4983230072969 + 3 ^ 40 * 551008 * 2
def baseEnd_551008 : Nat := 251495065309053699880859

theorem tailTrace_551008 : CollatzResearch.WordTrace tailWord_551008 prefixEnd_551008 251495065309053699880859 := by
  unfold tailWord_551008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048456393899797759726839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13397941858533063679635785 10048456393899797759726839)
  ·
    refine ⟨15072684590849696639590259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048456393899797759726839 15072684590849696639590259)
    ·
      refine ⟨22609026886274544959385389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15072684590849696639590259 22609026886274544959385389)
      ·
        refine ⟨8478385082352954359769521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22609026886274544959385389 8478385082352954359769521)
        ·
          refine ⟨6358788811764715769827141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8478385082352954359769521 6358788811764715769827141)
          ·
            refine ⟨1192272902205884206842589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6358788811764715769827141 1192272902205884206842589)
            ·
              refine ⟨447102338327206577565971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192272902205884206842589 447102338327206577565971)
              ·
                refine ⟨670653507490809866348957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447102338327206577565971 670653507490809866348957)
                ·
                  refine ⟨251495065309053699880859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670653507490809866348957 251495065309053699880859)
                  ·
                    rfl

theorem cell20_551008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_551008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551008 prefixEnd_551008 := by exact prefixLift 551008
  have htrace : WordTrace (prefixWord ++ tailWord_551008) baseStart_551008 baseEnd_551008 := by
    simpa [prefixWord, tailWord_551008, baseEnd_551008] using wordTrace_append hprefix tailTrace_551008
  have hstable : (prefixWord ++ tailWord_551008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551008).length < 2 ^ (prefixWord ++ tailWord_551008).sum := by decide
  have hdescent : baseEnd_551008 < baseStart_551008 := by decide
  rcases family_descends (prefixWord ++ tailWord_551008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551018 : List Nat := [3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_551018 : Nat := 118140960795 + 551018 * 2 ^ 59
def prefixEnd_551018 : Nat := 4983230072969 + 3 ^ 40 * 551018 * 2
def baseEnd_551018 : Nat := 83833209860512703182495

theorem tailTrace_551018 : CollatzResearch.WordTrace tailWord_551018 prefixEnd_551018 83833209860512703182495 := by
  unfold tailWord_551018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024319379440841806829427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13398185011842244818211805 5024319379440841806829427)
  ·
    refine ⟨7536479069161262710244141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5024319379440841806829427 7536479069161262710244141)
    ·
      refine ⟨2826179650935473516341553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7536479069161262710244141 2826179650935473516341553)
      ·
        refine ⟨2119634738201605137256165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2826179650935473516341553 2119634738201605137256165)
        ·
          refine ⟨397431513412800963235531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2119634738201605137256165 397431513412800963235531)
          ·
            refine ⟨596147270119201444853297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397431513412800963235531 596147270119201444853297)
            ·
              refine ⟨447110452589401083639973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596147270119201444853297 447110452589401083639973)
              ·
                refine ⟨83833209860512703182495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447110452589401083639973 83833209860512703182495)
                ·
                  rfl

theorem cell20_551018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_551018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551018 prefixEnd_551018 := by exact prefixLift 551018
  have htrace : WordTrace (prefixWord ++ tailWord_551018) baseStart_551018 baseEnd_551018 := by
    simpa [prefixWord, tailWord_551018, baseEnd_551018] using wordTrace_append hprefix tailTrace_551018
  have hstable : (prefixWord ++ tailWord_551018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551018).length < 2 ^ (prefixWord ++ tailWord_551018).sum := by decide
  have hdescent : baseEnd_551018 < baseStart_551018 := by decide
  rcases family_descends (prefixWord ++ tailWord_551018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551043 : List Nat := [1, 1, 1, 3, 3, 5, 6]
def baseStart_551043 : Nat := 118140960795 + 551043 * 2 ^ 59
def prefixEnd_551043 : Nat := 4983230072969 + 3 ^ 40 * 551043 * 2
def baseEnd_551043 : Nat := 27945671140305459301561

theorem tailTrace_551043 : CollatzResearch.WordTrace tailWord_551043 prefixEnd_551043 27945671140305459301561 := by
  unfold tailWord_551043
  simp only [CollatzResearch.WordTrace]
  refine ⟨20098189342672796496977783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13398792895115197664651855 20098189342672796496977783)
  ·
    refine ⟨30147284014009194745466675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20098189342672796496977783 30147284014009194745466675)
    ·
      refine ⟨45220926021013792118200013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30147284014009194745466675 45220926021013792118200013)
      ·
        refine ⟨16957847257880172044325005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45220926021013792118200013 16957847257880172044325005)
        ·
          refine ⟨6359192721705064516621877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16957847257880172044325005 6359192721705064516621877)
          ·
            refine ⟨596174317659849798433301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6359192721705064516621877 596174317659849798433301)
            ·
              refine ⟨27945671140305459301561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 596174317659849798433301 27945671140305459301561)
              ·
                rfl

theorem cell20_551043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_551043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551043 prefixEnd_551043 := by exact prefixLift 551043
  have htrace : WordTrace (prefixWord ++ tailWord_551043) baseStart_551043 baseEnd_551043 := by
    simpa [prefixWord, tailWord_551043, baseEnd_551043] using wordTrace_append hprefix tailTrace_551043
  have hstable : (prefixWord ++ tailWord_551043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551043).length < 2 ^ (prefixWord ++ tailWord_551043).sum := by decide
  have hdescent : baseEnd_551043 < baseStart_551043 := by decide
  rcases family_descends (prefixWord ++ tailWord_551043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551063 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_551063 : Nat := 118140960795 + 551063 * 2 ^ 59
def prefixEnd_551063 : Nat := 4983230072969 + 3 ^ 40 * 551063 * 2
def baseEnd_551063 : Nat := 251520168807717953047301

theorem tailTrace_551063 : CollatzResearch.WordTrace tailWord_551063 prefixEnd_551063 251520168807717953047301 := by
  unfold tailWord_551063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20098918802600339912705843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13399279201733559941803895 20098918802600339912705843)
  ·
    refine ⟨30148378203900509869058765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20098918802600339912705843 30148378203900509869058765)
    ·
      refine ⟨11305641826462691200897037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30148378203900509869058765 11305641826462691200897037)
      ·
        refine ⟨4239615684923509200336389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11305641826462691200897037 4239615684923509200336389)
        ·
          refine ⟨794927940923157975063073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4239615684923509200336389 794927940923157975063073)
          ·
            refine ⟨596195955692368481297305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794927940923157975063073 596195955692368481297305)
            ·
              refine ⟨447146966769276360972979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596195955692368481297305 447146966769276360972979)
              ·
                refine ⟨670720450153914541459469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447146966769276360972979 670720450153914541459469)
                ·
                  refine ⟨251520168807717953047301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670720450153914541459469 251520168807717953047301)
                  ·
                    rfl

theorem cell20_551063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_551063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551063 prefixEnd_551063 := by exact prefixLift 551063
  have htrace : WordTrace (prefixWord ++ tailWord_551063) baseStart_551063 baseEnd_551063 := by
    simpa [prefixWord, tailWord_551063, baseEnd_551063] using wordTrace_append hprefix tailTrace_551063
  have hstable : (prefixWord ++ tailWord_551063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551063).length < 2 ^ (prefixWord ++ tailWord_551063).sum := by decide
  have hdescent : baseEnd_551063 < baseStart_551063 := by decide
  rcases family_descends (prefixWord ++ tailWord_551063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551108 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_551108 : Nat := 118140960795 + 551108 * 2 ^ 59
def prefixEnd_551108 : Nat := 4983230072969 + 3 ^ 40 * 551108 * 2
def baseEnd_551108 : Nat := 251540708033897796547117

theorem tailTrace_551108 : CollatzResearch.WordTrace tailWord_551108 prefixEnd_551108 251540708033897796547117 := by
  unfold tailWord_551108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050280043718656299046989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13400373391624875065395985 10050280043718656299046989)
  ·
    refine ⟨3768855016394496112142621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10050280043718656299046989 3768855016394496112142621)
    ·
      refine ⟨1413320631147936042053483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3768855016394496112142621 1413320631147936042053483)
      ·
        refine ⟨2119980946721904063080225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413320631147936042053483 2119980946721904063080225)
        ·
          refine ⟨1589985710041428047310169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119980946721904063080225 1589985710041428047310169)
          ·
            refine ⟨1192489282531071035482627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589985710041428047310169 1192489282531071035482627)
            ·
              refine ⟨1788733923796606553223941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192489282531071035482627 1788733923796606553223941)
              ·
                refine ⟨335387610711863728729489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1788733923796606553223941 335387610711863728729489)
                ·
                  refine ⟨251540708033897796547117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335387610711863728729489 251540708033897796547117)
                  ·
                    rfl

theorem cell20_551108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_551108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551108 prefixEnd_551108 := by exact prefixLift 551108
  have htrace : WordTrace (prefixWord ++ tailWord_551108) baseStart_551108 baseEnd_551108 := by
    simpa [prefixWord, tailWord_551108, baseEnd_551108] using wordTrace_append hprefix tailTrace_551108
  have hstable : (prefixWord ++ tailWord_551108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551108).length < 2 ^ (prefixWord ++ tailWord_551108).sum := by decide
  have hdescent : baseEnd_551108 < baseStart_551108 := by decide
  rcases family_descends (prefixWord ++ tailWord_551108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551132 : List Nat := [2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_551132 : Nat := 118140960795 + 551132 * 2 ^ 59
def prefixEnd_551132 : Nat := 4983230072969 + 3 ^ 40 * 551132 * 2
def baseEnd_551132 : Nat := 83850554095953459915673

theorem tailTrace_551132 : CollatzResearch.WordTrace tailWord_551132 prefixEnd_551132 83850554095953459915673 := by
  unfold tailWord_551132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050717719675182348483825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13400956959566909797978433 10050717719675182348483825)
  ·
    refine ⟨7538038289756386761362869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10050717719675182348483825 7538038289756386761362869)
    ·
      refine ⟨706691089664661258877769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7538038289756386761362869 706691089664661258877769)
      ·
        refine ⟨530018317248495944158327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706691089664661258877769 530018317248495944158327)
        ·
          refine ⟨795027475872743916237491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530018317248495944158327 795027475872743916237491)
          ·
            refine ⟨1192541213809115874356237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795027475872743916237491 1192541213809115874356237)
            ·
              refine ⟨447202955178418452883589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192541213809115874356237 447202955178418452883589)
              ·
                refine ⟨83850554095953459915673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447202955178418452883589 83850554095953459915673)
                ·
                  rfl

theorem cell20_551132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_551132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551132 prefixEnd_551132 := by exact prefixLift 551132
  have htrace : WordTrace (prefixWord ++ tailWord_551132) baseStart_551132 baseEnd_551132 := by
    simpa [prefixWord, tailWord_551132, baseEnd_551132] using wordTrace_append hprefix tailTrace_551132
  have hstable : (prefixWord ++ tailWord_551132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551132).length < 2 ^ (prefixWord ++ tailWord_551132).sum := by decide
  have hdescent : baseEnd_551132 < baseStart_551132 := by decide
  rcases family_descends (prefixWord ++ tailWord_551132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551195 : List Nat := [1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_551195 : Nat := 118140960795 + 551195 * 2 ^ 59
def prefixEnd_551195 : Nat := 4983230072969 + 3 ^ 40 * 551195 * 2
def baseEnd_551195 : Nat := 83860139068170720215587

theorem tailTrace_551195 : CollatzResearch.WordTrace tailWord_551195 prefixEnd_551195 83860139068170720215587 := by
  unfold tailWord_551195
  simp only [CollatzResearch.WordTrace]
  refine ⟨20103733238122126456511039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13402488825414750971007359 20103733238122126456511039)
  ·
    refine ⟨30155599857183189684766559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20103733238122126456511039 30155599857183189684766559)
    ·
      refine ⟨45233399785774784527149839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30155599857183189684766559 45233399785774784527149839)
      ·
        refine ⟨67850099678662176790724759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45233399785774784527149839 67850099678662176790724759)
        ·
          refine ⟨101775149517993265186087139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67850099678662176790724759 101775149517993265186087139)
          ·
            refine ⟨152662724276989897779130709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101775149517993265186087139 152662724276989897779130709)
            ·
              refine ⟨447254075030243841149797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 152662724276989897779130709 447254075030243841149797)
              ·
                refine ⟨83860139068170720215587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447254075030243841149797 83860139068170720215587)
                ·
                  rfl

theorem cell20_551195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_551195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551195 prefixEnd_551195 := by exact prefixLift 551195
  have htrace : WordTrace (prefixWord ++ tailWord_551195) baseStart_551195 baseEnd_551195 := by
    simpa [prefixWord, tailWord_551195, baseEnd_551195] using wordTrace_append hprefix tailTrace_551195
  have hstable : (prefixWord ++ tailWord_551195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551195).length < 2 ^ (prefixWord ++ tailWord_551195).sum := by decide
  have hdescent : baseEnd_551195 < baseStart_551195 := by decide
  rcases family_descends (prefixWord ++ tailWord_551195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551198 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_551198 : Nat := 118140960795 + 551198 * 2 ^ 59
def prefixEnd_551198 : Nat := 4983230072969 + 3 ^ 40 * 551198 * 2
def baseEnd_551198 : Nat := 251581786486257483546749

theorem tailTrace_551198 : CollatzResearch.WordTrace tailWord_551198 prefixEnd_551198 251581786486257483546749 := by
  unfold tailWord_551198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512980332138907246108781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13402561771407505312580165 2512980332138907246108781)
  ·
    refine ⟨942367624552090217290793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2512980332138907246108781 942367624552090217290793)
    ·
      refine ⟨706775718414067662968095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 942367624552090217290793 706775718414067662968095)
      ·
        refine ⟨1060163577621101494452143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706775718414067662968095 1060163577621101494452143)
        ·
          refine ⟨1590245366431652241678215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060163577621101494452143 1590245366431652241678215)
          ·
            refine ⟨2385368049647478362517323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590245366431652241678215 2385368049647478362517323)
            ·
              refine ⟨3578052074471217543775985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385368049647478362517323 3578052074471217543775985)
              ·
                refine ⟨2683539055853413157831989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3578052074471217543775985 2683539055853413157831989)
                ·
                  refine ⟨251581786486257483546749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2683539055853413157831989 251581786486257483546749)
                  ·
                    rfl

theorem cell20_551198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_551198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551198 prefixEnd_551198 := by exact prefixLift 551198
  have htrace : WordTrace (prefixWord ++ tailWord_551198) baseStart_551198 baseEnd_551198 := by
    simpa [prefixWord, tailWord_551198, baseEnd_551198] using wordTrace_append hprefix tailTrace_551198
  have hstable : (prefixWord ++ tailWord_551198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551198).length < 2 ^ (prefixWord ++ tailWord_551198).sum := by decide
  have hdescent : baseEnd_551198 < baseStart_551198 := by decide
  rcases family_descends (prefixWord ++ tailWord_551198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551226 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_551226 : Nat := 118140960795 + 551226 * 2 ^ 59
def prefixEnd_551226 : Nat := 4983230072969 + 3 ^ 40 * 551226 * 2
def baseEnd_551226 : Nat := 251594566449213830613301

theorem tailTrace_551226 : CollatzResearch.WordTrace tailWord_551226 prefixEnd_551226 251594566449213830613301 := by
  unfold tailWord_551226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026215975252454687722383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13403242600673212500593021 5026215975252454687722383)
  ·
    refine ⟨7539323962878682031583575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5026215975252454687722383 7539323962878682031583575)
    ·
      refine ⟨11308985944318023047375363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7539323962878682031583575 11308985944318023047375363)
      ·
        refine ⟨16963478916477034571063045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308985944318023047375363 16963478916477034571063045)
        ·
          refine ⟨3180652296839443982074321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16963478916477034571063045 3180652296839443982074321)
          ·
            refine ⟨2385489222629582986555741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180652296839443982074321 2385489222629582986555741)
            ·
              refine ⟨894558458486093619958403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2385489222629582986555741 894558458486093619958403)
              ·
                refine ⟨1341837687729140429937605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894558458486093619958403 1341837687729140429937605)
                ·
                  refine ⟨251594566449213830613301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341837687729140429937605 251594566449213830613301)
                  ·
                    rfl

theorem cell20_551226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_551226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551226 prefixEnd_551226 := by exact prefixLift 551226
  have htrace : WordTrace (prefixWord ++ tailWord_551226) baseStart_551226 baseEnd_551226 := by
    simpa [prefixWord, tailWord_551226, baseEnd_551226] using wordTrace_append hprefix tailTrace_551226
  have hstable : (prefixWord ++ tailWord_551226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551226).length < 2 ^ (prefixWord ++ tailWord_551226).sum := by decide
  have hdescent : baseEnd_551226 < baseStart_551226 := by decide
  rcases family_descends (prefixWord ++ tailWord_551226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551274 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_551274 : Nat := 118140960795 + 551274 * 2 ^ 59
def prefixEnd_551274 : Nat := 4983230072969 + 3 ^ 40 * 551274 * 2
def baseEnd_551274 : Nat := 251616474957138997013105

theorem tailTrace_551274 : CollatzResearch.WordTrace tailWord_551274 prefixEnd_551274 251616474957138997013105 := by
  unfold tailWord_551274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026653651208980737159219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13404409736557281965757917 5026653651208980737159219)
  ·
    refine ⟨7539980476813471105738829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5026653651208980737159219 7539980476813471105738829)
    ·
      refine ⟨2827492678805051664652061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7539980476813471105738829 2827492678805051664652061)
      ·
        refine ⟨1060309754551894374244523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2827492678805051664652061 1060309754551894374244523)
        ·
          refine ⟨1590464631827841561366785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060309754551894374244523 1590464631827841561366785)
          ·
            refine ⟨1192848473870881171025089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590464631827841561366785 1192848473870881171025089)
            ·
              refine ⟨894636355403160878268817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192848473870881171025089 894636355403160878268817)
              ·
                refine ⟨670977266552370658701613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894636355403160878268817 670977266552370658701613)
                ·
                  refine ⟨251616474957138997013105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670977266552370658701613 251616474957138997013105)
                  ·
                    rfl

theorem cell20_551274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_551274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551274 prefixEnd_551274 := by exact prefixLift 551274
  have htrace : WordTrace (prefixWord ++ tailWord_551274) baseStart_551274 baseEnd_551274 := by
    simpa [prefixWord, tailWord_551274, baseEnd_551274] using wordTrace_append hprefix tailTrace_551274
  have hstable : (prefixWord ++ tailWord_551274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551274).length < 2 ^ (prefixWord ++ tailWord_551274).sum := by decide
  have hdescent : baseEnd_551274 < baseStart_551274 := by decide
  rcases family_descends (prefixWord ++ tailWord_551274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551292 : List Nat := [2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_551292 : Nat := 118140960795 + 551292 * 2 ^ 59
def prefixEnd_551292 : Nat := 4983230072969 + 3 ^ 40 * 551292 * 2
def baseEnd_551292 : Nat := 83874896882536978137677

theorem tailTrace_551292 : CollatzResearch.WordTrace tailWord_551292 prefixEnd_551292 83874896882536978137677 := by
  unfold tailWord_551292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10053635559385356011396065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13404847412513808015194753 10053635559385356011396065)
  ·
    refine ⟨7540226669539017008547049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10053635559385356011396065 7540226669539017008547049)
    ·
      refine ⟨5655170002154262756410287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7540226669539017008547049 5655170002154262756410287)
      ·
        refine ⟨8482755003231394134615431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5655170002154262756410287 8482755003231394134615431)
        ·
          refine ⟨12724132504847091201923147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482755003231394134615431 12724132504847091201923147)
          ·
            refine ⟨19086198757270636802884721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12724132504847091201923147 19086198757270636802884721)
            ·
              refine ⟨14314649067952977602163541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19086198757270636802884721 14314649067952977602163541)
              ·
                refine ⟨83874896882536978137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14314649067952977602163541 83874896882536978137677)
                ·
                  rfl

theorem cell20_551292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_551292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551292 prefixEnd_551292 := by exact prefixLift 551292
  have htrace : WordTrace (prefixWord ++ tailWord_551292) baseStart_551292 baseEnd_551292 := by
    simpa [prefixWord, tailWord_551292, baseEnd_551292] using wordTrace_append hprefix tailTrace_551292
  have hstable : (prefixWord ++ tailWord_551292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551292).length < 2 ^ (prefixWord ++ tailWord_551292).sum := by decide
  have hdescent : baseEnd_551292 < baseStart_551292 := by decide
  rcases family_descends (prefixWord ++ tailWord_551292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551298 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_551298 : Nat := 118140960795 + 551298 * 2 ^ 59
def prefixEnd_551298 : Nat := 4983230072969 + 3 ^ 40 * 551298 * 2
def baseEnd_551298 : Nat := 251627429211101580213007

theorem tailTrace_551298 : CollatzResearch.WordTrace tailWord_551298 prefixEnd_551298 251627429211101580213007 := by
  unfold tailWord_551298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026872489187243761877637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13404993304499316698340365 5026872489187243761877637)
  ·
    refine ⟨942538591722608205352057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5026872489187243761877637 942538591722608205352057)
    ·
      refine ⟨706903943791956154014043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 942538591722608205352057 706903943791956154014043)
      ·
        refine ⟨1060355915687934231021065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706903943791956154014043 1060355915687934231021065)
        ·
          refine ⟨795266936765950673265799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060355915687934231021065 795266936765950673265799)
          ·
            refine ⟨1192900405148926009898699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795266936765950673265799 1192900405148926009898699)
            ·
              refine ⟨1789350607723389014848049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192900405148926009898699 1789350607723389014848049)
              ·
                refine ⟨1342012955792541761136037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789350607723389014848049 1342012955792541761136037)
                ·
                  refine ⟨251627429211101580213007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342012955792541761136037 251627429211101580213007)
                  ·
                    rfl

theorem cell20_551298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_551298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551298 prefixEnd_551298 := by exact prefixLift 551298
  have htrace : WordTrace (prefixWord ++ tailWord_551298) baseStart_551298 baseEnd_551298 := by
    simpa [prefixWord, tailWord_551298, baseEnd_551298] using wordTrace_append hprefix tailTrace_551298
  have hstable : (prefixWord ++ tailWord_551298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551298).length < 2 ^ (prefixWord ++ tailWord_551298).sum := by decide
  have hdescent : baseEnd_551298 < baseStart_551298 := by decide
  rcases family_descends (prefixWord ++ tailWord_551298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551326 : List Nat := [4, 3, 1, 2, 1, 2, 7]
def baseStart_551326 : Nat := 118140960795 + 551326 * 2 ^ 59
def prefixEnd_551326 : Nat := 4983230072969 + 3 ^ 40 * 551326 * 2
def baseEnd_551326 : Nat := 27960023241561991919951

theorem tailTrace_551326 : CollatzResearch.WordTrace tailWord_551326 prefixEnd_551326 27960023241561991919951 := by
  unfold tailWord_551326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513563900080941978691229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13405674133765023886353221 2513563900080941978691229)
  ·
    refine ⟨942586462530353242009211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2513563900080941978691229 942586462530353242009211)
    ·
      refine ⟨1413879693795529863013817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942586462530353242009211 1413879693795529863013817)
      ·
        refine ⟨1060409770346647397260363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413879693795529863013817 1060409770346647397260363)
        ·
          refine ⟨1590614655519971095890545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060409770346647397260363 1590614655519971095890545)
          ·
            refine ⟨1192960991639978321917909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590614655519971095890545 1192960991639978321917909)
            ·
              refine ⟨27960023241561991919951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1192960991639978321917909 27960023241561991919951)
              ·
                rfl

theorem cell20_551326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_551326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551326 prefixEnd_551326 := by exact prefixLift 551326
  have htrace : WordTrace (prefixWord ++ tailWord_551326) baseStart_551326 baseEnd_551326 := by
    simpa [prefixWord, tailWord_551326, baseEnd_551326] using wordTrace_append hprefix tailTrace_551326
  have hstable : (prefixWord ++ tailWord_551326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551326).length < 2 ^ (prefixWord ++ tailWord_551326).sum := by decide
  have hdescent : baseEnd_551326 < baseStart_551326 := by decide
  rcases family_descends (prefixWord ++ tailWord_551326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551329 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_551329 : Nat := 118140960795 + 551329 * 2 ^ 59
def prefixEnd_551329 : Nat := 4983230072969 + 3 ^ 40 * 551329 * 2
def baseEnd_551329 : Nat := 251641578455803250179547

theorem tailTrace_551329 : CollatzResearch.WordTrace tailWord_551329 prefixEnd_551329 251641578455803250179547 := by
  unfold tailWord_551329
  simp only [CollatzResearch.WordTrace]
  refine ⟨20108620619636667341889041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13405747079757778227926027 20108620619636667341889041)
  ·
    refine ⟨15081465464727500506416781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20108620619636667341889041 15081465464727500506416781)
    ·
      refine ⟨5655549549272812689906293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15081465464727500506416781 5655549549272812689906293)
      ·
        refine ⟨530207770244326189678715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5655549549272812689906293 530207770244326189678715)
        ·
          refine ⟨795311655366489284518073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530207770244326189678715 795311655366489284518073)
          ·
            refine ⟨596483741524866963388555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795311655366489284518073 596483741524866963388555)
            ·
              refine ⟨894725612287300445082833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596483741524866963388555 894725612287300445082833)
              ·
                refine ⟨671044209215475333812125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894725612287300445082833 671044209215475333812125)
                ·
                  refine ⟨251641578455803250179547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671044209215475333812125 251641578455803250179547)
                  ·
                    rfl

theorem cell20_551329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_551329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551329 prefixEnd_551329 := by exact prefixLift 551329
  have htrace : WordTrace (prefixWord ++ tailWord_551329) baseStart_551329 baseEnd_551329 := by
    simpa [prefixWord, tailWord_551329, baseEnd_551329] using wordTrace_append hprefix tailTrace_551329
  have hstable : (prefixWord ++ tailWord_551329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551329).length < 2 ^ (prefixWord ++ tailWord_551329).sum := by decide
  have hdescent : baseEnd_551329 < baseStart_551329 := by decide
  rcases family_descends (prefixWord ++ tailWord_551329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551336 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_551336 : Nat := 118140960795 + 551336 * 2 ^ 59
def prefixEnd_551336 : Nat := 4983230072969 + 3 ^ 40 * 551336 * 2
def baseEnd_551336 : Nat := 251644773446542336946185

theorem tailTrace_551336 : CollatzResearch.WordTrace tailWord_551336 prefixEnd_551336 251644773446542336946185 := by
  unfold tailWord_551336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10054437965305653768696931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13405917287074205024929241 10054437965305653768696931)
  ·
    refine ⟨15081656947958480653045397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10054437965305653768696931 15081656947958480653045397)
    ·
      refine ⟨706952669435553780611503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15081656947958480653045397 706952669435553780611503)
      ·
        refine ⟨1060429004153330670917255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706952669435553780611503 1060429004153330670917255)
        ·
          refine ⟨1590643506229996006375883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060429004153330670917255 1590643506229996006375883)
          ·
            refine ⟨2385965259344994009563825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590643506229996006375883 2385965259344994009563825)
            ·
              refine ⟨1789473944508745507172869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385965259344994009563825 1789473944508745507172869)
              ·
                refine ⟨335526364595389782594913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1789473944508745507172869 335526364595389782594913)
                ·
                  refine ⟨251644773446542336946185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335526364595389782594913 251644773446542336946185)
                  ·
                    rfl

theorem cell20_551336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_551336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551336 prefixEnd_551336 := by exact prefixLift 551336
  have htrace : WordTrace (prefixWord ++ tailWord_551336) baseStart_551336 baseEnd_551336 := by
    simpa [prefixWord, tailWord_551336, baseEnd_551336] using wordTrace_append hprefix tailTrace_551336
  have hstable : (prefixWord ++ tailWord_551336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551336).length < 2 ^ (prefixWord ++ tailWord_551336).sum := by decide
  have hdescent : baseEnd_551336 < baseStart_551336 := by decide
  rcases family_descends (prefixWord ++ tailWord_551336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551354 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_551354 : Nat := 118140960795 + 551354 * 2 ^ 59
def prefixEnd_551354 : Nat := 4983230072969 + 3 ^ 40 * 551354 * 2
def baseEnd_551354 : Nat := 251652989137014274346111

theorem tailTrace_551354 : CollatzResearch.WordTrace tailWord_551354 prefixEnd_551354 251652989137014274346111 := by
  unfold tailWord_551354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5027383111136524152887279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13406354963030731074366077 5027383111136524152887279)
  ·
    refine ⟨7541074666704786229330919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5027383111136524152887279 7541074666704786229330919)
    ·
      refine ⟨11311612000057179343996379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541074666704786229330919 11311612000057179343996379)
      ·
        refine ⟨16967418000085769015994569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11311612000057179343996379 16967418000085769015994569)
        ·
          refine ⟨12725563500064326761995927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16967418000085769015994569 12725563500064326761995927)
          ·
            refine ⟨19088345250096490142993891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12725563500064326761995927 19088345250096490142993891)
            ·
              refine ⟨28632517875144735214490837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19088345250096490142993891 28632517875144735214490837)
              ·
                refine ⟨671074637698704731589629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28632517875144735214490837 671074637698704731589629)
                ·
                  refine ⟨251652989137014274346111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671074637698704731589629 251652989137014274346111)
                  ·
                    rfl

theorem cell20_551354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_551354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551354 prefixEnd_551354 := by exact prefixLift 551354
  have htrace : WordTrace (prefixWord ++ tailWord_551354) baseStart_551354 baseEnd_551354 := by
    simpa [prefixWord, tailWord_551354, baseEnd_551354] using wordTrace_append hprefix tailTrace_551354
  have hstable : (prefixWord ++ tailWord_551354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551354).length < 2 ^ (prefixWord ++ tailWord_551354).sum := by decide
  have hdescent : baseEnd_551354 < baseStart_551354 := by decide
  rcases family_descends (prefixWord ++ tailWord_551354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551364 : List Nat := [2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_551364 : Nat := 118140960795 + 551364 * 2 ^ 59
def prefixEnd_551364 : Nat := 4983230072969 + 3 ^ 40 * 551364 * 2
def baseEnd_551364 : Nat := 83885851136499561337579

theorem tailTrace_551364 : CollatzResearch.WordTrace tailWord_551364 prefixEnd_551364 83885851136499561337579 := by
  unfold tailWord_551364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10054948587254934159706573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13406598116339912212942097 10054948587254934159706573)
  ·
    refine ⟨3770605720220600309889965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10054948587254934159706573 3770605720220600309889965)
    ·
      refine ⟨1413977145082725116208737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3770605720220600309889965 1413977145082725116208737)
      ·
        refine ⟨1060482858812043837156553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413977145082725116208737 1060482858812043837156553)
        ·
          refine ⟨795362144109032877867415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060482858812043837156553 795362144109032877867415)
          ·
            refine ⟨1193043216163549316801123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795362144109032877867415 1193043216163549316801123)
            ·
              refine ⟨1789564824245323975201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193043216163549316801123 1789564824245323975201685)
              ·
                refine ⟨83885851136499561337579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1789564824245323975201685 83885851136499561337579)
                ·
                  rfl

theorem cell20_551364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_551364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551364 prefixEnd_551364 := by exact prefixLift 551364
  have htrace : WordTrace (prefixWord ++ tailWord_551364) baseStart_551364 baseEnd_551364 := by
    simpa [prefixWord, tailWord_551364, baseEnd_551364] using wordTrace_append hprefix tailTrace_551364
  have hstable : (prefixWord ++ tailWord_551364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551364).length < 2 ^ (prefixWord ++ tailWord_551364).sum := by decide
  have hdescent : baseEnd_551364 < baseStart_551364 := by decide
  rcases family_descends (prefixWord ++ tailWord_551364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551392 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_551392 : Nat := 118140960795 + 551392 * 2 ^ 59
def prefixEnd_551392 : Nat := 4983230072969 + 3 ^ 40 * 551392 * 2
def baseEnd_551392 : Nat := 251670333372455031079289

theorem tailTrace_551392 : CollatzResearch.WordTrace tailWord_551392 prefixEnd_551392 251670333372455031079289 := by
  unfold tailWord_551392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055459209204214550716215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13407278945605619400954953 10055459209204214550716215)
  ·
    refine ⟨15083188813806321826074323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055459209204214550716215 15083188813806321826074323)
    ·
      refine ⟨22624783220709482739111485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15083188813806321826074323 22624783220709482739111485)
      ·
        refine ⟨8484293707766056027166807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22624783220709482739111485 8484293707766056027166807)
        ·
          refine ⟨12726440561649084040750211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8484293707766056027166807 12726440561649084040750211)
          ·
            refine ⟨19089660842473626061125317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12726440561649084040750211 19089660842473626061125317)
            ·
              refine ⟨3579311407963804886460997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19089660842473626061125317 3579311407963804886460997)
              ·
                refine ⟨671120888993213416211437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3579311407963804886460997 671120888993213416211437)
                ·
                  refine ⟨251670333372455031079289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671120888993213416211437 251670333372455031079289)
                  ·
                    rfl

theorem cell20_551392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_551392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551392 prefixEnd_551392 := by exact prefixLift 551392
  have htrace : WordTrace (prefixWord ++ tailWord_551392) baseStart_551392 baseEnd_551392 := by
    simpa [prefixWord, tailWord_551392, baseEnd_551392] using wordTrace_append hprefix tailTrace_551392
  have hstable : (prefixWord ++ tailWord_551392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551392).length < 2 ^ (prefixWord ++ tailWord_551392).sum := by decide
  have hdescent : baseEnd_551392 < baseStart_551392 := by decide
  rcases family_descends (prefixWord ++ tailWord_551392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551395 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_551395 : Nat := 118140960795 + 551395 * 2 ^ 59
def prefixEnd_551395 : Nat := 4983230072969 + 3 ^ 40 * 551395 * 2
def baseEnd_551395 : Nat := 251671702654200353979277

theorem tailTrace_551395 : CollatzResearch.WordTrace tailWord_551395 prefixEnd_551395 251671702654200353979277 := by
  unfold tailWord_551395
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111027837397560613791639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407351891598373742527759 20111027837397560613791639)
  ·
    refine ⟨30166541756096340920687459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20111027837397560613791639 30166541756096340920687459)
    ·
      refine ⟨45249812634144511381031189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30166541756096340920687459 45249812634144511381031189)
      ·
        refine ⟨2121084967225523970985837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45249812634144511381031189 2121084967225523970985837)
        ·
          refine ⟨795406862709571489119689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2121084967225523970985837 795406862709571489119689)
          ·
            refine ⟨596555147032178616839767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795406862709571489119689 596555147032178616839767)
            ·
              refine ⟨894832720548267925259651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596555147032178616839767 894832720548267925259651)
              ·
                refine ⟨1342249080822401887889477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894832720548267925259651 1342249080822401887889477)
                ·
                  refine ⟨251671702654200353979277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342249080822401887889477 251671702654200353979277)
                  ·
                    rfl

theorem cell20_551395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_551395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551395 prefixEnd_551395 := by exact prefixLift 551395
  have htrace : WordTrace (prefixWord ++ tailWord_551395) baseStart_551395 baseEnd_551395 := by
    simpa [prefixWord, tailWord_551395, baseEnd_551395] using wordTrace_append hprefix tailTrace_551395
  have hstable : (prefixWord ++ tailWord_551395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551395).length < 2 ^ (prefixWord ++ tailWord_551395).sum := by decide
  have hdescent : baseEnd_551395 < baseStart_551395 := by decide
  rcases family_descends (prefixWord ++ tailWord_551395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551405 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_551405 : Nat := 118140960795 + 551405 * 2 ^ 59
def prefixEnd_551405 : Nat := 4983230072969 + 3 ^ 40 * 551405 * 2
def baseEnd_551405 : Nat := 251676266926684763645903

theorem tailTrace_551405 : CollatzResearch.WordTrace tailWord_551405 prefixEnd_551405 251676266926684763645903 := by
  unfold tailWord_551405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111392567361332321655669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407595044907554881103779 20111392567361332321655669)
  ·
    refine ⟨1885443053190124905155219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20111392567361332321655669 1885443053190124905155219)
    ·
      refine ⟨2828164579785187357732829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885443053190124905155219 2828164579785187357732829)
      ·
        refine ⟨1060561717419445259149811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2828164579785187357732829 1060561717419445259149811)
        ·
          refine ⟨1590842576129167888724717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060561717419445259149811 1590842576129167888724717)
          ·
            refine ⟨596565966048437958271769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1590842576129167888724717 596565966048437958271769)
            ·
              refine ⟨447424474536328468703827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596565966048437958271769 447424474536328468703827)
              ·
                refine ⟨671136711804492703055741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447424474536328468703827 671136711804492703055741)
                ·
                  refine ⟨251676266926684763645903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671136711804492703055741 251676266926684763645903)
                  ·
                    rfl

theorem cell20_551405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_551405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551405 prefixEnd_551405 := by exact prefixLift 551405
  have htrace : WordTrace (prefixWord ++ tailWord_551405) baseStart_551405 baseEnd_551405 := by
    simpa [prefixWord, tailWord_551405, baseEnd_551405] using wordTrace_append hprefix tailTrace_551405
  have hstable : (prefixWord ++ tailWord_551405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551405).length < 2 ^ (prefixWord ++ tailWord_551405).sum := by decide
  have hdescent : baseEnd_551405 < baseStart_551405 := by decide
  rcases family_descends (prefixWord ++ tailWord_551405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551475 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_551475 : Nat := 118140960795 + 551475 * 2 ^ 59
def prefixEnd_551475 : Nat := 4983230072969 + 3 ^ 40 * 551475 * 2
def baseEnd_551475 : Nat := 251708216834075631312283

theorem tailTrace_551475 : CollatzResearch.WordTrace tailWord_551475 prefixEnd_551475 251708216834075631312283 := by
  unfold tailWord_551475
  simp only [CollatzResearch.WordTrace]
  refine ⟨20113945677107734276703879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13409297118071822851135919 20113945677107734276703879)
  ·
    refine ⟨30170918515661601415055819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20113945677107734276703879 30170918515661601415055819)
    ·
      refine ⟨45256377773492402122583729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30170918515661601415055819 45256377773492402122583729)
      ·
        refine ⟨33942283330119301591937797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45256377773492402122583729 33942283330119301591937797)
        ·
          refine ⟨6364178124397369048488337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33942283330119301591937797 6364178124397369048488337)
          ·
            refine ⟨4773133593298026786366253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364178124397369048488337 4773133593298026786366253)
            ·
              refine ⟨1789925097486760044887345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4773133593298026786366253 1789925097486760044887345)
              ·
                refine ⟨1342443823115070033665509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789925097486760044887345 1342443823115070033665509)
                ·
                  refine ⟨251708216834075631312283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342443823115070033665509 251708216834075631312283)
                  ·
                    rfl

theorem cell20_551475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_551475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551475 prefixEnd_551475 := by exact prefixLift 551475
  have htrace : WordTrace (prefixWord ++ tailWord_551475) baseStart_551475 baseEnd_551475 := by
    simpa [prefixWord, tailWord_551475, baseEnd_551475] using wordTrace_append hprefix tailTrace_551475
  have hstable : (prefixWord ++ tailWord_551475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551475).length < 2 ^ (prefixWord ++ tailWord_551475).sum := by decide
  have hdescent : baseEnd_551475 < baseStart_551475 := by decide
  rcases family_descends (prefixWord ++ tailWord_551475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551506 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_551506 : Nat := 118140960795 + 551506 * 2 ^ 59
def prefixEnd_551506 : Nat := 4983230072969 + 3 ^ 40 * 551506 * 2
def baseEnd_551506 : Nat := 251722366078777301278823

theorem tailTrace_551506 : CollatzResearch.WordTrace tailWord_551506 prefixEnd_551506 251722366078777301278823 := by
  unfold tailWord_551506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028769084998856642770593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13410050893330284380721581 5028769084998856642770593)
  ·
    refine ⟨3771576813749142482077945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5028769084998856642770593 3771576813749142482077945)
    ·
      refine ⟨2828682610311856861558459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3771576813749142482077945 2828682610311856861558459)
      ·
        refine ⟨4243023915467785292337689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828682610311856861558459 4243023915467785292337689)
        ·
          refine ⟨3182267936600838969253267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4243023915467785292337689 3182267936600838969253267)
          ·
            refine ⟨4773401904901258453879901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182267936600838969253267 4773401904901258453879901)
            ·
              refine ⟨1790025714337971920204963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4773401904901258453879901 1790025714337971920204963)
              ·
                refine ⟨2685038571506957880307445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790025714337971920204963 2685038571506957880307445)
                ·
                  refine ⟨251722366078777301278823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685038571506957880307445 251722366078777301278823)
                  ·
                    rfl

theorem cell20_551506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_551506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551506 prefixEnd_551506 := by exact prefixLift 551506
  have htrace : WordTrace (prefixWord ++ tailWord_551506) baseStart_551506 baseEnd_551506 := by
    simpa [prefixWord, tailWord_551506, baseEnd_551506] using wordTrace_append hprefix tailTrace_551506
  have hstable : (prefixWord ++ tailWord_551506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551506).length < 2 ^ (prefixWord ++ tailWord_551506).sum := by decide
  have hdescent : baseEnd_551506 < baseStart_551506 := by decide
  rcases family_descends (prefixWord ++ tailWord_551506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551523 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_551523 : Nat := 118140960795 + 551523 * 2 ^ 59
def prefixEnd_551523 : Nat := 4983230072969 + 3 ^ 40 * 551523 * 2
def baseEnd_551523 : Nat := 251730125342000797712087

theorem tailTrace_551523 : CollatzResearch.WordTrace tailWord_551523 prefixEnd_551523 251730125342000797712087 := by
  unfold tailWord_551523
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115696380933838474451223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13410464253955892316300815 20115696380933838474451223)
  ·
    refine ⟨30173544571400757711676835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20115696380933838474451223 30173544571400757711676835)
    ·
      refine ⟨45260316857101136567515253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30173544571400757711676835 45260316857101136567515253)
      ·
        refine ⟨4243154705353231553204555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45260316857101136567515253 4243154705353231553204555)
        ·
          refine ⟨6364732058029847329806833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243154705353231553204555 6364732058029847329806833)
          ·
            refine ⟨4773549043522385497355125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364732058029847329806833 4773549043522385497355125)
            ·
              refine ⟨447520222830223640377043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4773549043522385497355125 447520222830223640377043)
              ·
                refine ⟨671280334245335460565565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447520222830223640377043 671280334245335460565565)
                ·
                  refine ⟨251730125342000797712087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671280334245335460565565 251730125342000797712087)
                  ·
                    rfl

theorem cell20_551523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_551523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551523 prefixEnd_551523 := by exact prefixLift 551523
  have htrace : WordTrace (prefixWord ++ tailWord_551523) baseStart_551523 baseEnd_551523 := by
    simpa [prefixWord, tailWord_551523, baseEnd_551523] using wordTrace_append hprefix tailTrace_551523
  have hstable : (prefixWord ++ tailWord_551523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551523).length < 2 ^ (prefixWord ++ tailWord_551523).sum := by decide
  have hdescent : baseEnd_551523 < baseStart_551523 := by decide
  rcases family_descends (prefixWord ++ tailWord_551523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551578 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_551578 : Nat := 118140960795 + 551578 * 2 ^ 59
def prefixEnd_551578 : Nat := 4983230072969 + 3 ^ 40 * 551578 * 2
def baseEnd_551578 : Nat := 251755228840665050878529

theorem tailTrace_551578 : CollatzResearch.WordTrace tailWord_551578 prefixEnd_551578 251755228840665050878529 := by
  unfold tailWord_551578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029425598933645716925847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13411801597156388578468925 5029425598933645716925847)
  ·
    refine ⟨7544138398400468575388771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029425598933645716925847 7544138398400468575388771)
    ·
      refine ⟨11316207597600702863083157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7544138398400468575388771 11316207597600702863083157)
      ·
        refine ⟨530447231137532946707023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11316207597600702863083157 530447231137532946707023)
        ·
          refine ⟨795670846706299420060535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530447231137532946707023 795670846706299420060535)
          ·
            refine ⟨1193506270059449130090803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795670846706299420060535 1193506270059449130090803)
            ·
              refine ⟨1790259405089173695136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193506270059449130090803 1790259405089173695136205)
              ·
                refine ⟨671347276908440135676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790259405089173695136205 671347276908440135676077)
                ·
                  refine ⟨251755228840665050878529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671347276908440135676077 251755228840665050878529)
                  ·
                    rfl

theorem cell20_551578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_551578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551578 prefixEnd_551578 := by exact prefixLift 551578
  have htrace : WordTrace (prefixWord ++ tailWord_551578) baseStart_551578 baseEnd_551578 := by
    simpa [prefixWord, tailWord_551578, baseEnd_551578] using wordTrace_append hprefix tailTrace_551578
  have hstable : (prefixWord ++ tailWord_551578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551578).length < 2 ^ (prefixWord ++ tailWord_551578).sum := by decide
  have hdescent : baseEnd_551578 < baseStart_551578 := by decide
  rcases family_descends (prefixWord ++ tailWord_551578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551644 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_551644 : Nat := 118140960795 + 551644 * 2 ^ 59
def prefixEnd_551644 : Nat := 4983230072969 + 3 ^ 40 * 551644 * 2
def baseEnd_551644 : Nat := 251785353039062154678259

theorem tailTrace_551644 : CollatzResearch.WordTrace tailWord_551644 prefixEnd_551644 251785353039062154678259 := by
  unfold tailWord_551644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060054806747738069802993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13413406408996984093070657 10060054806747738069802993)
  ·
    refine ⟨7545041105060803552352245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10060054806747738069802993 7545041105060803552352245)
    ·
      refine ⟨707347603599450333033023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7545041105060803552352245 707347603599450333033023)
      ·
        refine ⟨1061021405399175499549535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707347603599450333033023 1061021405399175499549535)
        ·
          refine ⟨1591532108098763249324303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061021405399175499549535 1591532108098763249324303)
          ·
            refine ⟨2387298162148144873986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591532108098763249324303 2387298162148144873986455)
            ·
              refine ⟨3580947243222217310979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387298162148144873986455 3580947243222217310979683)
              ·
                refine ⟨5371420864833325966469525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580947243222217310979683 5371420864833325966469525)
                ·
                  refine ⟨251785353039062154678259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5371420864833325966469525 251785353039062154678259)
                  ·
                    rfl

theorem cell20_551644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_551644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551644 prefixEnd_551644 := by exact prefixLift 551644
  have htrace : WordTrace (prefixWord ++ tailWord_551644) baseStart_551644 baseEnd_551644 := by
    simpa [prefixWord, tailWord_551644, baseEnd_551644] using wordTrace_append hprefix tailTrace_551644
  have hstable : (prefixWord ++ tailWord_551644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551644).length < 2 ^ (prefixWord ++ tailWord_551644).sum := by decide
  have hdescent : baseEnd_551644 < baseStart_551644 := by decide
  rcases family_descends (prefixWord ++ tailWord_551644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551661 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 2]
def baseStart_551661 : Nat := 118140960795 + 551661 * 2 ^ 59
def prefixEnd_551661 : Nat := 4983230072969 + 3 ^ 40 * 551661 * 2
def baseEnd_551661 : Nat := 251793112302285651111523

theorem tailTrace_551661 : CollatzResearch.WordTrace tailWord_551661 prefixEnd_551661 251793112302285651111523 := by
  unfold tailWord_551661
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120729654433888042974837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13413819769622592028649891 20120729654433888042974837)
  ·
    refine ⟨1886318405103177004028891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20120729654433888042974837 1886318405103177004028891)
    ·
      refine ⟨2829477607654765506043337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1886318405103177004028891 2829477607654765506043337)
      ·
        refine ⟨2122108205741074129532503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2829477607654765506043337 2122108205741074129532503)
        ·
          refine ⟨3183162308611611194298755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122108205741074129532503 3183162308611611194298755)
          ·
            refine ⟨4774743462917416791448133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183162308611611194298755 4774743462917416791448133)
            ·
              refine ⟨895264399297015648396525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4774743462917416791448133 895264399297015648396525)
              ·
                refine ⟨335724149736380868148697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895264399297015648396525 335724149736380868148697)
                ·
                  refine ⟨251793112302285651111523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335724149736380868148697 251793112302285651111523)
                  ·
                    rfl

theorem cell20_551661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_551661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551661 prefixEnd_551661 := by exact prefixLift 551661
  have htrace : WordTrace (prefixWord ++ tailWord_551661) baseStart_551661 baseEnd_551661 := by
    simpa [prefixWord, tailWord_551661, baseEnd_551661] using wordTrace_append hprefix tailTrace_551661
  have hstable : (prefixWord ++ tailWord_551661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551661).length < 2 ^ (prefixWord ++ tailWord_551661).sum := by decide
  have hdescent : baseEnd_551661 < baseStart_551661 := by decide
  rcases family_descends (prefixWord ++ tailWord_551661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551682 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_551682 : Nat := 118140960795 + 551682 * 2 ^ 59
def prefixEnd_551682 : Nat := 4983230072969 + 3 ^ 40 * 551682 * 2
def baseEnd_551682 : Nat := 251802697274502911411437

theorem tailTrace_551682 : CollatzResearch.WordTrace tailWord_551682 prefixEnd_551682 251802697274502911411437 := by
  unfold tailWord_551682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030373896839452157372325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13414330391571872419659533 5030373896839452157372325)
  ·
    refine ⟨943195105657397279507311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5030373896839452157372325 943195105657397279507311)
    ·
      refine ⟨1414792658486095919260967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943195105657397279507311 1414792658486095919260967)
      ·
        refine ⟨2122188987729143878891451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414792658486095919260967 2122188987729143878891451)
        ·
          refine ⟨3183283481593715818337177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122188987729143878891451 3183283481593715818337177)
          ·
            refine ⟨2387462611195286863752883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3183283481593715818337177 2387462611195286863752883)
            ·
              refine ⟨3581193916792930295629325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387462611195286863752883 3581193916792930295629325)
              ·
                refine ⟨1342947718797348860860997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3581193916792930295629325 1342947718797348860860997)
                ·
                  refine ⟨251802697274502911411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342947718797348860860997 251802697274502911411437)
                  ·
                    rfl

theorem cell20_551682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_551682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551682 prefixEnd_551682 := by exact prefixLift 551682
  have htrace : WordTrace (prefixWord ++ tailWord_551682) baseStart_551682 baseEnd_551682 := by
    simpa [prefixWord, tailWord_551682, baseEnd_551682] using wordTrace_append hprefix tailTrace_551682
  have hstable : (prefixWord ++ tailWord_551682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551682).length < 2 ^ (prefixWord ++ tailWord_551682).sum := by decide
  have hdescent : baseEnd_551682 < baseStart_551682 := by decide
  rcases family_descends (prefixWord ++ tailWord_551682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551716 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_551716 : Nat := 118140960795 + 551716 * 2 ^ 59
def prefixEnd_551716 : Nat := 4983230072969 + 3 ^ 40 * 551716 * 2
def baseEnd_551716 : Nat := 251818215800949904277965

theorem tailTrace_551716 : CollatzResearch.WordTrace tailWord_551716 prefixEnd_551716 251818215800949904277965 := by
  unfold tailWord_551716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061367834617316218113501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13415157112823088290818001 10061367834617316218113501)
  ·
    refine ⟨3773012937981493581792563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10061367834617316218113501 3773012937981493581792563)
    ·
      refine ⟨5659519406972240372688845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773012937981493581792563 5659519406972240372688845)
      ·
        refine ⟨2122319777614590139758317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5659519406972240372688845 2122319777614590139758317)
        ·
          refine ⟨795869916605471302409369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2122319777614590139758317 795869916605471302409369)
          ·
            refine ⟨596902437454103476807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795869916605471302409369 596902437454103476807027)
            ·
              refine ⟨895353656181155215210541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596902437454103476807027 895353656181155215210541)
              ·
                refine ⟨335757621067933205703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895353656181155215210541 335757621067933205703953)
                ·
                  refine ⟨251818215800949904277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335757621067933205703953 251818215800949904277965)
                  ·
                    rfl

theorem cell20_551716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_551716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551716 prefixEnd_551716 := by exact prefixLift 551716
  have htrace : WordTrace (prefixWord ++ tailWord_551716) baseStart_551716 baseEnd_551716 := by
    simpa [prefixWord, tailWord_551716, baseEnd_551716] using wordTrace_append hprefix tailTrace_551716
  have hstable : (prefixWord ++ tailWord_551716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551716).length < 2 ^ (prefixWord ++ tailWord_551716).sum := by decide
  have hdescent : baseEnd_551716 < baseStart_551716 := by decide
  rcases family_descends (prefixWord ++ tailWord_551716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551717 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_551717 : Nat := 118140960795 + 551717 * 2 ^ 59
def prefixEnd_551717 : Nat := 4983230072969 + 3 ^ 40 * 551717 * 2
def baseEnd_551717 : Nat := 251818672228198345244627

theorem tailTrace_551717 : CollatzResearch.WordTrace tailWord_551717 prefixEnd_551717 251818672228198345244627 := by
  unfold tailWord_551717
  simp only [CollatzResearch.WordTrace]
  refine ⟨20122772142231009607013405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13415181428154006404675603 20122772142231009607013405)
  ·
    refine ⟨7546039553336628602630027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20122772142231009607013405 7546039553336628602630027)
    ·
      refine ⟨11319059330004942903945041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7546039553336628602630027 11319059330004942903945041)
      ·
        refine ⟨8489294497503707177958781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11319059330004942903945041 8489294497503707177958781)
        ·
          refine ⟨3183485436563890191734543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8489294497503707177958781 3183485436563890191734543)
          ·
            refine ⟨4775228154845835287601815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183485436563890191734543 4775228154845835287601815)
            ·
              refine ⟨7162842232268752931402723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775228154845835287601815 7162842232268752931402723)
              ·
                refine ⟨10744263348403129397104085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7162842232268752931402723 10744263348403129397104085)
                ·
                  refine ⟨251818672228198345244627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10744263348403129397104085 251818672228198345244627)
                  ·
                    rfl

theorem cell20_551717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_551717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551717 prefixEnd_551717 := by exact prefixLift 551717
  have htrace : WordTrace (prefixWord ++ tailWord_551717) baseStart_551717 baseEnd_551717 := by
    simpa [prefixWord, tailWord_551717, baseEnd_551717] using wordTrace_append hprefix tailTrace_551717
  have hstable : (prefixWord ++ tailWord_551717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551717).length < 2 ^ (prefixWord ++ tailWord_551717).sum := by decide
  have hdescent : baseEnd_551717 < baseStart_551717 := by decide
  rcases family_descends (prefixWord ++ tailWord_551717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551817 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_551817 : Nat := 118140960795 + 551817 * 2 ^ 59
def prefixEnd_551817 : Nat := 4983230072969 + 3 ^ 40 * 551817 * 2
def baseEnd_551817 : Nat := 251864314953042441910885

theorem tailTrace_551817 : CollatzResearch.WordTrace tailWord_551817 prefixEnd_551817 251864314953042441910885 := by
  unfold tailWord_551817
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126419441868726685653705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13417612961245817790435803 20126419441868726685653705)
  ·
    refine ⟨15094814581401545014240279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20126419441868726685653705 15094814581401545014240279)
    ·
      refine ⟨22642221872102317521360419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094814581401545014240279 22642221872102317521360419)
      ·
        refine ⟨33963332808153476282040629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22642221872102317521360419 33963332808153476282040629)
        ·
          refine ⟨3184062450764388401441309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33963332808153476282040629 3184062450764388401441309)
          ·
            refine ⟨1194023419036645650540491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3184062450764388401441309 1194023419036645650540491)
            ·
              refine ⟨1791035128554968475810737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194023419036645650540491 1791035128554968475810737)
              ·
                refine ⟨1343276346416226356858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791035128554968475810737 1343276346416226356858053)
                ·
                  refine ⟨251864314953042441910885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343276346416226356858053 251864314953042441910885)
                  ·
                    rfl

theorem cell20_551817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_551817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551817 prefixEnd_551817 := by exact prefixLift 551817
  have htrace : WordTrace (prefixWord ++ tailWord_551817) baseStart_551817 baseEnd_551817 := by
    simpa [prefixWord, tailWord_551817, baseEnd_551817] using wordTrace_append hprefix tailTrace_551817
  have hstable : (prefixWord ++ tailWord_551817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551817).length < 2 ^ (prefixWord ++ tailWord_551817).sum := by decide
  have hdescent : baseEnd_551817 < baseStart_551817 := by decide
  rcases family_descends (prefixWord ++ tailWord_551817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551831 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_551831 : Nat := 118140960795 + 551831 * 2 ^ 59
def prefixEnd_551831 : Nat := 4983230072969 + 3 ^ 40 * 551831 * 2
def baseEnd_551831 : Nat := 251870704934520615444161

theorem tailTrace_551831 : CollatzResearch.WordTrace tailWord_551831 prefixEnd_551831 251870704934520615444161 := by
  unfold tailWord_551831
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126930063818007076663347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13417953375878671384442231 20126930063818007076663347)
  ·
    refine ⟨30190395095727010614995021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20126930063818007076663347 30190395095727010614995021)
    ·
      refine ⟨11321398160897628980623133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30190395095727010614995021 11321398160897628980623133)
      ·
        refine ⟨4245524310336610867733675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11321398160897628980623133 4245524310336610867733675)
        ·
          refine ⟨6368286465504916301600513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245524310336610867733675 6368286465504916301600513)
          ·
            refine ⟨4776214849128687226200385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6368286465504916301600513 4776214849128687226200385)
            ·
              refine ⟨3582161136846515419650289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776214849128687226200385 3582161136846515419650289)
              ·
                refine ⟨2686620852634886564737717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582161136846515419650289 2686620852634886564737717)
                ·
                  refine ⟨251870704934520615444161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686620852634886564737717 251870704934520615444161)
                  ·
                    rfl

theorem cell20_551831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_551831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551831 prefixEnd_551831 := by exact prefixLift 551831
  have htrace : WordTrace (prefixWord ++ tailWord_551831) baseStart_551831 baseEnd_551831 := by
    simpa [prefixWord, tailWord_551831, baseEnd_551831] using wordTrace_append hprefix tailTrace_551831
  have hstable : (prefixWord ++ tailWord_551831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551831).length < 2 ^ (prefixWord ++ tailWord_551831).sum := by decide
  have hdescent : baseEnd_551831 < baseStart_551831 := by decide
  rcases family_descends (prefixWord ++ tailWord_551831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551865 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_551865 : Nat := 118140960795 + 551865 * 2 ^ 59
def prefixEnd_551865 : Nat := 4983230072969 + 3 ^ 40 * 551865 * 2
def baseEnd_551865 : Nat := 251886223460967608310689

theorem tailTrace_551865 : CollatzResearch.WordTrace tailWord_551865 prefixEnd_551865 251886223460967608310689 := by
  unfold tailWord_551865
  simp only [CollatzResearch.WordTrace]
  refine ⟨20128170145694830883401049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13418780097129887255600699 20128170145694830883401049)
  ·
    refine ⟨15096127609271123162550787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20128170145694830883401049 15096127609271123162550787)
    ·
      refine ⟨22644191413906684743826181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15096127609271123162550787 22644191413906684743826181)
      ·
        refine ⟨4245785890107503389467409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22644191413906684743826181 4245785890107503389467409)
        ·
          refine ⟨3184339417580627542100557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4245785890107503389467409 3184339417580627542100557)
          ·
            refine ⟨1194127281592735328287709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3184339417580627542100557 1194127281592735328287709)
            ·
              refine ⟨447797730597275748107891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1194127281592735328287709 447797730597275748107891)
              ·
                refine ⟨671696595895913622161837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447797730597275748107891 671696595895913622161837)
                ·
                  refine ⟨251886223460967608310689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671696595895913622161837 251886223460967608310689)
                  ·
                    rfl

theorem cell20_551865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_551865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551865 prefixEnd_551865 := by exact prefixLift 551865
  have htrace : WordTrace (prefixWord ++ tailWord_551865) baseStart_551865 baseEnd_551865 := by
    simpa [prefixWord, tailWord_551865, baseEnd_551865] using wordTrace_append hprefix tailTrace_551865
  have hstable : (prefixWord ++ tailWord_551865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551865).length < 2 ^ (prefixWord ++ tailWord_551865).sum := by decide
  have hdescent : baseEnd_551865 < baseStart_551865 := by decide
  rcases family_descends (prefixWord ++ tailWord_551865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551907 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_551907 : Nat := 118140960795 + 551907 * 2 ^ 59
def prefixEnd_551907 : Nat := 4983230072969 + 3 ^ 40 * 551907 * 2
def baseEnd_551907 : Nat := 251905393405402128910517

theorem tailTrace_551907 : CollatzResearch.WordTrace tailWord_551907 prefixEnd_551907 251905393405402128910517 := by
  unfold tailWord_551907
  simp only [CollatzResearch.WordTrace]
  refine ⟨20129702011542672056429975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13419801341028448037619983 20129702011542672056429975)
  ·
    refine ⟨30194553017314008084644963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20129702011542672056429975 30194553017314008084644963)
    ·
      refine ⟨45291829525971012126967445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30194553017314008084644963 45291829525971012126967445)
      ·
        refine ⟨2123054509029891193451599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45291829525971012126967445 2123054509029891193451599)
        ·
          refine ⟨3184581763544836790177399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123054509029891193451599 3184581763544836790177399)
          ·
            refine ⟨4776872645317255185266099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184581763544836790177399 4776872645317255185266099)
            ·
              refine ⟨7165308967975882777899149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776872645317255185266099 7165308967975882777899149)
              ·
                refine ⟨2686990862990956041712181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7165308967975882777899149 2686990862990956041712181)
                ·
                  refine ⟨251905393405402128910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686990862990956041712181 251905393405402128910517)
                  ·
                    rfl

theorem cell20_551907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_551907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551907 prefixEnd_551907 := by exact prefixLift 551907
  have htrace : WordTrace (prefixWord ++ tailWord_551907) baseStart_551907 baseEnd_551907 := by
    simpa [prefixWord, tailWord_551907, baseEnd_551907] using wordTrace_append hprefix tailTrace_551907
  have hstable : (prefixWord ++ tailWord_551907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551907).length < 2 ^ (prefixWord ++ tailWord_551907).sum := by decide
  have hdescent : baseEnd_551907 < baseStart_551907 := by decide
  rcases family_descends (prefixWord ++ tailWord_551907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551962 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_551962 : Nat := 118140960795 + 551962 * 2 ^ 59
def prefixEnd_551962 : Nat := 4983230072969 + 3 ^ 40 * 551962 * 2
def baseEnd_551962 : Nat := 251930496904066382076959

theorem tailTrace_551962 : CollatzResearch.WordTrace tailWord_551962 prefixEnd_551962 251930496904066382076959 := by
  unfold tailWord_551962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032927006585854112420535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13421138684228944299788093 5032927006585854112420535)
  ·
    refine ⟨7549390509878781168630803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5032927006585854112420535 7549390509878781168630803)
    ·
      refine ⟨11324085764818171752946205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7549390509878781168630803 11324085764818171752946205)
      ·
        refine ⟨4246532161806814407354827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11324085764818171752946205 4246532161806814407354827)
        ·
          refine ⟨6369798242710221611032241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246532161806814407354827 6369798242710221611032241)
          ·
            refine ⟨4777348682032666208274181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369798242710221611032241 4777348682032666208274181)
            ·
              refine ⟨895752877881124914051409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4777348682032666208274181 895752877881124914051409)
              ·
                refine ⟨671814658410843685538557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895752877881124914051409 671814658410843685538557)
                ·
                  refine ⟨251930496904066382076959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671814658410843685538557 251930496904066382076959)
                  ·
                    rfl

theorem cell20_551962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_551962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551962 prefixEnd_551962 := by exact prefixLift 551962
  have htrace : WordTrace (prefixWord ++ tailWord_551962) baseStart_551962 baseEnd_551962 := by
    simpa [prefixWord, tailWord_551962, baseEnd_551962] using wordTrace_append hprefix tailTrace_551962
  have hstable : (prefixWord ++ tailWord_551962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551962).length < 2 ^ (prefixWord ++ tailWord_551962).sum := by decide
  have hdescent : baseEnd_551962 < baseStart_551962 := by decide
  rcases family_descends (prefixWord ++ tailWord_551962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551965 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 2]
def baseStart_551965 : Nat := 118140960795 + 551965 * 2 ^ 59
def prefixEnd_551965 : Nat := 4983230072969 + 3 ^ 40 * 551965 * 2
def baseEnd_551965 : Nat := 251931866185811704976947

theorem tailTrace_551965 : CollatzResearch.WordTrace tailWord_551965 prefixEnd_551965 251931866185811704976947 := by
  unfold tailWord_551965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131817445332547962041349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13421211630221698641360899 20131817445332547962041349)
  ·
    refine ⟨3774715770999852742882753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20131817445332547962041349 3774715770999852742882753)
    ·
      refine ⟨2831036828249889557162065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3774715770999852742882753 2831036828249889557162065)
      ·
        refine ⟨2123277621187417167871549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831036828249889557162065 2123277621187417167871549)
        ·
          refine ⟨796229107945281437951831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2123277621187417167871549 796229107945281437951831)
          ·
            refine ⟨1194343661917922156927747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796229107945281437951831 1194343661917922156927747)
            ·
              refine ⟨1791515492876883235391621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194343661917922156927747 1791515492876883235391621)
              ·
                refine ⟨335909154914415606635929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1791515492876883235391621 335909154914415606635929)
                ·
                  refine ⟨251931866185811704976947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335909154914415606635929 251931866185811704976947)
                  ·
                    rfl

theorem cell20_551965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_551965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551965 prefixEnd_551965 := by exact prefixLift 551965
  have htrace : WordTrace (prefixWord ++ tailWord_551965) baseStart_551965 baseEnd_551965 := by
    simpa [prefixWord, tailWord_551965, baseEnd_551965] using wordTrace_append hprefix tailTrace_551965
  have hstable : (prefixWord ++ tailWord_551965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551965).length < 2 ^ (prefixWord ++ tailWord_551965).sum := by decide
  have hdescent : baseEnd_551965 < baseStart_551965 := by decide
  rcases family_descends (prefixWord ++ tailWord_551965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551993 : List Nat := [1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_551993 : Nat := 118140960795 + 551993 * 2 ^ 59
def prefixEnd_551993 : Nat := 4983230072969 + 3 ^ 40 * 551993 * 2
def baseEnd_551993 : Nat := 83981548716256017347833

theorem tailTrace_551993 : CollatzResearch.WordTrace tailWord_551993 prefixEnd_551993 83981548716256017347833 := by
  unfold tailWord_551993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20132838689231108744060633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13421892459487405829373755 20132838689231108744060633)
  ·
    refine ⟨15099629016923331558045475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20132838689231108744060633 15099629016923331558045475)
    ·
      refine ⟨22649443525384997337068213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099629016923331558045475 22649443525384997337068213)
      ·
        refine ⟨2123385330504843500350145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22649443525384997337068213 2123385330504843500350145)
        ·
          refine ⟨1592538997878632625262609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2123385330504843500350145 1592538997878632625262609)
          ·
            refine ⟨1194404248408974468946957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592538997878632625262609 1194404248408974468946957)
            ·
              refine ⟨447901593153365425855109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1194404248408974468946957 447901593153365425855109)
              ·
                refine ⟨83981548716256017347833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447901593153365425855109 83981548716256017347833)
                ·
                  rfl

theorem cell20_551993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_551993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_551993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_551993 prefixEnd_551993 := by exact prefixLift 551993
  have htrace : WordTrace (prefixWord ++ tailWord_551993) baseStart_551993 baseEnd_551993 := by
    simpa [prefixWord, tailWord_551993, baseEnd_551993] using wordTrace_append hprefix tailTrace_551993
  have hstable : (prefixWord ++ tailWord_551993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551993).length < 2 ^ (prefixWord ++ tailWord_551993).sum := by decide
  have hdescent : baseEnd_551993 < baseStart_551993 := by decide
  rcases family_descends (prefixWord ++ tailWord_551993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552021 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_552021 : Nat := 118140960795 + 552021 * 2 ^ 59
def prefixEnd_552021 : Nat := 4983230072969 + 3 ^ 40 * 552021 * 2
def baseEnd_552021 : Nat := 251957426111724399110051

theorem tailTrace_552021 : CollatzResearch.WordTrace tailWord_552021 prefixEnd_552021 251957426111724399110051 := by
  unfold tailWord_552021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20133859933129669526079917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13422573288753113017386611 20133859933129669526079917)
  ·
    refine ⟨7550197474923626072279969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20133859933129669526079917 7550197474923626072279969)
    ·
      refine ⟨5662648106192719554209977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7550197474923626072279969 5662648106192719554209977)
      ·
        refine ⟨4246986079644539665657483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5662648106192719554209977 4246986079644539665657483)
        ·
          refine ⟨6370479119466809498486225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246986079644539665657483 6370479119466809498486225)
          ·
            refine ⟨4777859339600107123864669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6370479119466809498486225 4777859339600107123864669)
            ·
              refine ⟨1791697252350040171449251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4777859339600107123864669 1791697252350040171449251)
              ·
                refine ⟨2687545878525060257173877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791697252350040171449251 2687545878525060257173877)
                ·
                  refine ⟨251957426111724399110051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687545878525060257173877 251957426111724399110051)
                  ·
                    rfl

theorem cell20_552021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_552021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552021 prefixEnd_552021 := by exact prefixLift 552021
  have htrace : WordTrace (prefixWord ++ tailWord_552021) baseStart_552021 baseEnd_552021 := by
    simpa [prefixWord, tailWord_552021, baseEnd_552021] using wordTrace_append hprefix tailTrace_552021
  have hstable : (prefixWord ++ tailWord_552021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552021).length < 2 ^ (prefixWord ++ tailWord_552021).sum := by decide
  have hdescent : baseEnd_552021 < baseStart_552021 := by decide
  rcases family_descends (prefixWord ++ tailWord_552021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552034 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_552034 : Nat := 118140960795 + 552034 * 2 ^ 59
def prefixEnd_552034 : Nat := 4983230072969 + 3 ^ 40 * 552034 * 2
def baseEnd_552034 : Nat := 251963359665954131676665

theorem tailTrace_552034 : CollatzResearch.WordTrace tailWord_552034 prefixEnd_552034 251963359665954131676665 := by
  unfold tailWord_552034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033583520520643186575789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13422889388055048497535437 5033583520520643186575789)
  ·
    refine ⟨1887593820195241194965921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5033583520520643186575789 1887593820195241194965921)
    ·
      refine ⟨1415695365146430896224441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1887593820195241194965921 1415695365146430896224441)
      ·
        refine ⟨1061771523859823172168331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1415695365146430896224441 1061771523859823172168331)
        ·
          refine ⟨1592657285789734758252497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061771523859823172168331 1592657285789734758252497)
          ·
            refine ⟨1194492964342301068689373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592657285789734758252497 1194492964342301068689373)
            ·
              refine ⟨447934861628362900758515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1194492964342301068689373 447934861628362900758515)
              ·
                refine ⟨671902292442544351137773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447934861628362900758515 671902292442544351137773)
                ·
                  refine ⟨251963359665954131676665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671902292442544351137773 251963359665954131676665)
                  ·
                    rfl

theorem cell20_552034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_552034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552034 prefixEnd_552034 := by exact prefixLift 552034
  have htrace : WordTrace (prefixWord ++ tailWord_552034) baseStart_552034 baseEnd_552034 := by
    simpa [prefixWord, tailWord_552034, baseEnd_552034] using wordTrace_append hprefix tailTrace_552034
  have hstable : (prefixWord ++ tailWord_552034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552034).length < 2 ^ (prefixWord ++ tailWord_552034).sum := by decide
  have hdescent : baseEnd_552034 < baseStart_552034 := by decide
  rcases family_descends (prefixWord ++ tailWord_552034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552035 : List Nat := [1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_552035 : Nat := 118140960795 + 552035 * 2 ^ 59
def prefixEnd_552035 : Nat := 4983230072969 + 3 ^ 40 * 552035 * 2
def baseEnd_552035 : Nat := 83987938697734190881109

theorem tailTrace_552035 : CollatzResearch.WordTrace tailWord_552035 prefixEnd_552035 83987938697734190881109 := by
  unfold tailWord_552035
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134370555078949917089559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13422913703385966611393039 20134370555078949917089559)
  ·
    refine ⟨30201555832618424875634339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134370555078949917089559 30201555832618424875634339)
    ·
      refine ⟨45302333748927637313451509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30201555832618424875634339 45302333748927637313451509)
      ·
        refine ⟨4247093788961965998136079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45302333748927637313451509 4247093788961965998136079)
        ·
          refine ⟨6370640683442948997204119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247093788961965998136079 6370640683442948997204119)
          ·
            refine ⟨9555961025164423495806179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370640683442948997204119 9555961025164423495806179)
            ·
              refine ⟨14333941537746635243709269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9555961025164423495806179 14333941537746635243709269)
              ·
                refine ⟨83987938697734190881109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14333941537746635243709269 83987938697734190881109)
                ·
                  rfl

theorem cell20_552035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_552035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552035 prefixEnd_552035 := by exact prefixLift 552035
  have htrace : WordTrace (prefixWord ++ tailWord_552035) baseStart_552035 baseEnd_552035 := by
    simpa [prefixWord, tailWord_552035, baseEnd_552035] using wordTrace_append hprefix tailTrace_552035
  have hstable : (prefixWord ++ tailWord_552035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552035).length < 2 ^ (prefixWord ++ tailWord_552035).sum := by decide
  have hdescent : baseEnd_552035 < baseStart_552035 := by decide
  rcases family_descends (prefixWord ++ tailWord_552035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552045 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_552045 : Nat := 118140960795 + 552045 * 2 ^ 59
def prefixEnd_552045 : Nat := 4983230072969 + 3 ^ 40 * 552045 * 2
def baseEnd_552045 : Nat := 251968380365686982309953

theorem tailTrace_552045 : CollatzResearch.WordTrace tailWord_552045 prefixEnd_552045 251968380365686982309953 := by
  unfold tailWord_552045
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134735285042721624953589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423156856695147749969059 20134735285042721624953589)
  ·
    refine ⟨1887631432972755152339399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20134735285042721624953589 1887631432972755152339399)
    ·
      refine ⟨2831447149459132728509099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887631432972755152339399 2831447149459132728509099)
      ·
        refine ⟨4247170724188699092763649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831447149459132728509099 4247170724188699092763649)
        ·
          refine ⟨3185378043141524319572737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247170724188699092763649 3185378043141524319572737)
          ·
            refine ⟨2389033532356143239679553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185378043141524319572737 2389033532356143239679553)
            ·
              refine ⟨1791775149267107429759665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389033532356143239679553 1791775149267107429759665)
              ·
                refine ⟨1343831361950330572319749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791775149267107429759665 1343831361950330572319749)
                ·
                  refine ⟨251968380365686982309953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343831361950330572319749 251968380365686982309953)
                  ·
                    rfl

theorem cell20_552045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_552045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552045 prefixEnd_552045 := by exact prefixLift 552045
  have htrace : WordTrace (prefixWord ++ tailWord_552045) baseStart_552045 baseEnd_552045 := by
    simpa [prefixWord, tailWord_552045, baseEnd_552045] using wordTrace_append hprefix tailTrace_552045
  have hstable : (prefixWord ++ tailWord_552045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552045).length < 2 ^ (prefixWord ++ tailWord_552045).sum := by decide
  have hdescent : baseEnd_552045 < baseStart_552045 := by decide
  rcases family_descends (prefixWord ++ tailWord_552045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552069 : List Nat := [1, 3, 1, 1, 7, 1, 6]
def baseStart_552069 : Nat := 118140960795 + 552069 * 2 ^ 59
def prefixEnd_552069 : Nat := 4983230072969 + 3 ^ 40 * 552069 * 2
def baseEnd_552069 : Nat := 27997703846627729501095

theorem tailTrace_552069 : CollatzResearch.WordTrace tailWord_552069 prefixEnd_552069 27997703846627729501095 := by
  unfold tailWord_552069
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135610636955773723827261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423740424637182482551507 20135610636955773723827261)
  ·
    refine ⟨7550853988858415146435223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20135610636955773723827261 7550853988858415146435223)
    ·
      refine ⟨11326280983287622719652835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7550853988858415146435223 11326280983287622719652835)
      ·
        refine ⟨16989421474931434079479253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11326280983287622719652835 16989421474931434079479253)
        ·
          refine ⟨398189565818705486237795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16989421474931434079479253 398189565818705486237795)
          ·
            refine ⟨597284348728058229356693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398189565818705486237795 597284348728058229356693)
            ·
              refine ⟨27997703846627729501095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 597284348728058229356693 27997703846627729501095)
              ·
                rfl

theorem cell20_552069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_552069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552069 prefixEnd_552069 := by exact prefixLift 552069
  have htrace : WordTrace (prefixWord ++ tailWord_552069) baseStart_552069 baseEnd_552069 := by
    simpa [prefixWord, tailWord_552069, baseEnd_552069] using wordTrace_append hprefix tailTrace_552069
  have hstable : (prefixWord ++ tailWord_552069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552069).length < 2 ^ (prefixWord ++ tailWord_552069).sum := by decide
  have hdescent : baseEnd_552069 < baseStart_552069 := by decide
  rcases family_descends (prefixWord ++ tailWord_552069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552073 : List Nat := [1, 2, 1, 1, 4, 3, 8]
def baseStart_552073 : Nat := 118140960795 + 552073 * 2 ^ 59
def prefixEnd_552073 : Nat := 4983230072969 + 3 ^ 40 * 552073 * 2
def baseEnd_552073 : Nat := 27997906703182592152945

theorem tailTrace_552073 : CollatzResearch.WordTrace tailWord_552073 prefixEnd_552073 27997906703182592152945 := by
  unfold tailWord_552073
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135756528941282406972873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423837685960854937981915 20135756528941282406972873)
  ·
    refine ⟨15101817396705961805229655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20135756528941282406972873 15101817396705961805229655)
    ·
      refine ⟨22652726095058942707844483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15101817396705961805229655 22652726095058942707844483)
      ·
        refine ⟨33979089142588414061766725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22652726095058942707844483 33979089142588414061766725)
        ·
          refine ⟨6371079214235327636581261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33979089142588414061766725 6371079214235327636581261)
          ·
            refine ⟨2389154705338247863717973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6371079214235327636581261 2389154705338247863717973)
            ·
              refine ⟨27997906703182592152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2389154705338247863717973 27997906703182592152945)
              ·
                rfl

theorem cell20_552073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_552073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552073 prefixEnd_552073 := by exact prefixLift 552073
  have htrace : WordTrace (prefixWord ++ tailWord_552073) baseStart_552073 baseEnd_552073 := by
    simpa [prefixWord, tailWord_552073, baseEnd_552073] using wordTrace_append hprefix tailTrace_552073
  have hstable : (prefixWord ++ tailWord_552073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552073).length < 2 ^ (prefixWord ++ tailWord_552073).sum := by decide
  have hdescent : baseEnd_552073 < baseStart_552073 := by decide
  rcases family_descends (prefixWord ++ tailWord_552073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552083 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 2]
def baseStart_552083 : Nat := 118140960795 + 552083 * 2 ^ 59
def prefixEnd_552083 : Nat := 4983230072969 + 3 ^ 40 * 552083 * 2
def baseEnd_552083 : Nat := 251985724601127739043131

theorem tailTrace_552083 : CollatzResearch.WordTrace tailWord_552083 prefixEnd_552083 251985724601127739043131 := by
  unfold tailWord_552083
  simp only [CollatzResearch.WordTrace]
  refine ⟨20136121258905054114836903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13424080839270036076557935 20136121258905054114836903)
  ·
    refine ⟨30204181888357581172255355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20136121258905054114836903 30204181888357581172255355)
    ·
      refine ⟨45306272832536371758383033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30204181888357581172255355 45306272832536371758383033)
      ·
        refine ⟨33979704624402278818787275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45306272832536371758383033 33979704624402278818787275)
        ·
          refine ⟨50969556936603418228180913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33979704624402278818787275 50969556936603418228180913)
          ·
            refine ⟨38227167702452563671135685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50969556936603418228180913 38227167702452563671135685)
            ·
              refine ⟨7167593944209855688337941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38227167702452563671135685 7167593944209855688337941)
              ·
                refine ⟨335980966134836985390841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7167593944209855688337941 335980966134836985390841)
                ·
                  refine ⟨251985724601127739043131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335980966134836985390841 251985724601127739043131)
                  ·
                    rfl

theorem cell20_552083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2].length) (baseStart_552083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552083 prefixEnd_552083 := by exact prefixLift 552083
  have htrace : WordTrace (prefixWord ++ tailWord_552083) baseStart_552083 baseEnd_552083 := by
    simpa [prefixWord, tailWord_552083, baseEnd_552083] using wordTrace_append hprefix tailTrace_552083
  have hstable : (prefixWord ++ tailWord_552083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552083).length < 2 ^ (prefixWord ++ tailWord_552083).sum := by decide
  have hdescent : baseEnd_552083 < baseStart_552083 := by decide
  rcases family_descends (prefixWord ++ tailWord_552083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552090 : List Nat := [3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_552090 : Nat := 118140960795 + 552090 * 2 ^ 59
def prefixEnd_552090 : Nat := 4983230072969 + 3 ^ 40 * 552090 * 2
def baseEnd_552090 : Nat := 83996306530622275269923

theorem tailTrace_552090 : CollatzResearch.WordTrace tailWord_552090 prefixEnd_552090 83996306530622275269923 := by
  unfold tailWord_552090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034094142469923577585431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13424251046586462873561149 5034094142469923577585431)
  ·
    refine ⟨7551141213704885366378147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034094142469923577585431 7551141213704885366378147)
    ·
      refine ⟨11326711820557328049567221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551141213704885366378147 11326711820557328049567221)
      ·
        refine ⟨1061879233177249504646927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11326711820557328049567221 1061879233177249504646927)
        ·
          refine ⟨1592818849765874256970391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061879233177249504646927 1592818849765874256970391)
          ·
            refine ⟨2389228274648811385455587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592818849765874256970391 2389228274648811385455587)
            ·
              refine ⟨3583842411973217078183381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389228274648811385455587 3583842411973217078183381)
              ·
                refine ⟨83996306530622275269923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3583842411973217078183381 83996306530622275269923)
                ·
                  rfl

theorem cell20_552090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_552090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552090 prefixEnd_552090 := by exact prefixLift 552090
  have htrace : WordTrace (prefixWord ++ tailWord_552090) baseStart_552090 baseEnd_552090 := by
    simpa [prefixWord, tailWord_552090, baseEnd_552090] using wordTrace_append hprefix tailTrace_552090
  have hstable : (prefixWord ++ tailWord_552090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552090).length < 2 ^ (prefixWord ++ tailWord_552090).sum := by decide
  have hdescent : baseEnd_552090 < baseStart_552090 := by decide
  rcases family_descends (prefixWord ++ tailWord_552090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552111 : List Nat := [1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_552111 : Nat := 118140960795 + 552111 * 2 ^ 59
def prefixEnd_552111 : Nat := 4983230072969 + 3 ^ 40 * 552111 * 2
def baseEnd_552111 : Nat := 83999501521361362036561

theorem tailTrace_552111 : CollatzResearch.WordTrace tailWord_552111 prefixEnd_552111 83999501521361362036561 := by
  unfold tailWord_552111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20137142502803614896856187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13424761668535743264570791 20137142502803614896856187)
  ·
    refine ⟨30205713754205422345284281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20137142502803614896856187 30205713754205422345284281)
    ·
      refine ⟨22654285315654066758963211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30205713754205422345284281 22654285315654066758963211)
      ·
        refine ⟨33981427973481100138444817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22654285315654066758963211 33981427973481100138444817)
        ·
          refine ⟨25486070980110825103833613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33981427973481100138444817 25486070980110825103833613)
          ·
            refine ⟨9557276617541559413937605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25486070980110825103833613 9557276617541559413937605)
            ·
              refine ⟨1791989365789042390113301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9557276617541559413937605 1791989365789042390113301)
              ·
                refine ⟨83999501521361362036561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1791989365789042390113301 83999501521361362036561)
                ·
                  rfl

theorem cell20_552111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_552111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552111 prefixEnd_552111 := by exact prefixLift 552111
  have htrace : WordTrace (prefixWord ++ tailWord_552111) baseStart_552111 baseEnd_552111 := by
    simpa [prefixWord, tailWord_552111, baseEnd_552111] using wordTrace_append hprefix tailTrace_552111
  have hstable : (prefixWord ++ tailWord_552111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552111).length < 2 ^ (prefixWord ++ tailWord_552111).sum := by decide
  have hdescent : baseEnd_552111 < baseStart_552111 := by decide
  rcases family_descends (prefixWord ++ tailWord_552111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552128 : List Nat := [2, 1, 1, 2, 7, 7]
def baseStart_552128 : Nat := 118140960795 + 552128 * 2 ^ 59
def prefixEnd_552128 : Nat := 4983230072969 + 3 ^ 40 * 552128 * 2
def baseEnd_552128 : Nat := 9333565326937317871961

theorem tailTrace_552128 : CollatzResearch.WordTrace tailWord_552128 prefixEnd_552128 9333565326937317871961 := by
  unfold tailWord_552128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068881271871013400112519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13425175029161351200150025 10068881271871013400112519)
  ·
    refine ⟨15103321907806520100168779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068881271871013400112519 15103321907806520100168779)
    ·
      refine ⟨22654982861709780150253169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15103321907806520100168779 22654982861709780150253169)
      ·
        refine ⟨16991237146282335112689877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22654982861709780150253169 16991237146282335112689877)
        ·
          refine ⟨398232120615992229203669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16991237146282335112689877 398232120615992229203669)
          ·
            refine ⟨9333565326937317871961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 398232120615992229203669 9333565326937317871961)
            ·
              rfl

theorem cell20_552128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 7].length) (baseStart_552128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552128 prefixEnd_552128 := by exact prefixLift 552128
  have htrace : WordTrace (prefixWord ++ tailWord_552128) baseStart_552128 baseEnd_552128 := by
    simpa [prefixWord, tailWord_552128, baseEnd_552128] using wordTrace_append hprefix tailTrace_552128
  have hstable : (prefixWord ++ tailWord_552128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552128).length < 2 ^ (prefixWord ++ tailWord_552128).sum := by decide
  have hdescent : baseEnd_552128 < baseStart_552128 := by decide
  rcases family_descends (prefixWord ++ tailWord_552128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552130 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_552130 : Nat := 118140960795 + 552130 * 2 ^ 59
def prefixEnd_552130 : Nat := 4983230072969 + 3 ^ 40 * 552130 * 2
def baseEnd_552130 : Nat := 252007176681804464476273

theorem tailTrace_552130 : CollatzResearch.WordTrace tailWord_552130 prefixEnd_552130 252007176681804464476273 := by
  unfold tailWord_552130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034458872433695285449461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13425223659823187427865229 5034458872433695285449461)
  ·
    refine ⟨471980519290658933010887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5034458872433695285449461 471980519290658933010887)
    ·
      refine ⟨707970778935988399516331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471980519290658933010887 707970778935988399516331)
      ·
        refine ⟨1061956168403982599274497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707970778935988399516331 1061956168403982599274497)
        ·
          refine ⟨796467126302986949455873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061956168403982599274497 796467126302986949455873)
          ·
            refine ⟨597350344727240212091905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796467126302986949455873 597350344727240212091905)
            ·
              refine ⟨448012758545430159068929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597350344727240212091905 448012758545430159068929)
              ·
                refine ⟨336009568909072619301697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448012758545430159068929 336009568909072619301697)
                ·
                  refine ⟨252007176681804464476273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336009568909072619301697 252007176681804464476273)
                  ·
                    rfl

theorem cell20_552130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_552130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552130 prefixEnd_552130 := by exact prefixLift 552130
  have htrace : WordTrace (prefixWord ++ tailWord_552130) baseStart_552130 baseEnd_552130 := by
    simpa [prefixWord, tailWord_552130, baseEnd_552130] using wordTrace_append hprefix tailTrace_552130
  have hstable : (prefixWord ++ tailWord_552130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552130).length < 2 ^ (prefixWord ++ tailWord_552130).sum := by decide
  have hdescent : baseEnd_552130 < baseStart_552130 := by decide
  rcases family_descends (prefixWord ++ tailWord_552130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552138 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_552138 : Nat := 118140960795 + 552138 * 2 ^ 59
def prefixEnd_552138 : Nat := 4983230072969 + 3 ^ 40 * 552138 * 2
def baseEnd_552138 : Nat := 252010828099791992209573

theorem tailTrace_552138 : CollatzResearch.WordTrace tailWord_552138 prefixEnd_552138 252010828099791992209573 := by
  unfold tailWord_552138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034531818426449627022267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13425418182470532338726045 5034531818426449627022267)
  ·
    refine ⟨7551797727639674440533401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034531818426449627022267 7551797727639674440533401)
    ·
      refine ⟨5663848295729755830400051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7551797727639674440533401 5663848295729755830400051)
      ·
        refine ⟨8495772443594633745600077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663848295729755830400051 8495772443594633745600077)
        ·
          refine ⟨3185914666347987654600029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8495772443594633745600077 3185914666347987654600029)
          ·
            refine ⟨1194717999880495370475011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3185914666347987654600029 1194717999880495370475011)
            ·
              refine ⟨1792076999820743055712517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194717999880495370475011 1792076999820743055712517)
              ·
                refine ⟨336014437466389322946097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1792076999820743055712517 336014437466389322946097)
                ·
                  refine ⟨252010828099791992209573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336014437466389322946097 252010828099791992209573)
                  ·
                    rfl

theorem cell20_552138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_552138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552138 prefixEnd_552138 := by exact prefixLift 552138
  have htrace : WordTrace (prefixWord ++ tailWord_552138) baseStart_552138 baseEnd_552138 := by
    simpa [prefixWord, tailWord_552138, baseEnd_552138] using wordTrace_append hprefix tailTrace_552138
  have hstable : (prefixWord ++ tailWord_552138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552138).length < 2 ^ (prefixWord ++ tailWord_552138).sum := by decide
  have hdescent : baseEnd_552138 < baseStart_552138 := by decide
  rcases family_descends (prefixWord ++ tailWord_552138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552141 : List Nat := [1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_552141 : Nat := 118140960795 + 552141 * 2 ^ 59
def prefixEnd_552141 : Nat := 4983230072969 + 3 ^ 40 * 552141 * 2
def baseEnd_552141 : Nat := 84004065793845771703187

theorem tailTrace_552141 : CollatzResearch.WordTrace tailWord_552141 prefixEnd_552141 84004065793845771703187 := by
  unfold tailWord_552141
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138236692694930020448277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425491128463286680298851 20138236692694930020448277)
  ·
    refine ⟨943979844970074844708513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20138236692694930020448277 943979844970074844708513)
    ·
      refine ⟨707984883727556133531385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 943979844970074844708513 707984883727556133531385)
      ·
        refine ⟨530988662795667100148539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707984883727556133531385 530988662795667100148539)
        ·
          refine ⟨796482994193500650222809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530988662795667100148539 796482994193500650222809)
          ·
            refine ⟨597362245645125487667107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796482994193500650222809 597362245645125487667107)
            ·
              refine ⟨896043368467688231500661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597362245645125487667107 896043368467688231500661)
              ·
                refine ⟨84004065793845771703187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 896043368467688231500661 84004065793845771703187)
                ·
                  rfl

theorem cell20_552141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_552141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552141 prefixEnd_552141 := by exact prefixLift 552141
  have htrace : WordTrace (prefixWord ++ tailWord_552141) baseStart_552141 baseEnd_552141 := by
    simpa [prefixWord, tailWord_552141, baseEnd_552141] using wordTrace_append hprefix tailTrace_552141
  have hstable : (prefixWord ++ tailWord_552141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552141).length < 2 ^ (prefixWord ++ tailWord_552141).sum := by decide
  have hdescent : baseEnd_552141 < baseStart_552141 := by decide
  rcases family_descends (prefixWord ++ tailWord_552141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552190 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_552190 : Nat := 118140960795 + 552190 * 2 ^ 59
def prefixEnd_552190 : Nat := 4983230072969 + 3 ^ 40 * 552190 * 2
def baseEnd_552190 : Nat := 252034562316710922476027

theorem tailTrace_552190 : CollatzResearch.WordTrace tailWord_552190 prefixEnd_552190 252034562316710922476027 := by
  unfold tailWord_552190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517502983689676423622753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13426682579678274259321349 2517502983689676423622753)
  ·
    refine ⟨1888127237767257317717065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2517502983689676423622753 1888127237767257317717065)
    ·
      refine ⟨1416095428325442988287799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1888127237767257317717065 1416095428325442988287799)
      ·
        refine ⟨2124143142488164482431699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416095428325442988287799 2124143142488164482431699)
        ·
          refine ⟨3186214713732246723647549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124143142488164482431699 3186214713732246723647549)
          ·
            refine ⟨1194830517649592521367831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3186214713732246723647549 1194830517649592521367831)
            ·
              refine ⟨1792245776474388782051747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194830517649592521367831 1792245776474388782051747)
              ·
                refine ⟨2688368664711583173077621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792245776474388782051747 2688368664711583173077621)
                ·
                  refine ⟨252034562316710922476027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688368664711583173077621 252034562316710922476027)
                  ·
                    rfl

theorem cell20_552190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_552190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552190 prefixEnd_552190 := by exact prefixLift 552190
  have htrace : WordTrace (prefixWord ++ tailWord_552190) baseStart_552190 baseEnd_552190 := by
    simpa [prefixWord, tailWord_552190, baseEnd_552190] using wordTrace_append hprefix tailTrace_552190
  have hstable : (prefixWord ++ tailWord_552190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552190).length < 2 ^ (prefixWord ++ tailWord_552190).sum := by decide
  have hdescent : baseEnd_552190 < baseStart_552190 := by decide
  rcases family_descends (prefixWord ++ tailWord_552190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552197 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 2]
def baseStart_552197 : Nat := 118140960795 + 552197 * 2 ^ 59
def prefixEnd_552197 : Nat := 4983230072969 + 3 ^ 40 * 552197 * 2
def baseEnd_552197 : Nat := 252037757307450009242665

theorem tailTrace_552197 : CollatzResearch.WordTrace tailWord_552197 prefixEnd_552197 252037757307450009242665 := by
  unfold tailWord_552197
  simp only [CollatzResearch.WordTrace]
  refine ⟨20140279180492051584486845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13426852786994701056324563 20140279180492051584486845)
  ·
    refine ⟨7552604692684519344182567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20140279180492051584486845 7552604692684519344182567)
    ·
      refine ⟨11328907039026779016273851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7552604692684519344182567 11328907039026779016273851)
      ·
        refine ⟨16993360558540168524410777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11328907039026779016273851 16993360558540168524410777)
        ·
          refine ⟨12745020418905126393308083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16993360558540168524410777 12745020418905126393308083)
          ·
            refine ⟨19117530628357689589962125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12745020418905126393308083 19117530628357689589962125)
            ·
              refine ⟨7169073985634133596235797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19117530628357689589962125 7169073985634133596235797)
              ·
                refine ⟨336050343076600012323553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7169073985634133596235797 336050343076600012323553)
                ·
                  refine ⟨252037757307450009242665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336050343076600012323553 252037757307450009242665)
                  ·
                    rfl

theorem cell20_552197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_552197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552197 prefixEnd_552197 := by exact prefixLift 552197
  have htrace : WordTrace (prefixWord ++ tailWord_552197) baseStart_552197 baseEnd_552197 := by
    simpa [prefixWord, tailWord_552197, baseEnd_552197] using wordTrace_append hprefix tailTrace_552197
  have hstable : (prefixWord ++ tailWord_552197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552197).length < 2 ^ (prefixWord ++ tailWord_552197).sum := by decide
  have hdescent : baseEnd_552197 < baseStart_552197 := by decide
  rcases family_descends (prefixWord ++ tailWord_552197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552221 : List Nat := [1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_552221 : Nat := 118140960795 + 552221 * 2 ^ 59
def prefixEnd_552221 : Nat := 4983230072969 + 3 ^ 40 * 552221 * 2
def baseEnd_552221 : Nat := 84016237187137530814189

theorem tailTrace_552221 : CollatzResearch.WordTrace tailWord_552221 prefixEnd_552221 84016237187137530814189 := by
  unfold tailWord_552221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20141154532405103683360517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13427436354936735788907011 20141154532405103683360517)
  ·
    refine ⟨3776466474825956940630097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20141154532405103683360517 3776466474825956940630097)
    ·
      refine ⟨2832349856119467705472573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3776466474825956940630097 2832349856119467705472573)
      ·
        refine ⟨1062131196044800389552215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2832349856119467705472573 1062131196044800389552215)
        ·
          refine ⟨1593196794067200584328323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062131196044800389552215 1593196794067200584328323)
          ·
            refine ⟨2389795191100800876492485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593196794067200584328323 2389795191100800876492485)
            ·
              refine ⟨448086598331400164342341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2389795191100800876492485 448086598331400164342341)
              ·
                refine ⟨84016237187137530814189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448086598331400164342341 84016237187137530814189)
                ·
                  rfl

theorem cell20_552221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_552221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552221 prefixEnd_552221 := by exact prefixLift 552221
  have htrace : WordTrace (prefixWord ++ tailWord_552221) baseStart_552221 baseEnd_552221 := by
    simpa [prefixWord, tailWord_552221, baseEnd_552221] using wordTrace_append hprefix tailTrace_552221
  have hstable : (prefixWord ++ tailWord_552221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552221).length < 2 ^ (prefixWord ++ tailWord_552221).sum := by decide
  have hdescent : baseEnd_552221 < baseStart_552221 := by decide
  rcases family_descends (prefixWord ++ tailWord_552221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552242 : List Nat := [3, 2, 1, 1, 4, 3, 6]
def baseStart_552242 : Nat := 118140960795 + 552242 * 2 ^ 59
def prefixEnd_552242 : Nat := 4983230072969 + 3 ^ 40 * 552242 * 2
def baseEnd_552242 : Nat := 28006477392625539193609

theorem tailTrace_552242 : CollatzResearch.WordTrace tailWord_552242 prefixEnd_552242 28006477392625539193609 := by
  unfold tailWord_552242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035480116332256067468745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13427946976886016179916653 5035480116332256067468745)
  ·
    refine ⟨3776610087249192050601559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5035480116332256067468745 3776610087249192050601559)
    ·
      refine ⟨5664915130873788075902339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776610087249192050601559 5664915130873788075902339)
      ·
        refine ⟨8497372696310682113853509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664915130873788075902339 8497372696310682113853509)
        ·
          refine ⟨1593257380558252896347533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8497372696310682113853509 1593257380558252896347533)
          ·
            refine ⟨597471517709344836130325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1593257380558252896347533 597471517709344836130325)
            ·
              refine ⟨28006477392625539193609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 597471517709344836130325 28006477392625539193609)
              ·
                rfl

theorem cell20_552242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_552242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552242 prefixEnd_552242 := by exact prefixLift 552242
  have htrace : WordTrace (prefixWord ++ tailWord_552242) baseStart_552242 baseEnd_552242 := by
    simpa [prefixWord, tailWord_552242, baseEnd_552242] using wordTrace_append hprefix tailTrace_552242
  have hstable : (prefixWord ++ tailWord_552242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552242).length < 2 ^ (prefixWord ++ tailWord_552242).sum := by decide
  have hdescent : baseEnd_552242 < baseStart_552242 := by decide
  rcases family_descends (prefixWord ++ tailWord_552242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552263 : List Nat := [1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_552263 : Nat := 118140960795 + 552263 * 2 ^ 59
def prefixEnd_552263 : Nat := 4983230072969 + 3 ^ 40 * 552263 * 2
def baseEnd_552263 : Nat := 84022627168615704347465

theorem tailTrace_552263 : CollatzResearch.WordTrace tailWord_552263 prefixEnd_552263 84022627168615704347465 := by
  unfold tailWord_552263
  simp only [CollatzResearch.WordTrace]
  refine ⟨20142686398252944856389443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13428457598835296570926295 20142686398252944856389443)
  ·
    refine ⟨30214029597379417284584165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20142686398252944856389443 30214029597379417284584165)
    ·
      refine ⟨5665130549508640740859531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30214029597379417284584165 5665130549508640740859531)
      ·
        refine ⟨8497695824262961111289297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665130549508640740859531 8497695824262961111289297)
        ·
          refine ⟨6373271868197220833466973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8497695824262961111289297 6373271868197220833466973)
          ·
            refine ⟨2389976950573957812550115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6373271868197220833466973 2389976950573957812550115)
            ·
              refine ⟨3584965425860936718825173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389976950573957812550115 3584965425860936718825173)
              ·
                refine ⟨84022627168615704347465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3584965425860936718825173 84022627168615704347465)
                ·
                  rfl

theorem cell20_552263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_552263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552263 prefixEnd_552263 := by exact prefixLift 552263
  have htrace : WordTrace (prefixWord ++ tailWord_552263) baseStart_552263 baseEnd_552263 := by
    simpa [prefixWord, tailWord_552263, baseEnd_552263] using wordTrace_append hprefix tailTrace_552263
  have hstable : (prefixWord ++ tailWord_552263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552263).length < 2 ^ (prefixWord ++ tailWord_552263).sum := by decide
  have hdescent : baseEnd_552263 < baseStart_552263 := by decide
  rcases family_descends (prefixWord ++ tailWord_552263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552290 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_552290 : Nat := 118140960795 + 552290 * 2 ^ 59
def prefixEnd_552290 : Nat := 4983230072969 + 3 ^ 40 * 552290 * 2
def baseEnd_552290 : Nat := 252080205041555019142285

theorem tailTrace_552290 : CollatzResearch.WordTrace tailWord_552290 prefixEnd_552290 252080205041555019142285 := by
  unfold tailWord_552290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035917792288782116905581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13429114112770085645081549 5035917792288782116905581)
  ·
    refine ⟨1888469172108293293839593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5035917792288782116905581 1888469172108293293839593)
    ·
      refine ⟨1416351879081219970379695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1888469172108293293839593 1416351879081219970379695)
      ·
        refine ⟨2124527818621829955569543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416351879081219970379695 2124527818621829955569543)
        ·
          refine ⟨3186791727932744933354315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124527818621829955569543 3186791727932744933354315)
          ·
            refine ⟨4780187591899117400031473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186791727932744933354315 4780187591899117400031473)
            ·
              refine ⟨3585140693924338050023605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780187591899117400031473 3585140693924338050023605)
              ·
                refine ⟨336106940055406692189713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3585140693924338050023605 336106940055406692189713)
                ·
                  refine ⟨252080205041555019142285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336106940055406692189713 252080205041555019142285)
                  ·
                    rfl

theorem cell20_552290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_552290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552290 prefixEnd_552290 := by exact prefixLift 552290
  have htrace : WordTrace (prefixWord ++ tailWord_552290) baseStart_552290 baseEnd_552290 := by
    simpa [prefixWord, tailWord_552290, baseEnd_552290] using wordTrace_append hprefix tailTrace_552290
  have hstable : (prefixWord ++ tailWord_552290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552290).length < 2 ^ (prefixWord ++ tailWord_552290).sum := by decide
  have hdescent : baseEnd_552290 < baseStart_552290 := by decide
  rcases family_descends (prefixWord ++ tailWord_552290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552301 : List Nat := [1, 5, 1, 1, 1, 11]
def baseStart_552301 : Nat := 118140960795 + 552301 * 2 ^ 59
def prefixEnd_552301 : Nat := 4983230072969 + 3 ^ 40 * 552301 * 2
def baseEnd_552301 : Nat := 9336489842269921102799

theorem tailTrace_552301 : CollatzResearch.WordTrace tailWord_552301 prefixEnd_552301 9336489842269921102799 := by
  unfold tailWord_552301
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144072372115277346272757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13429381581410184897515171 20144072372115277346272757)
  ·
    refine ⟨1888506784885807251213071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20144072372115277346272757 1888506784885807251213071)
    ·
      refine ⟨2832760177328710876819607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888506784885807251213071 2832760177328710876819607)
      ·
        refine ⟨4249140265993066315229411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832760177328710876819607 4249140265993066315229411)
        ·
          refine ⟨6373710398989599472844117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249140265993066315229411 6373710398989599472844117)
          ·
            refine ⟨9336489842269921102799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6373710398989599472844117 9336489842269921102799)
            ·
              rfl

theorem cell20_552301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_552301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552301 prefixEnd_552301 := by exact prefixLift 552301
  have htrace : WordTrace (prefixWord ++ tailWord_552301) baseStart_552301 baseEnd_552301 := by
    simpa [prefixWord, tailWord_552301, baseEnd_552301] using wordTrace_append hprefix tailTrace_552301
  have hstable : (prefixWord ++ tailWord_552301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552301).length < 2 ^ (prefixWord ++ tailWord_552301).sum := by decide
  have hdescent : baseEnd_552301 < baseStart_552301 := by decide
  rcases family_descends (prefixWord ++ tailWord_552301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552311 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 2]
def baseStart_552311 : Nat := 118140960795 + 552311 * 2 ^ 59
def prefixEnd_552311 : Nat := 4983230072969 + 3 ^ 40 * 552311 * 2
def baseEnd_552311 : Nat := 252089790013772279442199

theorem tailTrace_552311 : CollatzResearch.WordTrace tailWord_552311 prefixEnd_552311 252089790013772279442199 := by
  unfold tailWord_552311
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144437102079049054136787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13429624734719366036091191 20144437102079049054136787)
  ·
    refine ⟨30216655653118573581205181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20144437102079049054136787 30216655653118573581205181)
    ·
      refine ⟨11331245869919465092951943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30216655653118573581205181 11331245869919465092951943)
      ·
        refine ⟨16996868804879197639427915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331245869919465092951943 16996868804879197639427915)
        ·
          refine ⟨25495303207318796459141873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16996868804879197639427915 25495303207318796459141873)
          ·
            refine ⟨19121477405489097344356405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25495303207318796459141873 19121477405489097344356405)
            ·
              refine ⟨1792638506764602876033413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19121477405489097344356405 1792638506764602876033413)
              ·
                refine ⟨336119720018363039256265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1792638506764602876033413 336119720018363039256265)
                ·
                  refine ⟨252089790013772279442199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336119720018363039256265 252089790013772279442199)
                  ·
                    rfl

theorem cell20_552311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2].length) (baseStart_552311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552311 prefixEnd_552311 := by exact prefixLift 552311
  have htrace : WordTrace (prefixWord ++ tailWord_552311) baseStart_552311 baseEnd_552311 := by
    simpa [prefixWord, tailWord_552311, baseEnd_552311] using wordTrace_append hprefix tailTrace_552311
  have hstable : (prefixWord ++ tailWord_552311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552311).length < 2 ^ (prefixWord ++ tailWord_552311).sum := by decide
  have hdescent : baseEnd_552311 < baseStart_552311 := by decide
  rcases family_descends (prefixWord ++ tailWord_552311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552325 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_552325 : Nat := 118140960795 + 552325 * 2 ^ 59
def prefixEnd_552325 : Nat := 4983230072969 + 3 ^ 40 * 552325 * 2
def baseEnd_552325 : Nat := 252096179995250452975475

theorem tailTrace_552325 : CollatzResearch.WordTrace tailWord_552325 prefixEnd_552325 252096179995250452975475 := by
  unfold tailWord_552325
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144947724028329445146429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13429965149352219630097619 20144947724028329445146429)
  ·
    refine ⟨7554355396510623541929911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20144947724028329445146429 7554355396510623541929911)
    ·
      refine ⟨11331533094765935312894867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554355396510623541929911 11331533094765935312894867)
      ·
        refine ⟨16997299642148902969342301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331533094765935312894867 16997299642148902969342301)
        ·
          refine ⟨6373987365805838613503363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16997299642148902969342301 6373987365805838613503363)
          ·
            refine ⟨9560981048708757920255045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6373987365805838613503363 9560981048708757920255045)
            ·
              refine ⟨1792683946632892110047821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9560981048708757920255045 1792683946632892110047821)
              ·
                refine ⟨672256479987334541267933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1792683946632892110047821 672256479987334541267933)
                ·
                  refine ⟨252096179995250452975475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672256479987334541267933 252096179995250452975475)
                  ·
                    rfl

theorem cell20_552325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_552325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552325 prefixEnd_552325 := by exact prefixLift 552325
  have htrace : WordTrace (prefixWord ++ tailWord_552325) baseStart_552325 baseEnd_552325 := by
    simpa [prefixWord, tailWord_552325, baseEnd_552325] using wordTrace_append hprefix tailTrace_552325
  have hstable : (prefixWord ++ tailWord_552325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552325).length < 2 ^ (prefixWord ++ tailWord_552325).sum := by decide
  have hdescent : baseEnd_552325 < baseStart_552325 := by decide
  rcases family_descends (prefixWord ++ tailWord_552325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552332 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_552332 : Nat := 118140960795 + 552332 * 2 ^ 59
def prefixEnd_552332 : Nat := 4983230072969 + 3 ^ 40 * 552332 * 2
def baseEnd_552332 : Nat := 252099374985989539742113

theorem tailTrace_552332 : CollatzResearch.WordTrace tailWord_552332 prefixEnd_552332 252099374985989539742113 := by
  unfold tailWord_552332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072601517501484820325625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13430135356668646427100833 10072601517501484820325625)
  ·
    refine ⟨7554451138126113615244219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10072601517501484820325625 7554451138126113615244219)
    ·
      refine ⟨11331676707189170422866329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554451138126113615244219 11331676707189170422866329)
      ·
        refine ⟨8498757530391877817149747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11331676707189170422866329 8498757530391877817149747)
        ·
          refine ⟨12748136295587816725724621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498757530391877817149747 12748136295587816725724621)
          ·
            refine ⟨4780551110845431272146733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12748136295587816725724621 4780551110845431272146733)
            ·
              refine ⟨1792706666567036727055025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4780551110845431272146733 1792706666567036727055025)
              ·
                refine ⟨1344529999925277545291269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792706666567036727055025 1344529999925277545291269)
                ·
                  refine ⟨252099374985989539742113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344529999925277545291269 252099374985989539742113)
                  ·
                    rfl

theorem cell20_552332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_552332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552332 prefixEnd_552332 := by exact prefixLift 552332
  have htrace : WordTrace (prefixWord ++ tailWord_552332) baseStart_552332 baseEnd_552332 := by
    simpa [prefixWord, tailWord_552332, baseEnd_552332] using wordTrace_append hprefix tailTrace_552332
  have hstable : (prefixWord ++ tailWord_552332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552332).length < 2 ^ (prefixWord ++ tailWord_552332).sum := by decide
  have hdescent : baseEnd_552332 < baseStart_552332 := by decide
  rcases family_descends (prefixWord ++ tailWord_552332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552394 : List Nat := [3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_552394 : Nat := 118140960795 + 552394 * 2 ^ 59
def prefixEnd_552394 : Nat := 4983230072969 + 3 ^ 40 * 552394 * 2
def baseEnd_552394 : Nat := 84042557825130959891731

theorem tailTrace_552394 : CollatzResearch.WordTrace tailWord_552394 prefixEnd_552394 84042557825130959891731 := by
  unfold tailWord_552394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036866090194588557352059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13431642907185569486272157 5036866090194588557352059)
  ·
    refine ⟨7555299135291882836028089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036866090194588557352059 7555299135291882836028089)
    ·
      refine ⟨5666474351468912127021067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7555299135291882836028089 5666474351468912127021067)
      ·
        refine ⟨8499711527203368190531601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5666474351468912127021067 8499711527203368190531601)
        ·
          refine ⟨6374783645402526142898701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8499711527203368190531601 6374783645402526142898701)
          ·
            refine ⟨2390543867025947303587013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6374783645402526142898701 2390543867025947303587013)
            ·
              refine ⟨448226975067365119422565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2390543867025947303587013 448226975067365119422565)
              ·
                refine ⟨84042557825130959891731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448226975067365119422565 84042557825130959891731)
                ·
                  rfl

theorem cell20_552394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_552394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552394 prefixEnd_552394 := by exact prefixLift 552394
  have htrace : WordTrace (prefixWord ++ tailWord_552394) baseStart_552394 baseEnd_552394 := by
    simpa [prefixWord, tailWord_552394, baseEnd_552394] using wordTrace_append hprefix tailTrace_552394
  have hstable : (prefixWord ++ tailWord_552394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552394).length < 2 ^ (prefixWord ++ tailWord_552394).sum := by decide
  have hdescent : baseEnd_552394 < baseStart_552394 := by decide
  rcases family_descends (prefixWord ++ tailWord_552394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552421 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 2]
def baseStart_552421 : Nat := 118140960795 + 552421 * 2 ^ 59
def prefixEnd_552421 : Nat := 4983230072969 + 3 ^ 40 * 552421 * 2
def baseEnd_552421 : Nat := 252139997011100785775083

theorem tailTrace_552421 : CollatzResearch.WordTrace tailWord_552421 prefixEnd_552421 252139997011100785775083 := by
  unfold tailWord_552421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20148449131680537840641117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13432299421120358560427411 20148449131680537840641117)
  ·
    refine ⟨7555668424380201690240419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20148449131680537840641117 7555668424380201690240419)
    ·
      refine ⟨11333502636570302535360629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555668424380201690240419 11333502636570302535360629)
      ·
        refine ⟨1062515872178465862690059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11333502636570302535360629 1062515872178465862690059)
        ·
          refine ⟨1593773808267698794035089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062515872178465862690059 1593773808267698794035089)
          ·
            refine ⟨1195330356200774095526317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593773808267698794035089 1195330356200774095526317)
            ·
              refine ⟨448248883575290285822369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195330356200774095526317 448248883575290285822369)
              ·
                refine ⟨336186662681467714366777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448248883575290285822369 336186662681467714366777)
                ·
                  refine ⟨252139997011100785775083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336186662681467714366777 252139997011100785775083)
                  ·
                    rfl

theorem cell20_552421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_552421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552421 prefixEnd_552421 := by exact prefixLift 552421
  have htrace : WordTrace (prefixWord ++ tailWord_552421) baseStart_552421 baseEnd_552421 := by
    simpa [prefixWord, tailWord_552421, baseEnd_552421] using wordTrace_append hprefix tailTrace_552421
  have hstable : (prefixWord ++ tailWord_552421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552421).length < 2 ^ (prefixWord ++ tailWord_552421).sum := by decide
  have hdescent : baseEnd_552421 < baseStart_552421 := by decide
  rcases family_descends (prefixWord ++ tailWord_552421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552480 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_552480 : Nat := 118140960795 + 552480 * 2 ^ 59
def prefixEnd_552480 : Nat := 4983230072969 + 3 ^ 40 * 552480 * 2
def baseEnd_552480 : Nat := 252166926218758802808175

theorem tailTrace_552480 : CollatzResearch.WordTrace tailWord_552480 prefixEnd_552480 252166926218758802808175 := by
  unfold tailWord_552480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10075300519233395458519447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13433734025644527278025929 10075300519233395458519447)
  ·
    refine ⟨15112950778850093187779171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10075300519233395458519447 15112950778850093187779171)
    ·
      refine ⟨22669426168275139781668757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15112950778850093187779171 22669426168275139781668757)
      ·
        refine ⟨1062629351637897177265723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22669426168275139781668757 1062629351637897177265723)
        ·
          refine ⟨1593944027456845765898585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062629351637897177265723 1593944027456845765898585)
          ·
            refine ⟨1195458020592634324423939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593944027456845765898585 1195458020592634324423939)
            ·
              refine ⟨1793187030888951486635909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195458020592634324423939 1793187030888951486635909)
              ·
                refine ⟨336222568291678403744233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1793187030888951486635909 336222568291678403744233)
                ·
                  refine ⟨252166926218758802808175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336222568291678403744233 252166926218758802808175)
                  ·
                    rfl

theorem cell20_552480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_552480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552480 prefixEnd_552480 := by exact prefixLift 552480
  have htrace : WordTrace (prefixWord ++ tailWord_552480) baseStart_552480 baseEnd_552480 := by
    simpa [prefixWord, tailWord_552480, baseEnd_552480] using wordTrace_append hprefix tailTrace_552480
  have hstable : (prefixWord ++ tailWord_552480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552480).length < 2 ^ (prefixWord ++ tailWord_552480).sum := by decide
  have hdescent : baseEnd_552480 < baseStart_552480 := by decide
  rcases family_descends (prefixWord ++ tailWord_552480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552494 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_552494 : Nat := 118140960795 + 552494 * 2 ^ 59
def prefixEnd_552494 : Nat := 4983230072969 + 3 ^ 40 * 552494 * 2
def baseEnd_552494 : Nat := 252173316200236976341451

theorem tailTrace_552494 : CollatzResearch.WordTrace tailWord_552494 prefixEnd_552494 252173316200236976341451 := by
  unfold tailWord_552494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518888957552008913506067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13434074440277380872032357 2518888957552008913506067)
  ·
    refine ⟨3778333436328013370259101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518888957552008913506067 3778333436328013370259101)
    ·
      refine ⟨1416875038623005013847163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3778333436328013370259101 1416875038623005013847163)
      ·
        refine ⟨2125312557934507520770745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416875038623005013847163 2125312557934507520770745)
        ·
          refine ⟨1593984418450880640578059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125312557934507520770745 1593984418450880640578059)
          ·
            refine ⟨2390976627676320960867089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593984418450880640578059 2390976627676320960867089)
            ·
              refine ⟨1793232470757240720650317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390976627676320960867089 1793232470757240720650317)
              ·
                refine ⟨672462176533965270243869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1793232470757240720650317 672462176533965270243869)
                ·
                  refine ⟨252173316200236976341451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672462176533965270243869 252173316200236976341451)
                  ·
                    rfl

theorem cell20_552494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_552494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552494 prefixEnd_552494 := by exact prefixLift 552494
  have htrace : WordTrace (prefixWord ++ tailWord_552494) baseStart_552494 baseEnd_552494 := by
    simpa [prefixWord, tailWord_552494, baseEnd_552494] using wordTrace_append hprefix tailTrace_552494
  have hstable : (prefixWord ++ tailWord_552494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552494).length < 2 ^ (prefixWord ++ tailWord_552494).sum := by decide
  have hdescent : baseEnd_552494 < baseStart_552494 := by decide
  rcases family_descends (prefixWord ++ tailWord_552494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552498 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_552498 : Nat := 118140960795 + 552498 * 2 ^ 59
def prefixEnd_552498 : Nat := 4983230072969 + 3 ^ 40 * 552498 * 2
def baseEnd_552498 : Nat := 252175141909230740208101

theorem tailTrace_552498 : CollatzResearch.WordTrace tailWord_552498 prefixEnd_552498 252175141909230740208101 := by
  unfold tailWord_552498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037814388100394997798537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13434171701601053327462765 5037814388100394997798537)
  ·
    refine ⟨3778360791075296248348903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5037814388100394997798537 3778360791075296248348903)
    ·
      refine ⟨5667541186612944372523355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778360791075296248348903 5667541186612944372523355)
      ·
        refine ⟨8501311779919416558785033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667541186612944372523355 8501311779919416558785033)
        ·
          refine ⟨6375983834939562419088775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8501311779919416558785033 6375983834939562419088775)
          ·
            refine ⟨9563975752409343628633163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375983834939562419088775 9563975752409343628633163)
            ·
              refine ⟨14345963628614015442949745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9563975752409343628633163 14345963628614015442949745)
              ·
                refine ⟨10759472721460511582212309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14345963628614015442949745 10759472721460511582212309)
                ·
                  refine ⟨252175141909230740208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10759472721460511582212309 252175141909230740208101)
                  ·
                    rfl

theorem cell20_552498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_552498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552498 prefixEnd_552498 := by exact prefixLift 552498
  have htrace : WordTrace (prefixWord ++ tailWord_552498) baseStart_552498 baseEnd_552498 := by
    simpa [prefixWord, tailWord_552498, baseEnd_552498] using wordTrace_append hprefix tailTrace_552498
  have hstable : (prefixWord ++ tailWord_552498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552498).length < 2 ^ (prefixWord ++ tailWord_552498).sum := by decide
  have hdescent : baseEnd_552498 < baseStart_552498 := by decide
  rcases family_descends (prefixWord ++ tailWord_552498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552560 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_552560 : Nat := 118140960795 + 552560 * 2 ^ 59
def prefixEnd_552560 : Nat := 4983230072969 + 3 ^ 40 * 552560 * 2
def baseEnd_552560 : Nat := 252203440398634080141181

theorem tailTrace_552560 : CollatzResearch.WordTrace tailWord_552560 prefixEnd_552560 252203440398634080141181 := by
  unfold tailWord_552560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076759439088482289975567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13435679252117976386634089 10076759439088482289975567)
  ·
    refine ⟨15115139158632723434963351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10076759439088482289975567 15115139158632723434963351)
    ·
      refine ⟨22672708737949085152445027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15115139158632723434963351 22672708737949085152445027)
      ·
        refine ⟨34009063106923627728667541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22672708737949085152445027 34009063106923627728667541)
        ·
          refine ⟨1594174833137045049781291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34009063106923627728667541 1594174833137045049781291)
          ·
            refine ⟨2391262249705567574671937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594174833137045049781291 2391262249705567574671937)
            ·
              refine ⟨1793446687279175681003953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391262249705567574671937 1793446687279175681003953)
              ·
                refine ⟨1345085015459381760752965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793446687279175681003953 1345085015459381760752965)
                ·
                  refine ⟨252203440398634080141181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345085015459381760752965 252203440398634080141181)
                  ·
                    rfl

theorem cell20_552560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_552560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552560 prefixEnd_552560 := by exact prefixLift 552560
  have htrace : WordTrace (prefixWord ++ tailWord_552560) baseStart_552560 baseEnd_552560 := by
    simpa [prefixWord, tailWord_552560, baseEnd_552560] using wordTrace_append hprefix tailTrace_552560
  have hstable : (prefixWord ++ tailWord_552560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552560).length < 2 ^ (prefixWord ++ tailWord_552560).sum := by decide
  have hdescent : baseEnd_552560 < baseStart_552560 := by decide
  rcases family_descends (prefixWord ++ tailWord_552560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552594 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_552594 : Nat := 118140960795 + 552594 * 2 ^ 59
def prefixEnd_552594 : Nat := 4983230072969 + 3 ^ 40 * 552594 * 2
def baseEnd_552594 : Nat := 252218958925081073007709

theorem tailTrace_552594 : CollatzResearch.WordTrace tailWord_552594 prefixEnd_552594 252218958925081073007709 := by
  unfold tailWord_552594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038689740013447096672209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13436505973369192257792557 5038689740013447096672209)
  ·
    refine ⟨3779017305010085322504157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5038689740013447096672209 3779017305010085322504157)
    ·
      refine ⟨1417131489378781995939059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3779017305010085322504157 1417131489378781995939059)
      ·
        refine ⟨2125697234068172993908589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417131489378781995939059 2125697234068172993908589)
        ·
          refine ⟨797136462775564872715721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2125697234068172993908589 797136462775564872715721)
          ·
            refine ⟨597852347081673654536791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797136462775564872715721 597852347081673654536791)
            ·
              refine ⟨896778520622510481805187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597852347081673654536791 896778520622510481805187)
              ·
                refine ⟨1345167780933765722707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896778520622510481805187 1345167780933765722707781)
                ·
                  refine ⟨252218958925081073007709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345167780933765722707781 252218958925081073007709)
                  ·
                    rfl

theorem cell20_552594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_552594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552594 prefixEnd_552594 := by exact prefixLift 552594
  have htrace : WordTrace (prefixWord ++ tailWord_552594) baseStart_552594 baseEnd_552594 := by
    simpa [prefixWord, tailWord_552594, baseEnd_552594] using wordTrace_append hprefix tailTrace_552594
  have hstable : (prefixWord ++ tailWord_552594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552594).length < 2 ^ (prefixWord ++ tailWord_552594).sum := by decide
  have hdescent : baseEnd_552594 < baseStart_552594 := by decide
  rcases family_descends (prefixWord ++ tailWord_552594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552604 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_552604 : Nat := 118140960795 + 552604 * 2 ^ 59
def prefixEnd_552604 : Nat := 4983230072969 + 3 ^ 40 * 552604 * 2
def baseEnd_552604 : Nat := 252223523197565482674335

theorem tailTrace_552604 : CollatzResearch.WordTrace tailWord_552604 prefixEnd_552604 252223523197565482674335 := by
  unfold tailWord_552604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077561845008780047276433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13436749126678373396368577 10077561845008780047276433)
  ·
    refine ⟨7558171383756585035457325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10077561845008780047276433 7558171383756585035457325)
    ·
      refine ⟨2834314268908719388296497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7558171383756585035457325 2834314268908719388296497)
      ·
        refine ⟨2125735701681539541222373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2834314268908719388296497 2125735701681539541222373)
        ·
          refine ⟨398575444065288663979195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2125735701681539541222373 398575444065288663979195)
          ·
            refine ⟨597863166097932995968793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398575444065288663979195 597863166097932995968793)
            ·
              refine ⟨448397374573449746976595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597863166097932995968793 448397374573449746976595)
              ·
                refine ⟨672596061860174620464893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448397374573449746976595 672596061860174620464893)
                ·
                  refine ⟨252223523197565482674335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672596061860174620464893 252223523197565482674335)
                  ·
                    rfl

theorem cell20_552604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_552604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552604 prefixEnd_552604 := by exact prefixLift 552604
  have htrace : WordTrace (prefixWord ++ tailWord_552604) baseStart_552604 baseEnd_552604 := by
    simpa [prefixWord, tailWord_552604, baseEnd_552604] using wordTrace_append hprefix tailTrace_552604
  have hstable : (prefixWord ++ tailWord_552604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552604).length < 2 ^ (prefixWord ++ tailWord_552604).sum := by decide
  have hdescent : baseEnd_552604 < baseStart_552604 := by decide
  rcases family_descends (prefixWord ++ tailWord_552604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552608 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_552608 : Nat := 118140960795 + 552608 * 2 ^ 59
def prefixEnd_552608 : Nat := 4983230072969 + 3 ^ 40 * 552608 * 2
def baseEnd_552608 : Nat := 252225348906559246540985

theorem tailTrace_552608 : CollatzResearch.WordTrace tailWord_552608 prefixEnd_552608 252225348906559246540985 := by
  unfold tailWord_552608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077634791001534388849239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13436846388002045851798985 10077634791001534388849239)
  ·
    refine ⟨15116452186502301583273859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10077634791001534388849239 15116452186502301583273859)
    ·
      refine ⟨22674678279753452374910789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15116452186502301583273859 22674678279753452374910789)
      ·
        refine ⟨4251502177453772320295773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22674678279753452374910789 4251502177453772320295773)
        ·
          refine ⟨1594313316545164620110915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4251502177453772320295773 1594313316545164620110915)
          ·
            refine ⟨2391469974817746930166373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594313316545164620110915 2391469974817746930166373)
            ·
              refine ⟨448400620278327549406195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2391469974817746930166373 448400620278327549406195)
              ·
                refine ⟨672600930417491324109293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448400620278327549406195 672600930417491324109293)
                ·
                  refine ⟨252225348906559246540985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672600930417491324109293 252225348906559246540985)
                  ·
                    rfl

theorem cell20_552608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_552608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552608 prefixEnd_552608 := by exact prefixLift 552608
  have htrace : WordTrace (prefixWord ++ tailWord_552608) baseStart_552608 baseEnd_552608 := by
    simpa [prefixWord, tailWord_552608, baseEnd_552608] using wordTrace_append hprefix tailTrace_552608
  have hstable : (prefixWord ++ tailWord_552608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552608).length < 2 ^ (prefixWord ++ tailWord_552608).sum := by decide
  have hdescent : baseEnd_552608 < baseStart_552608 := by decide
  rcases family_descends (prefixWord ++ tailWord_552608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552660 : List Nat := [2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_552660 : Nat := 118140960795 + 552660 * 2 ^ 59
def prefixEnd_552660 : Nat := 4983230072969 + 3 ^ 40 * 552660 * 2
def baseEnd_552660 : Nat := 84083027707826058935813

theorem tailTrace_552660 : CollatzResearch.WordTrace tailWord_552660 prefixEnd_552660 84083027707826058935813 := by
  unfold tailWord_552660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078583088907340829295717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13438110785209787772394289 10078583088907340829295717)
  ·
    refine ⟨1889734329170126405492947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10078583088907340829295717 1889734329170126405492947)
    ·
      refine ⟨2834601493755189608239421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889734329170126405492947 2834601493755189608239421)
      ·
        refine ⟨1062975560158196103089783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2834601493755189608239421 1062975560158196103089783)
        ·
          refine ⟨1594463340237294154634675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062975560158196103089783 1594463340237294154634675)
          ·
            refine ⟨2391695010355941231952013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594463340237294154634675 2391695010355941231952013)
            ·
              refine ⟨896885628883477961982005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2391695010355941231952013 896885628883477961982005)
              ·
                refine ⟨84083027707826058935813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 896885628883477961982005 84083027707826058935813)
                ·
                  rfl

theorem cell20_552660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_552660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552660 prefixEnd_552660 := by exact prefixLift 552660
  have htrace : WordTrace (prefixWord ++ tailWord_552660) baseStart_552660 baseEnd_552660 := by
    simpa [prefixWord, tailWord_552660, baseEnd_552660] using wordTrace_append hprefix tailTrace_552660
  have hstable : (prefixWord ++ tailWord_552660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552660).length < 2 ^ (prefixWord ++ tailWord_552660).sum := by decide
  have hdescent : baseEnd_552660 < baseStart_552660 := by decide
  rcases family_descends (prefixWord ++ tailWord_552660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552705 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_552705 : Nat := 118140960795 + 552705 * 2 ^ 59
def prefixEnd_552705 : Nat := 4983230072969 + 3 ^ 40 * 552705 * 2
def baseEnd_552705 : Nat := 252269622349658020307255

theorem tailTrace_552705 : CollatzResearch.WordTrace tailWord_552705 prefixEnd_552705 252269622349658020307255 := by
  unfold tailWord_552705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20158807462651654343979569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13439204975101102895986379 20158807462651654343979569)
  ·
    refine ⟨15119105596988740757984677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20158807462651654343979569 15119105596988740757984677)
    ·
      refine ⟨2834832299435388892122127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15119105596988740757984677 2834832299435388892122127)
      ·
        refine ⟨4252248449153083338183191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834832299435388892122127 4252248449153083338183191)
        ·
          refine ⟨6378372673729625007274787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4252248449153083338183191 6378372673729625007274787)
          ·
            refine ⟨9567559010594437510912181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378372673729625007274787 9567559010594437510912181)
            ·
              refine ⟨896958657243228516648017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9567559010594437510912181 896958657243228516648017)
              ·
                refine ⟨672718992932421387486013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896958657243228516648017 672718992932421387486013)
                ·
                  refine ⟨252269622349658020307255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672718992932421387486013 252269622349658020307255)
                  ·
                    rfl

theorem cell20_552705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_552705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552705 prefixEnd_552705 := by exact prefixLift 552705
  have htrace : WordTrace (prefixWord ++ tailWord_552705) baseStart_552705 baseEnd_552705 := by
    simpa [prefixWord, tailWord_552705, baseEnd_552705] using wordTrace_append hprefix tailTrace_552705
  have hstable : (prefixWord ++ tailWord_552705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552705).length < 2 ^ (prefixWord ++ tailWord_552705).sum := by decide
  have hdescent : baseEnd_552705 < baseStart_552705 := by decide
  rcases family_descends (prefixWord ++ tailWord_552705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552712 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_552712 : Nat := 118140960795 + 552712 * 2 ^ 59
def prefixEnd_552712 : Nat := 4983230072969 + 3 ^ 40 * 552712 * 2
def baseEnd_552712 : Nat := 252272817340397107073893

theorem tailTrace_552712 : CollatzResearch.WordTrace tailWord_552712 prefixEnd_552712 252272817340397107073893 := by
  unfold tailWord_552712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079531386813147269742195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13439375182417529692989593 10079531386813147269742195)
  ·
    refine ⟨15119297080219720904613293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079531386813147269742195 15119297080219720904613293)
    ·
      refine ⟨5669736405082395339229985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15119297080219720904613293 5669736405082395339229985)
      ·
        refine ⟨4252302303811796504422489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5669736405082395339229985 4252302303811796504422489)
        ·
          refine ⟨3189226727858847378316867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4252302303811796504422489 3189226727858847378316867)
          ·
            refine ⟨4783840091788271067475301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189226727858847378316867 4783840091788271067475301)
            ·
              refine ⟨896970017210300825151619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4783840091788271067475301 896970017210300825151619)
              ·
                refine ⟨1345455025815451237727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896970017210300825151619 1345455025815451237727429)
                ·
                  refine ⟨252272817340397107073893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345455025815451237727429 252272817340397107073893)
                  ·
                    rfl

theorem cell20_552712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_552712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552712 prefixEnd_552712 := by exact prefixLift 552712
  have htrace : WordTrace (prefixWord ++ tailWord_552712) baseStart_552712 baseEnd_552712 := by
    simpa [prefixWord, tailWord_552712, baseEnd_552712] using wordTrace_append hprefix tailTrace_552712
  have hstable : (prefixWord ++ tailWord_552712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552712).length < 2 ^ (prefixWord ++ tailWord_552712).sum := by decide
  have hdescent : baseEnd_552712 < baseStart_552712 := by decide
  rcases family_descends (prefixWord ++ tailWord_552712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552764 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_552764 : Nat := 118140960795 + 552764 * 2 ^ 59
def prefixEnd_552764 : Nat := 4983230072969 + 3 ^ 40 * 552764 * 2
def baseEnd_552764 : Nat := 252296551557316037340347

theorem tailTrace_552764 : CollatzResearch.WordTrace tailWord_552764 prefixEnd_552764 252296551557316037340347 := by
  unfold tailWord_552764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080479684718953710188673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13440639579625271613584897 10080479684718953710188673)
  ·
    refine ⟨7560359763539215282641505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10080479684718953710188673 7560359763539215282641505)
    ·
      refine ⟨5670269822654411461981129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7560359763539215282641505 5670269822654411461981129)
      ·
        refine ⟨4252702366990808596485847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5670269822654411461981129 4252702366990808596485847)
        ·
          refine ⟨6379053550486212894728771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4252702366990808596485847 6379053550486212894728771)
          ·
            refine ⟨9568580325729319342093157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379053550486212894728771 9568580325729319342093157)
            ·
              refine ⟨1794108811074247376642467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9568580325729319342093157 1794108811074247376642467)
              ·
                refine ⟨2691163216611371064963701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794108811074247376642467 2691163216611371064963701)
                ·
                  refine ⟨252296551557316037340347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2691163216611371064963701 252296551557316037340347)
                  ·
                    rfl

theorem cell20_552764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_552764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552764 prefixEnd_552764 := by exact prefixLift 552764
  have htrace : WordTrace (prefixWord ++ tailWord_552764) baseStart_552764 baseEnd_552764 := by
    simpa [prefixWord, tailWord_552764, baseEnd_552764] using wordTrace_append hprefix tailTrace_552764
  have hstable : (prefixWord ++ tailWord_552764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552764).length < 2 ^ (prefixWord ++ tailWord_552764).sum := by decide
  have hdescent : baseEnd_552764 < baseStart_552764 := by decide
  rcases family_descends (prefixWord ++ tailWord_552764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552767 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_552767 : Nat := 118140960795 + 552767 * 2 ^ 59
def prefixEnd_552767 : Nat := 4983230072969 + 3 ^ 40 * 552767 * 2
def baseEnd_552767 : Nat := 252297920839061360240335

theorem tailTrace_552767 : CollatzResearch.WordTrace tailWord_552767 prefixEnd_552767 252297920839061360240335 := by
  unfold tailWord_552767
  simp only [CollatzResearch.WordTrace]
  refine ⟨20161068788427038932736555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13440712525618025955157703 20161068788427038932736555)
  ·
    refine ⟨30241603182640558399104833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20161068788427038932736555 30241603182640558399104833)
    ·
      refine ⟨22681202386980418799328625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30241603182640558399104833 22681202386980418799328625)
      ·
        refine ⟨17010901790235314099496469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22681202386980418799328625 17010901790235314099496469)
        ·
          refine ⟨797386021417280348413897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17010901790235314099496469 797386021417280348413897)
          ·
            refine ⟨598039516062960261310423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797386021417280348413897 598039516062960261310423)
            ·
              refine ⟨897059274094440391965635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598039516062960261310423 897059274094440391965635)
              ·
                refine ⟨1345588911141660587948453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897059274094440391965635 1345588911141660587948453)
                ·
                  refine ⟨252297920839061360240335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345588911141660587948453 252297920839061360240335)
                  ·
                    rfl

theorem cell20_552767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_552767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552767 prefixEnd_552767 := by exact prefixLift 552767
  have htrace : WordTrace (prefixWord ++ tailWord_552767) baseStart_552767 baseEnd_552767 := by
    simpa [prefixWord, tailWord_552767, baseEnd_552767] using wordTrace_append hprefix tailTrace_552767
  have hstable : (prefixWord ++ tailWord_552767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552767).length < 2 ^ (prefixWord ++ tailWord_552767).sum := by decide
  have hdescent : baseEnd_552767 < baseStart_552767 := by decide
  rcases family_descends (prefixWord ++ tailWord_552767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552860 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_552860 : Nat := 118140960795 + 552860 * 2 ^ 59
def prefixEnd_552860 : Nat := 4983230072969 + 3 ^ 40 * 552860 * 2
def baseEnd_552860 : Nat := 252340368573166370139955

theorem tailTrace_552860 : CollatzResearch.WordTrace tailWord_552860 prefixEnd_552860 252340368573166370139955 := by
  unfold tailWord_552860
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082230388545057907936017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13442973851393410543914689 10082230388545057907936017)
  ·
    refine ⟨7561672791408793430952013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10082230388545057907936017 7561672791408793430952013)
    ·
      refine ⟨2835627296778297536607005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7561672791408793430952013 2835627296778297536607005)
      ·
        refine ⟨1063360236291861576227627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2835627296778297536607005 1063360236291861576227627)
        ·
          refine ⟨1595040354437792364341441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063360236291861576227627 1595040354437792364341441)
          ·
            refine ⟨1196280265828344273256081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595040354437792364341441 1196280265828344273256081)
            ·
              refine ⟨897210199371258204942061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196280265828344273256081 897210199371258204942061)
              ·
                refine ⟨336453824764221826853273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897210199371258204942061 336453824764221826853273)
                ·
                  refine ⟨252340368573166370139955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336453824764221826853273 252340368573166370139955)
                  ·
                    rfl

theorem cell20_552860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_552860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552860 prefixEnd_552860 := by exact prefixLift 552860
  have htrace : WordTrace (prefixWord ++ tailWord_552860) baseStart_552860 baseEnd_552860 := by
    simpa [prefixWord, tailWord_552860, baseEnd_552860] using wordTrace_append hprefix tailTrace_552860
  have hstable : (prefixWord ++ tailWord_552860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552860).length < 2 ^ (prefixWord ++ tailWord_552860).sum := by decide
  have hdescent : baseEnd_552860 < baseStart_552860 := by decide
  rcases family_descends (prefixWord ++ tailWord_552860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552871 : List Nat := [1, 1, 6, 1, 2, 2, 7]
def baseStart_552871 : Nat := 118140960795 + 552871 * 2 ^ 59
def prefixEnd_552871 : Nat := 4983230072969 + 3 ^ 40 * 552871 * 2
def baseEnd_552871 : Nat := 28038376585877691197027

theorem tailTrace_552871 : CollatzResearch.WordTrace tailWord_552871 prefixEnd_552871 28038376585877691197027 := by
  unfold tailWord_552871
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164861980050264694522467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443241320033509796348311 20164861980050264694522467)
  ·
    refine ⟨30247292970075397041783701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20164861980050264694522467 30247292970075397041783701)
    ·
      refine ⟨1417841857972284236333611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30247292970075397041783701 1417841857972284236333611)
      ·
        refine ⟨2126762786958426354500417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417841857972284236333611 2126762786958426354500417)
        ·
          refine ⟨1595072090218819765875313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126762786958426354500417 1595072090218819765875313)
          ·
            refine ⟨1196304067664114824406485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595072090218819765875313 1196304067664114824406485)
            ·
              refine ⟨28038376585877691197027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1196304067664114824406485 28038376585877691197027)
              ·
                rfl

theorem cell20_552871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_552871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552871 prefixEnd_552871 := by exact prefixLift 552871
  have htrace : WordTrace (prefixWord ++ tailWord_552871) baseStart_552871 baseEnd_552871 := by
    simpa [prefixWord, tailWord_552871, baseEnd_552871] using wordTrace_append hprefix tailTrace_552871
  have hstable : (prefixWord ++ tailWord_552871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552871).length < 2 ^ (prefixWord ++ tailWord_552871).sum := by decide
  have hdescent : baseEnd_552871 < baseStart_552871 := by decide
  rcases family_descends (prefixWord ++ tailWord_552871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552881 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 2]
def baseStart_552881 : Nat := 118140960795 + 552881 * 2 ^ 59
def prefixEnd_552881 : Nat := 4983230072969 + 3 ^ 40 * 552881 * 2
def baseEnd_552881 : Nat := 252349953545383630439869

theorem tailTrace_552881 : CollatzResearch.WordTrace tailWord_552881 prefixEnd_552881 252349953545383630439869 := by
  unfold tailWord_552881
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165226710014036402386497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443484473342690934924331 20165226710014036402386497)
  ·
    refine ⟨15123920032510527301789873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20165226710014036402386497 15123920032510527301789873)
    ·
      refine ⟨11342940024382895476342405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15123920032510527301789873 11342940024382895476342405)
      ·
        refine ⟨2126801254571792901814201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11342940024382895476342405 2126801254571792901814201)
        ·
          refine ⟨1595100940928844676360651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126801254571792901814201 1595100940928844676360651)
          ·
            refine ⟨2392651411393267014540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595100940928844676360651 2392651411393267014540977)
            ·
              refine ⟨1794488558544950260905733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392651411393267014540977 1794488558544950260905733)
              ·
                refine ⟨336466604727178173919825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1794488558544950260905733 336466604727178173919825)
                ·
                  refine ⟨252349953545383630439869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336466604727178173919825 252349953545383630439869)
                  ·
                    rfl

theorem cell20_552881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_552881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552881 prefixEnd_552881 := by exact prefixLift 552881
  have htrace : WordTrace (prefixWord ++ tailWord_552881) baseStart_552881 baseEnd_552881 := by
    simpa [prefixWord, tailWord_552881, baseEnd_552881] using wordTrace_append hprefix tailTrace_552881
  have hstable : (prefixWord ++ tailWord_552881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552881).length < 2 ^ (prefixWord ++ tailWord_552881).sum := by decide
  have hdescent : baseEnd_552881 < baseStart_552881 := by decide
  rcases family_descends (prefixWord ++ tailWord_552881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552895 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_552895 : Nat := 118140960795 + 552895 * 2 ^ 59
def prefixEnd_552895 : Nat := 4983230072969 + 3 ^ 40 * 552895 * 2
def baseEnd_552895 : Nat := 252356343526861803973145

theorem tailTrace_552895 : CollatzResearch.WordTrace tailWord_552895 prefixEnd_552895 252356343526861803973145 := by
  unfold tailWord_552895
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165737331963316793396139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443824887975544528930759 20165737331963316793396139)
  ·
    refine ⟨30248605997944975190094209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20165737331963316793396139 30248605997944975190094209)
    ·
      refine ⟨22686454498458731392570657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30248605997944975190094209 22686454498458731392570657)
      ·
        refine ⟨17014840873844048544427993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22686454498458731392570657 17014840873844048544427993)
        ·
          refine ⟨12761130655383036408320995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17014840873844048544427993 12761130655383036408320995)
          ·
            refine ⟨19141695983074554612481493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12761130655383036408320995 19141695983074554612481493)
            ·
              refine ⟨448633499603309873730035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19141695983074554612481493 448633499603309873730035)
              ·
                refine ⟨672950249404964810595053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448633499603309873730035 672950249404964810595053)
                ·
                  refine ⟨252356343526861803973145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672950249404964810595053 252356343526861803973145)
                  ·
                    rfl

theorem cell20_552895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_552895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552895 prefixEnd_552895 := by exact prefixLift 552895
  have htrace : WordTrace (prefixWord ++ tailWord_552895) baseStart_552895 baseEnd_552895 := by
    simpa [prefixWord, tailWord_552895, baseEnd_552895] using wordTrace_append hprefix tailTrace_552895
  have hstable : (prefixWord ++ tailWord_552895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552895).length < 2 ^ (prefixWord ++ tailWord_552895).sum := by decide
  have hdescent : baseEnd_552895 < baseStart_552895 := by decide
  rcases family_descends (prefixWord ++ tailWord_552895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552899 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_552899 : Nat := 118140960795 + 552899 * 2 ^ 59
def prefixEnd_552899 : Nat := 4983230072969 + 3 ^ 40 * 552899 * 2
def baseEnd_552899 : Nat := 252358169235855567839795

theorem tailTrace_552899 : CollatzResearch.WordTrace tailWord_552899 prefixEnd_552899 252358169235855567839795 := by
  unfold tailWord_552899
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165883223948825476541751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443922149299216984361167 20165883223948825476541751)
  ·
    refine ⟨30248824835923238214812627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20165883223948825476541751 30248824835923238214812627)
    ·
      refine ⟨45373237253884857322218941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30248824835923238214812627 45373237253884857322218941)
      ·
        refine ⟨17014963970206821495832103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45373237253884857322218941 17014963970206821495832103)
        ·
          refine ⟨25522445955310232243748155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17014963970206821495832103 25522445955310232243748155)
          ·
            refine ⟨38283668932965348365622233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25522445955310232243748155 38283668932965348365622233)
            ·
              refine ⟨28712751699724011274216675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38283668932965348365622233 28712751699724011274216675)
              ·
                refine ⟨43069127549586016911325013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28712751699724011274216675 43069127549586016911325013)
                ·
                  refine ⟨252358169235855567839795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43069127549586016911325013 252358169235855567839795)
                  ·
                    rfl

theorem cell20_552899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_552899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552899 prefixEnd_552899 := by exact prefixLift 552899
  have htrace : WordTrace (prefixWord ++ tailWord_552899) baseStart_552899 baseEnd_552899 := by
    simpa [prefixWord, tailWord_552899, baseEnd_552899] using wordTrace_append hprefix tailTrace_552899
  have hstable : (prefixWord ++ tailWord_552899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552899).length < 2 ^ (prefixWord ++ tailWord_552899).sum := by decide
  have hdescent : baseEnd_552899 < baseStart_552899 := by decide
  rcases family_descends (prefixWord ++ tailWord_552899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552916 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_552916 : Nat := 118140960795 + 552916 * 2 ^ 59
def prefixEnd_552916 : Nat := 4983230072969 + 3 ^ 40 * 552916 * 2
def baseEnd_552916 : Nat := 252365928499079064273059

theorem tailTrace_552916 : CollatzResearch.WordTrace tailWord_552916 prefixEnd_552916 252365928499079064273059 := by
  unfold tailWord_552916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083251632443618689955301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13444335509924824919940401 10083251632443618689955301)
  ·
    refine ⟨1890609681083178504366619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10083251632443618689955301 1890609681083178504366619)
    ·
      refine ⟨2835914521624767756549929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890609681083178504366619 2835914521624767756549929)
      ·
        refine ⟨2126935891218575817412447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2835914521624767756549929 2126935891218575817412447)
        ·
          refine ⟨3190403836827863726118671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126935891218575817412447 3190403836827863726118671)
          ·
            refine ⟨4785605755241795589178007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190403836827863726118671 4785605755241795589178007)
            ·
              refine ⟨7178408632862693383767011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785605755241795589178007 7178408632862693383767011)
              ·
                refine ⟨10767612949294040075650517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7178408632862693383767011 10767612949294040075650517)
                ·
                  refine ⟨252365928499079064273059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10767612949294040075650517 252365928499079064273059)
                  ·
                    rfl

theorem cell20_552916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_552916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552916 prefixEnd_552916 := by exact prefixLift 552916
  have htrace : WordTrace (prefixWord ++ tailWord_552916) baseStart_552916 baseEnd_552916 := by
    simpa [prefixWord, tailWord_552916, baseEnd_552916] using wordTrace_append hprefix tailTrace_552916
  have hstable : (prefixWord ++ tailWord_552916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552916).length < 2 ^ (prefixWord ++ tailWord_552916).sum := by decide
  have hdescent : baseEnd_552916 < baseStart_552916 := by decide
  rcases family_descends (prefixWord ++ tailWord_552916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552940 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_552940 : Nat := 118140960795 + 552940 * 2 ^ 59
def prefixEnd_552940 : Nat := 4983230072969 + 3 ^ 40 * 552940 * 2
def baseEnd_552940 : Nat := 252376882753041647472961

theorem tailTrace_552940 : CollatzResearch.WordTrace tailWord_552940 prefixEnd_552940 252376882753041647472961 := by
  unfold tailWord_552940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083689308400144739392137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13444919077866859652522849 10083689308400144739392137)
  ·
    refine ⟨7562766981300108554544103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10083689308400144739392137 7562766981300108554544103)
    ·
      refine ⟨11344150471950162831816155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7562766981300108554544103 11344150471950162831816155)
      ·
        refine ⟨17016225707925244247724233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11344150471950162831816155 17016225707925244247724233)
        ·
          refine ⟨12762169280943933185793175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17016225707925244247724233 12762169280943933185793175)
          ·
            refine ⟨19143253921415899778689763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12762169280943933185793175 19143253921415899778689763)
            ·
              refine ⟨28714880882123849668034645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19143253921415899778689763 28714880882123849668034645)
              ·
                refine ⟨336502510337388863297281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28714880882123849668034645 336502510337388863297281)
                ·
                  refine ⟨252376882753041647472961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336502510337388863297281 252376882753041647472961)
                  ·
                    rfl

theorem cell20_552940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_552940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552940 prefixEnd_552940 := by exact prefixLift 552940
  have htrace : WordTrace (prefixWord ++ tailWord_552940) baseStart_552940 baseEnd_552940 := by
    simpa [prefixWord, tailWord_552940, baseEnd_552940] using wordTrace_append hprefix tailTrace_552940
  have hstable : (prefixWord ++ tailWord_552940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552940).length < 2 ^ (prefixWord ++ tailWord_552940).sum := by decide
  have hdescent : baseEnd_552940 < baseStart_552940 := by decide
  rcases family_descends (prefixWord ++ tailWord_552940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552950 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_552950 : Nat := 118140960795 + 552950 * 2 ^ 59
def prefixEnd_552950 : Nat := 4983230072969 + 3 ^ 40 * 552950 * 2
def baseEnd_552950 : Nat := 252381447025526057139587

theorem tailTrace_552950 : CollatzResearch.WordTrace tailWord_552950 prefixEnd_552950 252381447025526057139587 := by
  unfold tailWord_552950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260483959172753824165519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13445162231176040791098869 1260483959172753824165519)
  ·
    refine ⟨1890725938759130736248279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260483959172753824165519 1890725938759130736248279)
    ·
      refine ⟨2836088908138696104372419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890725938759130736248279 2836088908138696104372419)
      ·
        refine ⟨4254133362208044156558629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836088908138696104372419 4254133362208044156558629)
        ·
          refine ⟨797650005414008279354743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4254133362208044156558629 797650005414008279354743)
          ·
            refine ⟨1196475008121012419032115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797650005414008279354743 1196475008121012419032115)
            ·
              refine ⟨1794712512181518628548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196475008121012419032115 1794712512181518628548173)
              ·
                refine ⟨673017192068069485705565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1794712512181518628548173 673017192068069485705565)
                ·
                  refine ⟨252381447025526057139587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673017192068069485705565 252381447025526057139587)
                  ·
                    rfl

theorem cell20_552950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_552950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552950 prefixEnd_552950 := by exact prefixLift 552950
  have htrace : WordTrace (prefixWord ++ tailWord_552950) baseStart_552950 baseEnd_552950 := by
    simpa [prefixWord, tailWord_552950, baseEnd_552950] using wordTrace_append hprefix tailTrace_552950
  have hstable : (prefixWord ++ tailWord_552950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552950).length < 2 ^ (prefixWord ++ tailWord_552950).sum := by decide
  have hdescent : baseEnd_552950 < baseStart_552950 := by decide
  rcases family_descends (prefixWord ++ tailWord_552950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552961 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_552961 : Nat := 118140960795 + 552961 * 2 ^ 59
def prefixEnd_552961 : Nat := 4983230072969 + 3 ^ 40 * 552961 * 2
def baseEnd_552961 : Nat := 252386467725258907772875

theorem tailTrace_552961 : CollatzResearch.WordTrace tailWord_552961 prefixEnd_552961 252386467725258907772875 := by
  unfold tailWord_552961
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168144549724210065298737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13445429699816140043532491 20168144549724210065298737)
  ·
    refine ⟨15126108412293157548974053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20168144549724210065298737 15126108412293157548974053)
    ·
      refine ⟨2836145327304967040432635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15126108412293157548974053 2836145327304967040432635)
      ·
        refine ⟨4254217990957450560648953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836145327304967040432635 4254217990957450560648953)
        ·
          refine ⟨3190663493218087920486715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254217990957450560648953 3190663493218087920486715)
          ·
            refine ⟨4785995239827131880730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190663493218087920486715 4785995239827131880730073)
            ·
              refine ⟨3589496429870348910547555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785995239827131880730073 3589496429870348910547555)
              ·
                refine ⟨5384244644805523365821333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589496429870348910547555 5384244644805523365821333)
                ·
                  refine ⟨252386467725258907772875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5384244644805523365821333 252386467725258907772875)
                  ·
                    rfl

theorem cell20_552961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_552961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552961 prefixEnd_552961 := by exact prefixLift 552961
  have htrace : WordTrace (prefixWord ++ tailWord_552961) baseStart_552961 baseEnd_552961 := by
    simpa [prefixWord, tailWord_552961, baseEnd_552961] using wordTrace_append hprefix tailTrace_552961
  have hstable : (prefixWord ++ tailWord_552961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552961).length < 2 ^ (prefixWord ++ tailWord_552961).sum := by decide
  have hdescent : baseEnd_552961 < baseStart_552961 := by decide
  rcases family_descends (prefixWord ++ tailWord_552961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552968 : List Nat := [2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_552968 : Nat := 118140960795 + 552968 * 2 ^ 59
def prefixEnd_552968 : Nat := 4983230072969 + 3 ^ 40 * 552968 * 2
def baseEnd_552968 : Nat := 84129887571999331513171

theorem tailTrace_552968 : CollatzResearch.WordTrace tailWord_552968 prefixEnd_552968 84129887571999331513171 := by
  unfold tailWord_552968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084199930349425130401779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13445599907132566840535705 10084199930349425130401779)
  ·
    refine ⟨15126299895524137695602669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10084199930349425130401779 15126299895524137695602669)
    ·
      refine ⟨5672362460821551635851001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15126299895524137695602669 5672362460821551635851001)
      ·
        refine ⟨4254271845616163726888251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5672362460821551635851001 4254271845616163726888251)
        ·
          refine ⟨6381407768424245590332377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254271845616163726888251 6381407768424245590332377)
          ·
            refine ⟨4786055826318184192749283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381407768424245590332377 4786055826318184192749283)
            ·
              refine ⟨7179083739477276289123925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786055826318184192749283 7179083739477276289123925)
              ·
                refine ⟨84129887571999331513171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7179083739477276289123925 84129887571999331513171)
                ·
                  rfl

theorem cell20_552968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_552968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_552968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_552968 prefixEnd_552968 := by exact prefixLift 552968
  have htrace : WordTrace (prefixWord ++ tailWord_552968) baseStart_552968 baseEnd_552968 := by
    simpa [prefixWord, tailWord_552968, baseEnd_552968] using wordTrace_append hprefix tailTrace_552968
  have hstable : (prefixWord ++ tailWord_552968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552968).length < 2 ^ (prefixWord ++ tailWord_552968).sum := by decide
  have hdescent : baseEnd_552968 < baseStart_552968 := by decide
  rcases family_descends (prefixWord ++ tailWord_552968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553002 : List Nat := [3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_553002 : Nat := 118140960795 + 553002 * 2 ^ 59
def prefixEnd_553002 : Nat := 4983230072969 + 3 ^ 40 * 553002 * 2
def baseEnd_553002 : Nat := 84135060414148329135347

theorem tailTrace_553002 : CollatzResearch.WordTrace tailWord_553002 prefixEnd_553002 84135060414148329135347 := by
  unfold tailWord_553002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042409985643918516885315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13446426628383782711694173 5042409985643918516885315)
  ·
    refine ⟨7563614978465877775327973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5042409985643918516885315 7563614978465877775327973)
    ·
      refine ⟨1418177808462352082873995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7563614978465877775327973 1418177808462352082873995)
      ·
        refine ⟨2127266712693528124310993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418177808462352082873995 2127266712693528124310993)
        ·
          refine ⟨1595450034520146093233245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127266712693528124310993 1595450034520146093233245)
          ·
            refine ⟨598293762945054784962467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1595450034520146093233245 598293762945054784962467)
            ·
              refine ⟨897440644417582177443701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598293762945054784962467 897440644417582177443701)
              ·
                refine ⟨84135060414148329135347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897440644417582177443701 84135060414148329135347)
                ·
                  rfl

theorem cell20_553002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_553002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553002 prefixEnd_553002 := by exact prefixLift 553002
  have htrace : WordTrace (prefixWord ++ tailWord_553002) baseStart_553002 baseEnd_553002 := by
    simpa [prefixWord, tailWord_553002, baseEnd_553002] using wordTrace_append hprefix tailTrace_553002
  have hstable : (prefixWord ++ tailWord_553002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553002).length < 2 ^ (prefixWord ++ tailWord_553002).sum := by decide
  have hdescent : baseEnd_553002 < baseStart_553002 := by decide
  rcases family_descends (prefixWord ++ tailWord_553002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553016 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_553016 : Nat := 118140960795 + 553016 * 2 ^ 59
def prefixEnd_553016 : Nat := 4983230072969 + 3 ^ 40 * 553016 * 2
def baseEnd_553016 : Nat := 252411571223923160939317

theorem tailTrace_553016 : CollatzResearch.WordTrace tailWord_553016 prefixEnd_553016 252411571223923160939317 := by
  unfold tailWord_553016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085075282262477229275451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13446767043016636305700601 10085075282262477229275451)
  ·
    refine ⟨15127612923393715843913177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10085075282262477229275451 15127612923393715843913177)
    ·
      refine ⟨11345709692545286882934883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15127612923393715843913177 11345709692545286882934883)
      ·
        refine ⟨17018564538817930324402325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11345709692545286882934883 17018564538817930324402325)
        ·
          refine ⟨797745212757090483956359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17018564538817930324402325 797745212757090483956359)
          ·
            refine ⟨1196617819135635725934539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797745212757090483956359 1196617819135635725934539)
            ·
              refine ⟨1794926728703453588901809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196617819135635725934539 1794926728703453588901809)
              ·
                refine ⟨1346195046527590191676357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794926728703453588901809 1346195046527590191676357)
                ·
                  refine ⟨252411571223923160939317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346195046527590191676357 252411571223923160939317)
                  ·
                    rfl

theorem cell20_553016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_553016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553016 prefixEnd_553016 := by exact prefixLift 553016
  have htrace : WordTrace (prefixWord ++ tailWord_553016) baseStart_553016 baseEnd_553016 := by
    simpa [prefixWord, tailWord_553016, baseEnd_553016] using wordTrace_append hprefix tailTrace_553016
  have hstable : (prefixWord ++ tailWord_553016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553016).length < 2 ^ (prefixWord ++ tailWord_553016).sum := by decide
  have hdescent : baseEnd_553016 < baseStart_553016 := by decide
  rcases family_descends (prefixWord ++ tailWord_553016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553078 : List Nat := [5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_553078 : Nat := 118140960795 + 553078 * 2 ^ 59
def prefixEnd_553078 : Nat := 4983230072969 + 3 ^ 40 * 553078 * 2
def baseEnd_553078 : Nat := 84146623237775500290799

theorem tailTrace_553078 : CollatzResearch.WordTrace tailWord_553078 prefixEnd_553078 84146623237775500290799 := by
  unfold tailWord_553078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260775743143771190456743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13448274593533559364871925 1260775743143771190456743)
  ·
    refine ⟨1891163614715656785685115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260775743143771190456743 1891163614715656785685115)
    ·
      refine ⟨2836745422073485178527673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891163614715656785685115 2836745422073485178527673)
      ·
        refine ⟨2127559066555113883895755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836745422073485178527673 2127559066555113883895755)
        ·
          refine ⟨3191338599832670825843633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127559066555113883895755 3191338599832670825843633)
          ·
            refine ⟨2393503949874503119382725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191338599832670825843633 2393503949874503119382725)
            ·
              refine ⟨448781990601469334884261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2393503949874503119382725 448781990601469334884261)
              ·
                refine ⟨84146623237775500290799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448781990601469334884261 84146623237775500290799)
                ·
                  rfl

theorem cell20_553078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_553078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553078 prefixEnd_553078 := by exact prefixLift 553078
  have htrace : WordTrace (prefixWord ++ tailWord_553078) baseStart_553078 baseEnd_553078 := by
    simpa [prefixWord, tailWord_553078, baseEnd_553078] using wordTrace_append hprefix tailTrace_553078
  have hstable : (prefixWord ++ tailWord_553078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553078).length < 2 ^ (prefixWord ++ tailWord_553078).sum := by decide
  have hdescent : baseEnd_553078 < baseStart_553078 := by decide
  rcases family_descends (prefixWord ++ tailWord_553078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553106 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_553106 : Nat := 118140960795 + 553106 * 2 ^ 59
def prefixEnd_553106 : Nat := 4983230072969 + 3 ^ 40 * 553106 * 2
def baseEnd_553106 : Nat := 252452649676282847938949

theorem tailTrace_553106 : CollatzResearch.WordTrace tailWord_553106 prefixEnd_553106 252452649676282847938949 := by
  unfold tailWord_553106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043358283549724957331793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13448955422799266552884781 5043358283549724957331793)
  ·
    refine ⟨3782518712662293717998845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5043358283549724957331793 3782518712662293717998845)
    ·
      refine ⟨1418444517248360144249567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3782518712662293717998845 1418444517248360144249567)
      ·
        refine ⟨2127666775872540216374351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418444517248360144249567 2127666775872540216374351)
        ·
          refine ⟨3191500163808810324561527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127666775872540216374351 3191500163808810324561527)
          ·
            refine ⟨4787250245713215486842291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191500163808810324561527 4787250245713215486842291)
            ·
              refine ⟨7180875368569823230263437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787250245713215486842291 7180875368569823230263437)
              ·
                refine ⟨2692828263213683711348789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7180875368569823230263437 2692828263213683711348789)
                ·
                  refine ⟨252452649676282847938949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692828263213683711348789 252452649676282847938949)
                  ·
                    rfl

theorem cell20_553106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_553106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553106 prefixEnd_553106 := by exact prefixLift 553106
  have htrace : WordTrace (prefixWord ++ tailWord_553106) baseStart_553106 baseEnd_553106 := by
    simpa [prefixWord, tailWord_553106, baseEnd_553106] using wordTrace_append hprefix tailTrace_553106
  have hstable : (prefixWord ++ tailWord_553106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553106).length < 2 ^ (prefixWord ++ tailWord_553106).sum := by decide
  have hdescent : baseEnd_553106 < baseStart_553106 := by decide
  rcases family_descends (prefixWord ++ tailWord_553106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553109 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 2]
def baseStart_553109 : Nat := 118140960795 + 553109 * 2 ^ 59
def prefixEnd_553109 : Nat := 4983230072969 + 3 ^ 40 * 553109 * 2
def baseEnd_553109 : Nat := 252454018958028170838937

theorem tailTrace_553109 : CollatzResearch.WordTrace tailWord_553109 prefixEnd_553109 252454018958028170838937 := by
  unfold tailWord_553109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20173542553188031341686381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13449028368792020894457587 20173542553188031341686381)
  ·
    refine ⟨7565078457445511753132393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20173542553188031341686381 7565078457445511753132393)
    ·
      refine ⟨5673808843084133814849295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7565078457445511753132393 5673808843084133814849295)
      ·
        refine ⟨8510713264626200722273943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673808843084133814849295 8510713264626200722273943)
        ·
          refine ⟨12766069896939301083410915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510713264626200722273943 12766069896939301083410915)
          ·
            refine ⟨19149104845408951625116373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12766069896939301083410915 19149104845408951625116373)
            ·
              refine ⟨448807144814272303713665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19149104845408951625116373 448807144814272303713665)
              ·
                refine ⟨336605358610704227785249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448807144814272303713665 336605358610704227785249)
                ·
                  refine ⟨252454018958028170838937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336605358610704227785249 252454018958028170838937)
                  ·
                    rfl

theorem cell20_553109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_553109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553109 prefixEnd_553109 := by exact prefixLift 553109
  have htrace : WordTrace (prefixWord ++ tailWord_553109) baseStart_553109 baseEnd_553109 := by
    simpa [prefixWord, tailWord_553109, baseEnd_553109] using wordTrace_append hprefix tailTrace_553109
  have hstable : (prefixWord ++ tailWord_553109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553109).length < 2 ^ (prefixWord ++ tailWord_553109).sum := by decide
  have hdescent : baseEnd_553109 < baseStart_553109 := by decide
  rcases family_descends (prefixWord ++ tailWord_553109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553120 : List Nat := [2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_553120 : Nat := 118140960795 + 553120 * 2 ^ 59
def prefixEnd_553120 : Nat := 4983230072969 + 3 ^ 40 * 553120 * 2
def baseEnd_553120 : Nat := 84153013219253673824075

theorem tailTrace_553120 : CollatzResearch.WordTrace tailWord_553120 prefixEnd_553120 84153013219253673824075 := by
  unfold tailWord_553120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086971878074090110168407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13449295837432120146891209 10086971878074090110168407)
  ·
    refine ⟨15130457817111135165252611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086971878074090110168407 15130457817111135165252611)
    ·
      refine ⟨22695686725666702747878917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15130457817111135165252611 22695686725666702747878917)
      ·
        refine ⟨4255441261062506765227297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22695686725666702747878917 4255441261062506765227297)
        ·
          refine ⟨3191580945796880073920473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255441261062506765227297 3191580945796880073920473)
          ·
            refine ⟨2393685709347660055440355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191580945796880073920473 2393685709347660055440355)
            ·
              refine ⟨3590528564021490083160533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393685709347660055440355 3590528564021490083160533)
              ·
                refine ⟨84153013219253673824075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3590528564021490083160533 84153013219253673824075)
                ·
                  rfl

theorem cell20_553120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_553120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553120 prefixEnd_553120 := by exact prefixLift 553120
  have htrace : WordTrace (prefixWord ++ tailWord_553120) baseStart_553120 baseEnd_553120 := by
    simpa [prefixWord, tailWord_553120, baseEnd_553120] using wordTrace_append hprefix tailTrace_553120
  have hstable : (prefixWord ++ tailWord_553120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553120).length < 2 ^ (prefixWord ++ tailWord_553120).sum := by decide
  have hdescent : baseEnd_553120 < baseStart_553120 := by decide
  rcases family_descends (prefixWord ++ tailWord_553120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553154 : List Nat := [3, 5, 1, 1, 1, 9]
def baseStart_553154 : Nat := 118140960795 + 553154 * 2 ^ 59
def prefixEnd_553154 : Nat := 4983230072969 + 3 ^ 40 * 553154 * 2
def baseEnd_553154 : Nat := 9350909562378074605139

theorem tailTrace_553154 : CollatzResearch.WordTrace tailWord_553154 prefixEnd_553154 9350909562378074605139 := by
  unfold tailWord_553154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043795959506251006768629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13450122558683336018049677 5043795959506251006768629)
  ·
    refine ⟨472855871203711031884559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5043795959506251006768629 472855871203711031884559)
    ·
      refine ⟨709283806805566547826839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472855871203711031884559 709283806805566547826839)
      ·
        refine ⟨1063925710208349821740259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709283806805566547826839 1063925710208349821740259)
        ·
          refine ⟨1595888565312524732610389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063925710208349821740259 1595888565312524732610389)
          ·
            refine ⟨9350909562378074605139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1595888565312524732610389 9350909562378074605139)
            ·
              rfl

theorem cell20_553154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 9].length) (baseStart_553154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553154 prefixEnd_553154 := by exact prefixLift 553154
  have htrace : WordTrace (prefixWord ++ tailWord_553154) baseStart_553154 baseEnd_553154 := by
    simpa [prefixWord, tailWord_553154, baseEnd_553154] using wordTrace_append hprefix tailTrace_553154
  have hstable : (prefixWord ++ tailWord_553154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553154).length < 2 ^ (prefixWord ++ tailWord_553154).sum := by decide
  have hdescent : baseEnd_553154 < baseStart_553154 := by decide
  rcases family_descends (prefixWord ++ tailWord_553154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553164 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_553164 : Nat := 118140960795 + 553164 * 2 ^ 59
def prefixEnd_553164 : Nat := 4983230072969 + 3 ^ 40 * 553164 * 2
def baseEnd_553164 : Nat := 252479122456692424005379

theorem tailTrace_553164 : CollatzResearch.WordTrace tailWord_553164 prefixEnd_553164 252479122456692424005379 := by
  unfold tailWord_553164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087774283994387867469273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13450365711992517156625697 10087774283994387867469273)
  ·
    refine ⟨7565830712995790900601955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10087774283994387867469273 7565830712995790900601955)
    ·
      refine ⟨11348746069493686350902933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565830712995790900601955 11348746069493686350902933)
      ·
        refine ⟨531972472007516547698575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11348746069493686350902933 531972472007516547698575)
        ·
          refine ⟨797958708011274821547863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531972472007516547698575 797958708011274821547863)
          ·
            refine ⟨1196938062016912232321795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797958708011274821547863 1196938062016912232321795)
            ·
              refine ⟨1795407093025368348482693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196938062016912232321795 1795407093025368348482693)
              ·
                refine ⟨336638829942256565340505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1795407093025368348482693 336638829942256565340505)
                ·
                  refine ⟨252479122456692424005379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336638829942256565340505 252479122456692424005379)
                  ·
                    rfl

theorem cell20_553164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_553164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553164 prefixEnd_553164 := by exact prefixLift 553164
  have htrace : WordTrace (prefixWord ++ tailWord_553164) baseStart_553164 baseEnd_553164 := by
    simpa [prefixWord, tailWord_553164, baseEnd_553164] using wordTrace_append hprefix tailTrace_553164
  have hstable : (prefixWord ++ tailWord_553164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553164).length < 2 ^ (prefixWord ++ tailWord_553164).sum := by decide
  have hdescent : baseEnd_553164 < baseStart_553164 := by decide
  rcases family_descends (prefixWord ++ tailWord_553164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553189 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_553189 : Nat := 118140960795 + 553189 * 2 ^ 59
def prefixEnd_553189 : Nat := 4983230072969 + 3 ^ 40 * 553189 * 2
def baseEnd_553189 : Nat := 252490533137903448171943

theorem tailTrace_553189 : CollatzResearch.WordTrace tailWord_553189 prefixEnd_553189 252490533137903448171943 := by
  unfold tailWord_553189
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176460392898205004598621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450973595265470003065747 20176460392898205004598621)
  ·
    refine ⟨7566172647336826876724483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20176460392898205004598621 7566172647336826876724483)
    ·
      refine ⟨11349258971005240315086725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566172647336826876724483 11349258971005240315086725)
      ·
        refine ⟨2127986057063482559078761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11349258971005240315086725 2127986057063482559078761)
        ·
          refine ⟨1595989542797611919309071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127986057063482559078761 1595989542797611919309071)
          ·
            refine ⟨2393984314196417878963607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595989542797611919309071 2393984314196417878963607)
            ·
              refine ⟨3590976471294626818445411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393984314196417878963607 3590976471294626818445411)
              ·
                refine ⟨5386464706941940227668117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590976471294626818445411 5386464706941940227668117)
                ·
                  refine ⟨252490533137903448171943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5386464706941940227668117 252490533137903448171943)
                  ·
                    rfl

theorem cell20_553189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_553189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553189 prefixEnd_553189 := by exact prefixLift 553189
  have htrace : WordTrace (prefixWord ++ tailWord_553189) baseStart_553189 baseEnd_553189 := by
    simpa [prefixWord, tailWord_553189, baseEnd_553189] using wordTrace_append hprefix tailTrace_553189
  have hstable : (prefixWord ++ tailWord_553189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553189).length < 2 ^ (prefixWord ++ tailWord_553189).sum := by decide
  have hdescent : baseEnd_553189 < baseStart_553189 := by decide
  rcases family_descends (prefixWord ++ tailWord_553189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553203 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_553203 : Nat := 118140960795 + 553203 * 2 ^ 59
def prefixEnd_553203 : Nat := 4983230072969 + 3 ^ 40 * 553203 * 2
def baseEnd_553203 : Nat := 252496923119381621705219

theorem tailTrace_553203 : CollatzResearch.WordTrace tailWord_553203 prefixEnd_553203 252496923119381621705219 := by
  unfold tailWord_553203
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176971014847485395608263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451314009898323597072175 20176971014847485395608263)
  ·
    refine ⟨30265456522271228093412395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20176971014847485395608263 30265456522271228093412395)
    ·
      refine ⟨45398184783406842140118593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30265456522271228093412395 45398184783406842140118593)
      ·
        refine ⟨34048638587555131605088945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45398184783406842140118593 34048638587555131605088945)
        ·
          refine ⟨25536478940666348703816709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34048638587555131605088945 25536478940666348703816709)
          ·
            refine ⟨4788089801374940381965633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25536478940666348703816709 4788089801374940381965633)
            ·
              refine ⟨3591067351031205286474225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788089801374940381965633 3591067351031205286474225)
              ·
                refine ⟨2693300513273403964855669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591067351031205286474225 2693300513273403964855669)
                ·
                  refine ⟨252496923119381621705219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2693300513273403964855669 252496923119381621705219)
                  ·
                    rfl

theorem cell20_553203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_553203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553203 prefixEnd_553203 := by exact prefixLift 553203
  have htrace : WordTrace (prefixWord ++ tailWord_553203) baseStart_553203 baseEnd_553203 := by
    simpa [prefixWord, tailWord_553203, baseEnd_553203] using wordTrace_append hprefix tailTrace_553203
  have hstable : (prefixWord ++ tailWord_553203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553203).length < 2 ^ (prefixWord ++ tailWord_553203).sum := by decide
  have hdescent : baseEnd_553203 < baseStart_553203 := by decide
  rcases family_descends (prefixWord ++ tailWord_553203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553223 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_553223 : Nat := 118140960795 + 553223 * 2 ^ 59
def prefixEnd_553223 : Nat := 4983230072969 + 3 ^ 40 * 553223 * 2
def baseEnd_553223 : Nat := 252506051664350441038471

theorem tailTrace_553223 : CollatzResearch.WordTrace tailWord_553223 prefixEnd_553223 252506051664350441038471 := by
  unfold tailWord_553223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177700474775028811336323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451800316516685874224215 20177700474775028811336323)
  ·
    refine ⟨30266550712162543217004485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177700474775028811336323 30266550712162543217004485)
    ·
      refine ⟨5674978258530476853188341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30266550712162543217004485 5674978258530476853188341)
      ·
        refine ⟨532029211737232204986407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5674978258530476853188341 532029211737232204986407)
        ·
          refine ⟨798043817605848307479611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532029211737232204986407 798043817605848307479611)
          ·
            refine ⟨1197065726408772461219417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798043817605848307479611 1197065726408772461219417)
            ·
              refine ⟨897799294806579345914563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197065726408772461219417 897799294806579345914563)
              ·
                refine ⟨1346698942209869018871845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897799294806579345914563 1346698942209869018871845)
                ·
                  refine ⟨252506051664350441038471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346698942209869018871845 252506051664350441038471)
                  ·
                    rfl

theorem cell20_553223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_553223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553223 prefixEnd_553223 := by exact prefixLift 553223
  have htrace : WordTrace (prefixWord ++ tailWord_553223) baseStart_553223 baseEnd_553223 := by
    simpa [prefixWord, tailWord_553223, baseEnd_553223] using wordTrace_append hprefix tailTrace_553223
  have hstable : (prefixWord ++ tailWord_553223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553223).length < 2 ^ (prefixWord ++ tailWord_553223).sum := by decide
  have hdescent : baseEnd_553223 < baseStart_553223 := by decide
  rcases family_descends (prefixWord ++ tailWord_553223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553227 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_553227 : Nat := 118140960795 + 553227 * 2 ^ 59
def prefixEnd_553227 : Nat := 4983230072969 + 3 ^ 40 * 553227 * 2
def baseEnd_553227 : Nat := 252507877373344204905121

theorem tailTrace_553227 : CollatzResearch.WordTrace tailWord_553227 prefixEnd_553227 252507877373344204905121 := by
  unfold tailWord_553227
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177846366760537494481935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451897577840358329654623 20177846366760537494481935)
  ·
    refine ⟨30266769550140806241722903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177846366760537494481935 30266769550140806241722903)
    ·
      refine ⟨45400154325211209362584355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30266769550140806241722903 45400154325211209362584355)
      ·
        refine ⟨68100231487816814043876533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45400154325211209362584355 68100231487816814043876533)
        ·
          refine ⟨6384396701982826316613425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68100231487816814043876533 6384396701982826316613425)
          ·
            refine ⟨4788297526487119737460069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6384396701982826316613425 4788297526487119737460069)
            ·
              refine ⟨897805786216334950773763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4788297526487119737460069 897805786216334950773763)
              ·
                refine ⟨1346708679324502426160645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897805786216334950773763 1346708679324502426160645)
                ·
                  refine ⟨252507877373344204905121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346708679324502426160645 252507877373344204905121)
                  ·
                    rfl

theorem cell20_553227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_553227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553227 prefixEnd_553227 := by exact prefixLift 553227
  have htrace : WordTrace (prefixWord ++ tailWord_553227) baseStart_553227 baseEnd_553227 := by
    simpa [prefixWord, tailWord_553227, baseEnd_553227] using wordTrace_append hprefix tailTrace_553227
  have hstable : (prefixWord ++ tailWord_553227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553227).length < 2 ^ (prefixWord ++ tailWord_553227).sum := by decide
  have hdescent : baseEnd_553227 < baseStart_553227 := by decide
  rcases family_descends (prefixWord ++ tailWord_553227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553278 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_553278 : Nat := 118140960795 + 553278 * 2 ^ 59
def prefixEnd_553278 : Nat := 4983230072969 + 3 ^ 40 * 553278 * 2
def baseEnd_553278 : Nat := 252531155163014694204913

theorem tailTrace_553278 : CollatzResearch.WordTrace tailWord_553278 prefixEnd_553278 252531155163014694204913 := by
  unfold tailWord_553278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522463311196971650573561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13453137659717182136392325 2522463311196971650573561)
  ·
    refine ⟨1891847483397728737930171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2522463311196971650573561 1891847483397728737930171)
    ·
      refine ⟨2837771225096593106895257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891847483397728737930171 2837771225096593106895257)
      ·
        refine ⟨2128328418822444830171443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2837771225096593106895257 2128328418822444830171443)
        ·
          refine ⟨3192492628233667245257165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128328418822444830171443 3192492628233667245257165)
          ·
            refine ⟨1197184735587625216971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3192492628233667245257165 1197184735587625216971437)
            ·
              refine ⟨448944275845359456364289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1197184735587625216971437 448944275845359456364289)
              ·
                refine ⟨336708206884019592273217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448944275845359456364289 336708206884019592273217)
                ·
                  refine ⟨252531155163014694204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336708206884019592273217 252531155163014694204913)
                  ·
                    rfl

theorem cell20_553278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_553278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553278 prefixEnd_553278 := by exact prefixLift 553278
  have htrace : WordTrace (prefixWord ++ tailWord_553278) baseStart_553278 baseEnd_553278 := by
    simpa [prefixWord, tailWord_553278, baseEnd_553278] using wordTrace_append hprefix tailTrace_553278
  have hstable : (prefixWord ++ tailWord_553278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553278).length < 2 ^ (prefixWord ++ tailWord_553278).sum := by decide
  have hdescent : baseEnd_553278 < baseStart_553278 := by decide
  rcases family_descends (prefixWord ++ tailWord_553278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553279 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_553279 : Nat := 118140960795 + 553279 * 2 ^ 59
def prefixEnd_553279 : Nat := 4983230072969 + 3 ^ 40 * 553279 * 2
def baseEnd_553279 : Nat := 252531611590263135171575

theorem tailTrace_553279 : CollatzResearch.WordTrace tailWord_553279 prefixEnd_553279 252531611590263135171575 := by
  unfold tailWord_553279
  simp only [CollatzResearch.WordTrace]
  refine ⟨20179742962572150375374891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13453161975048100250249927 20179742962572150375374891)
  ·
    refine ⟨30269614443858225563062337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20179742962572150375374891 30269614443858225563062337)
    ·
      refine ⟨22702210832893669172296753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30269614443858225563062337 22702210832893669172296753)
      ·
        refine ⟨17026658124670251879222565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22702210832893669172296753 17026658124670251879222565)
        ·
          refine ⟨3192498398375672227354231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17026658124670251879222565 3192498398375672227354231)
          ·
            refine ⟨4788747597563508341031347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192498398375672227354231 4788747597563508341031347)
            ·
              refine ⟨7183121396345262511547021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4788747597563508341031347 7183121396345262511547021)
              ·
                refine ⟨2693670523629473441830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7183121396345262511547021 2693670523629473441830133)
                ·
                  refine ⟨252531611590263135171575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2693670523629473441830133 252531611590263135171575)
                  ·
                    rfl

theorem cell20_553279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_553279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553279 prefixEnd_553279 := by exact prefixLift 553279
  have htrace : WordTrace (prefixWord ++ tailWord_553279) baseStart_553279 baseEnd_553279 := by
    simpa [prefixWord, tailWord_553279, baseEnd_553279] using wordTrace_append hprefix tailTrace_553279
  have hstable : (prefixWord ++ tailWord_553279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553279).length < 2 ^ (prefixWord ++ tailWord_553279).sum := by decide
  have hdescent : baseEnd_553279 < baseStart_553279 := by decide
  rcases family_descends (prefixWord ++ tailWord_553279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553296 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_553296 : Nat := 118140960795 + 553296 * 2 ^ 59
def prefixEnd_553296 : Nat := 4983230072969 + 3 ^ 40 * 553296 * 2
def baseEnd_553296 : Nat := 252539370853486631604839

theorem tailTrace_553296 : CollatzResearch.WordTrace tailWord_553296 prefixEnd_553296 252539370853486631604839 := by
  unfold tailWord_553296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090181501755281139371871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13453575335673708185829161 10090181501755281139371871)
  ·
    refine ⟨15135272252632921709057807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10090181501755281139371871 15135272252632921709057807)
    ·
      refine ⟨22702908378949382563586711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135272252632921709057807 22702908378949382563586711)
      ·
        refine ⟨34054362568424073845380067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22702908378949382563586711 34054362568424073845380067)
        ·
          refine ⟨51081543852636110768070101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34054362568424073845380067 51081543852636110768070101)
          ·
            refine ⟨1197223684046158846126643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51081543852636110768070101 1197223684046158846126643)
            ·
              refine ⟨1795835526069238269189965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197223684046158846126643 1795835526069238269189965)
              ·
                refine ⟨673438322275964350946237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795835526069238269189965 673438322275964350946237)
                ·
                  refine ⟨252539370853486631604839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673438322275964350946237 252539370853486631604839)
                  ·
                    rfl

theorem cell20_553296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_553296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553296 prefixEnd_553296 := by exact prefixLift 553296
  have htrace : WordTrace (prefixWord ++ tailWord_553296) baseStart_553296 baseEnd_553296 := by
    simpa [prefixWord, tailWord_553296, baseEnd_553296] using wordTrace_append hprefix tailTrace_553296
  have hstable : (prefixWord ++ tailWord_553296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553296).length < 2 ^ (prefixWord ++ tailWord_553296).sum := by decide
  have hdescent : baseEnd_553296 < baseStart_553296 := by decide
  rcases family_descends (prefixWord ++ tailWord_553296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553358 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_553358 : Nat := 118140960795 + 553358 * 2 ^ 59
def prefixEnd_553358 : Nat := 4983230072969 + 3 ^ 40 * 553358 * 2
def baseEnd_553358 : Nat := 252567669342889971537919

theorem tailTrace_553358 : CollatzResearch.WordTrace tailWord_553358 prefixEnd_553358 252567669342889971537919 := by
  unfold tailWord_553358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522828041160743358437591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13455082886190631245000485 2522828041160743358437591)
  ·
    refine ⟨3784242061741115037656387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2522828041160743358437591 3784242061741115037656387)
    ·
      refine ⟨5676363092611672556484581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3784242061741115037656387 5676363092611672556484581)
      ·
        refine ⟨1064318079864688604340859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5676363092611672556484581 1064318079864688604340859)
        ·
          refine ⟨1596477119797032906511289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064318079864688604340859 1596477119797032906511289)
          ·
            refine ⟨1197357839847774679883467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596477119797032906511289 1197357839847774679883467)
            ·
              refine ⟨1796036759771662019825201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197357839847774679883467 1796036759771662019825201)
              ·
                refine ⟨1347027569828746514868901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796036759771662019825201 1347027569828746514868901)
                ·
                  refine ⟨252567669342889971537919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347027569828746514868901 252567669342889971537919)
                  ·
                    rfl

theorem cell20_553358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_553358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553358 prefixEnd_553358 := by exact prefixLift 553358
  have htrace : WordTrace (prefixWord ++ tailWord_553358) baseStart_553358 baseEnd_553358 := by
    simpa [prefixWord, tailWord_553358, baseEnd_553358] using wordTrace_append hprefix tailTrace_553358
  have hstable : (prefixWord ++ tailWord_553358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553358).length < 2 ^ (prefixWord ++ tailWord_553358).sum := by decide
  have hdescent : baseEnd_553358 < baseStart_553358 := by decide
  rcases family_descends (prefixWord ++ tailWord_553358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553389 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_553389 : Nat := 118140960795 + 553389 * 2 ^ 59
def prefixEnd_553389 : Nat := 4983230072969 + 3 ^ 40 * 553389 * 2
def baseEnd_553389 : Nat := 252581818587591641504459

theorem tailTrace_553389 : CollatzResearch.WordTrace tailWord_553389 prefixEnd_553389 252581818587591641504459 := by
  unfold tailWord_553389
  simp only [CollatzResearch.WordTrace]
  refine ⟨20183754992173639161879221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13455836661449092774586147 20183754992173639161879221)
  ·
    refine ⟨1892227030516278671426177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20183754992173639161879221 1892227030516278671426177)
    ·
      refine ⟨1419170272887209003569633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1892227030516278671426177 1419170272887209003569633)
      ·
        refine ⟨1064377704665406752677225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1419170272887209003569633 1064377704665406752677225)
        ·
          refine ⟨798283278499055064507919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064377704665406752677225 798283278499055064507919)
          ·
            refine ⟨1197424917748582596761879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798283278499055064507919 1197424917748582596761879)
            ·
              refine ⟨1796137376622873895142819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197424917748582596761879 1796137376622873895142819)
              ·
                refine ⟨2694206064934310842714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796137376622873895142819 2694206064934310842714229)
                ·
                  refine ⟨252581818587591641504459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694206064934310842714229 252581818587591641504459)
                  ·
                    rfl

theorem cell20_553389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_553389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553389 prefixEnd_553389 := by exact prefixLift 553389
  have htrace : WordTrace (prefixWord ++ tailWord_553389) baseStart_553389 baseEnd_553389 := by
    simpa [prefixWord, tailWord_553389, baseEnd_553389] using wordTrace_append hprefix tailTrace_553389
  have hstable : (prefixWord ++ tailWord_553389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553389).length < 2 ^ (prefixWord ++ tailWord_553389).sum := by decide
  have hdescent : baseEnd_553389 < baseStart_553389 := by decide
  rcases family_descends (prefixWord ++ tailWord_553389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553420 : List Nat := [2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_553420 : Nat := 118140960795 + 553420 * 2 ^ 59
def prefixEnd_553420 : Nat := 4983230072969 + 3 ^ 40 * 553420 * 2
def baseEnd_553420 : Nat := 84198655944097770490333

theorem tailTrace_553420 : CollatzResearch.WordTrace tailWord_553420 prefixEnd_553420 84198655944097770490333 := by
  unfold tailWord_553420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10092442827530665728128857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13456590436707554304171809 10092442827530665728128857)
  ·
    refine ⟨7569332120647999296096643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10092442827530665728128857 7569332120647999296096643)
    ·
      refine ⟨11353998180971998944144965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7569332120647999296096643 11353998180971998944144965)
      ·
        refine ⟨2128874658932249802027181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11353998180971998944144965 2128874658932249802027181)
        ·
          refine ⟨798327997099593675760193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2128874658932249802027181 798327997099593675760193)
          ·
            refine ⟨598745997824695256820145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798327997099593675760193 598745997824695256820145)
            ·
              refine ⟨449059498368521442615109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598745997824695256820145 449059498368521442615109)
              ·
                refine ⟨84198655944097770490333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449059498368521442615109 84198655944097770490333)
                ·
                  rfl

theorem cell20_553420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_553420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553420 prefixEnd_553420 := by exact prefixLift 553420
  have htrace : WordTrace (prefixWord ++ tailWord_553420) baseStart_553420 baseEnd_553420 := by
    simpa [prefixWord, tailWord_553420, baseEnd_553420] using wordTrace_append hprefix tailTrace_553420
  have hstable : (prefixWord ++ tailWord_553420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553420).length < 2 ^ (prefixWord ++ tailWord_553420).sum := by decide
  have hdescent : baseEnd_553420 < baseStart_553420 := by decide
  rcases family_descends (prefixWord ++ tailWord_553420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553461 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_553461 : Nat := 118140960795 + 553461 * 2 ^ 59
def prefixEnd_553461 : Nat := 4983230072969 + 3 ^ 40 * 553461 * 2
def baseEnd_553461 : Nat := 252614681349479391104165

theorem tailTrace_553461 : CollatzResearch.WordTrace tailWord_553461 prefixEnd_553461 252614681349479391104165 := by
  unfold tailWord_553461
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186381047912795458500237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13457587365275196972333491 20186381047912795458500237)
  ·
    refine ⟨7569892892967298296937589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20186381047912795458500237 7569892892967298296937589)
    ·
      refine ⟨709677458715684215337899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7569892892967298296937589 709677458715684215337899)
      ·
        refine ⟨1064516188073526323006849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709677458715684215337899 1064516188073526323006849)
        ·
          refine ⟨798387141055144742255137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064516188073526323006849 798387141055144742255137)
          ·
            refine ⟨598790355791358556691353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798387141055144742255137 598790355791358556691353)
            ·
              refine ⟨449092766843518917518515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598790355791358556691353 449092766843518917518515)
              ·
                refine ⟨673639150265278376277773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449092766843518917518515 673639150265278376277773)
                ·
                  refine ⟨252614681349479391104165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673639150265278376277773 252614681349479391104165)
                  ·
                    rfl

theorem cell20_553461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_553461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553461 prefixEnd_553461 := by exact prefixLift 553461
  have htrace : WordTrace (prefixWord ++ tailWord_553461) baseStart_553461 baseEnd_553461 := by
    simpa [prefixWord, tailWord_553461, baseEnd_553461] using wordTrace_append hprefix tailTrace_553461
  have hstable : (prefixWord ++ tailWord_553461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553461).length < 2 ^ (prefixWord ++ tailWord_553461).sum := by decide
  have hdescent : baseEnd_553461 < baseStart_553461 := by decide
  rcases family_descends (prefixWord ++ tailWord_553461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553548 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_553548 : Nat := 118140960795 + 553548 * 2 ^ 59
def prefixEnd_553548 : Nat := 4983230072969 + 3 ^ 40 * 553548 * 2
def baseEnd_553548 : Nat := 252654390520093755203809

theorem tailTrace_553548 : CollatzResearch.WordTrace tailWord_553548 prefixEnd_553548 252654390520093755203809 := by
  unfold tailWord_553548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10094777099298804658458649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13459702799065072877944865 10094777099298804658458649)
  ·
    refine ⟨7571082824474103493843987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10094777099298804658458649 7571082824474103493843987)
    ·
      refine ⟨11356624236711155240765981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7571082824474103493843987 11356624236711155240765981)
      ·
        refine ⟨4258734088766683215287243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11356624236711155240765981 4258734088766683215287243)
        ·
          refine ⟨6388101133150024822930865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258734088766683215287243 6388101133150024822930865)
          ·
            refine ⟨4791075849862518617198149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6388101133150024822930865 4791075849862518617198149)
            ·
              refine ⟨898326721849222240724653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4791075849862518617198149 898326721849222240724653)
              ·
                refine ⟨336872520693458340271745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 898326721849222240724653 336872520693458340271745)
                ·
                  refine ⟨252654390520093755203809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336872520693458340271745 252654390520093755203809)
                  ·
                    rfl

theorem cell20_553548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_553548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553548 prefixEnd_553548 := by exact prefixLift 553548
  have htrace : WordTrace (prefixWord ++ tailWord_553548) baseStart_553548 baseEnd_553548 := by
    simpa [prefixWord, tailWord_553548, baseEnd_553548] using wordTrace_append hprefix tailTrace_553548
  have hstable : (prefixWord ++ tailWord_553548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553548).length < 2 ^ (prefixWord ++ tailWord_553548).sum := by decide
  have hdescent : baseEnd_553548 < baseStart_553548 := by decide
  rcases family_descends (prefixWord ++ tailWord_553548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553559 : List Nat := [1, 1, 3, 2, 2, 2, 9]
def baseStart_553559 : Nat := 118140960795 + 553559 * 2 ^ 59
def prefixEnd_553559 : Nat := 4983230072969 + 3 ^ 40 * 553559 * 2
def baseEnd_553559 : Nat := 28073267913314067315233

theorem tailTrace_553559 : CollatzResearch.WordTrace tailWord_553559 prefixEnd_553559 28073267913314067315233 := by
  unfold tailWord_553559
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189955401557758195567731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13459970267705172130378487 20189955401557758195567731)
  ·
    refine ⟨30284933102336637293351597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20189955401557758195567731 30284933102336637293351597)
    ·
      refine ⟨11356849913376238985006849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30284933102336637293351597 11356849913376238985006849)
      ·
        refine ⟨8517637435032179238755137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11356849913376238985006849 8517637435032179238755137)
        ·
          refine ⟨6388228076274134429066353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8517637435032179238755137 6388228076274134429066353)
          ·
            refine ⟨4791171057205600821799765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6388228076274134429066353 4791171057205600821799765)
            ·
              refine ⟨28073267913314067315233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4791171057205600821799765 28073267913314067315233)
              ·
                rfl

theorem cell20_553559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_553559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553559 prefixEnd_553559 := by exact prefixLift 553559
  have htrace : WordTrace (prefixWord ++ tailWord_553559) baseStart_553559 baseEnd_553559 := by
    simpa [prefixWord, tailWord_553559, baseEnd_553559] using wordTrace_append hprefix tailTrace_553559
  have hstable : (prefixWord ++ tailWord_553559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553559).length < 2 ^ (prefixWord ++ tailWord_553559).sum := by decide
  have hdescent : baseEnd_553559 < baseStart_553559 := by decide
  rcases family_descends (prefixWord ++ tailWord_553559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553569 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_553569 : Nat := 118140960795 + 553569 * 2 ^ 59
def prefixEnd_553569 : Nat := 4983230072969 + 3 ^ 40 * 553569 * 2
def baseEnd_553569 : Nat := 252663975492311015503723

theorem tailTrace_553569 : CollatzResearch.WordTrace tailWord_553569 prefixEnd_553569 252663975492311015503723 := by
  unfold tailWord_553569
  simp only [CollatzResearch.WordTrace]
  refine ⟨20190320131521529903431761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13460213421014353268954507 20190320131521529903431761)
  ·
    refine ⟨15142740098641147427573821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20190320131521529903431761 15142740098641147427573821)
    ·
      refine ⟨5678527536990430285340183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15142740098641147427573821 5678527536990430285340183)
      ·
        refine ⟨8517791305485645428010275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5678527536990430285340183 8517791305485645428010275)
        ·
          refine ⟨12776686958228468142015413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8517791305485645428010275 12776686958228468142015413)
          ·
            refine ⟨1197814402333918888313945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12776686958228468142015413 1197814402333918888313945)
            ·
              refine ⟨898360801750439166235459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197814402333918888313945 898360801750439166235459)
              ·
                refine ⟨1347541202625658749353189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898360801750439166235459 1347541202625658749353189)
                ·
                  refine ⟨252663975492311015503723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347541202625658749353189 252663975492311015503723)
                  ·
                    rfl

theorem cell20_553569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_553569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553569 prefixEnd_553569 := by exact prefixLift 553569
  have htrace : WordTrace (prefixWord ++ tailWord_553569) baseStart_553569 baseEnd_553569 := by
    simpa [prefixWord, tailWord_553569, baseEnd_553569] using wordTrace_append hprefix tailTrace_553569
  have hstable : (prefixWord ++ tailWord_553569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553569).length < 2 ^ (prefixWord ++ tailWord_553569).sum := by decide
  have hdescent : baseEnd_553569 < baseStart_553569 := by decide
  rcases family_descends (prefixWord ++ tailWord_553569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553583 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_553583 : Nat := 118140960795 + 553583 * 2 ^ 59
def prefixEnd_553583 : Nat := 4983230072969 + 3 ^ 40 * 553583 * 2
def baseEnd_553583 : Nat := 252670365473789189036999

theorem tailTrace_553583 : CollatzResearch.WordTrace tailWord_553583 prefixEnd_553583 252670365473789189036999 := by
  unfold tailWord_553583
  simp only [CollatzResearch.WordTrace]
  refine ⟨20190830753470810294441403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13460553835647206862960935 20190830753470810294441403)
  ·
    refine ⟨30286246130206215441662105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20190830753470810294441403 30286246130206215441662105)
    ·
      refine ⟨22714684597654661581246579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30286246130206215441662105 22714684597654661581246579)
      ·
        refine ⟨34072026896481992371869869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22714684597654661581246579 34072026896481992371869869)
        ·
          refine ⟨12777010086180747139451201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34072026896481992371869869 12777010086180747139451201)
          ·
            refine ⟨9582757564635560354588401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12777010086180747139451201 9582757564635560354588401)
            ·
              refine ⟨7187068173476670265941301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9582757564635560354588401 7187068173476670265941301)
              ·
                refine ⟨673787641263437837431997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7187068173476670265941301 673787641263437837431997)
                ·
                  refine ⟨252670365473789189036999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673787641263437837431997 252670365473789189036999)
                  ·
                    rfl

theorem cell20_553583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_553583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553583 prefixEnd_553583 := by exact prefixLift 553583
  have htrace : WordTrace (prefixWord ++ tailWord_553583) baseStart_553583 baseEnd_553583 := by
    simpa [prefixWord, tailWord_553583, baseEnd_553583] using wordTrace_append hprefix tailTrace_553583
  have hstable : (prefixWord ++ tailWord_553583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553583).length < 2 ^ (prefixWord ++ tailWord_553583).sum := by decide
  have hdescent : baseEnd_553583 < baseStart_553583 := by decide
  rcases family_descends (prefixWord ++ tailWord_553583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553589 : List Nat := [1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_553589 : Nat := 118140960795 + 553589 * 2 ^ 59
def prefixEnd_553589 : Nat := 4983230072969 + 3 ^ 40 * 553589 * 2
def baseEnd_553589 : Nat := 84224368012426611612325

theorem tailTrace_553589 : CollatzResearch.WordTrace tailWord_553589 prefixEnd_553589 84224368012426611612325 := by
  unfold tailWord_553589
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191049591449073319159821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13460699727632715546106547 20191049591449073319159821)
  ·
    refine ⟨7571643596793402494684933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20191049591449073319159821 7571643596793402494684933)
    ·
      refine ⟨1419683174398762967753425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7571643596793402494684933 1419683174398762967753425)
      ·
        refine ⟨1064762380799072225815069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1419683174398762967753425 1064762380799072225815069)
        ·
          refine ⟨399285892799652084680651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1064762380799072225815069 399285892799652084680651)
          ·
            refine ⟨598928839199478127020977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399285892799652084680651 598928839199478127020977)
            ·
              refine ⟨449196629399608595265733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598928839199478127020977 449196629399608595265733)
              ·
                refine ⟨84224368012426611612325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449196629399608595265733 84224368012426611612325)
                ·
                  rfl

theorem cell20_553589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_553589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553589 prefixEnd_553589 := by exact prefixLift 553589
  have htrace : WordTrace (prefixWord ++ tailWord_553589) baseStart_553589 baseEnd_553589 := by
    simpa [prefixWord, tailWord_553589, baseEnd_553589] using wordTrace_append hprefix tailTrace_553589
  have hstable : (prefixWord ++ tailWord_553589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553589).length < 2 ^ (prefixWord ++ tailWord_553589).sum := by decide
  have hdescent : baseEnd_553589 < baseStart_553589 := by decide
  rcases family_descends (prefixWord ++ tailWord_553589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553593 : List Nat := [1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_553593 : Nat := 118140960795 + 553593 * 2 ^ 59
def prefixEnd_553593 : Nat := 4983230072969 + 3 ^ 40 * 553593 * 2
def baseEnd_553593 : Nat := 84224976582091199567875

theorem tailTrace_553593 : CollatzResearch.WordTrace tailWord_553593 prefixEnd_553593 84224976582091199567875 := by
  unfold tailWord_553593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191195483434582002305433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13460796988956388001536955 20191195483434582002305433)
  ·
    refine ⟨15143396612575936501729075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20191195483434582002305433 15143396612575936501729075)
    ·
      refine ⟨22715094918863904752593613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143396612575936501729075 22715094918863904752593613)
      ·
        refine ⟨8518160594573964282222605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22715094918863904752593613 8518160594573964282222605)
        ·
          refine ⟨3194310222965236605833477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8518160594573964282222605 3194310222965236605833477)
          ·
            refine ⟨598933166805981863593777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3194310222965236605833477 598933166805981863593777)
            ·
              refine ⟨449199875104486397695333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598933166805981863593777 449199875104486397695333)
              ·
                refine ⟨84224976582091199567875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449199875104486397695333 84224976582091199567875)
                ·
                  rfl

theorem cell20_553593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_553593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553593 prefixEnd_553593 := by exact prefixLift 553593
  have htrace : WordTrace (prefixWord ++ tailWord_553593) baseStart_553593 baseEnd_553593 := by
    simpa [prefixWord, tailWord_553593, baseEnd_553593] using wordTrace_append hprefix tailTrace_553593
  have hstable : (prefixWord ++ tailWord_553593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553593).length < 2 ^ (prefixWord ++ tailWord_553593).sum := by decide
  have hdescent : baseEnd_553593 < baseStart_553593 := by decide
  rcases family_descends (prefixWord ++ tailWord_553593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553620 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_553620 : Nat := 118140960795 + 553620 * 2 ^ 59
def prefixEnd_553620 : Nat := 4983230072969 + 3 ^ 40 * 553620 * 2
def baseEnd_553620 : Nat := 252687253281981504803515

theorem tailTrace_553620 : CollatzResearch.WordTrace tailWord_553620 prefixEnd_553620 252687253281981504803515 := by
  unfold tailWord_553620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096090127168382806769157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13461453502891177075692209 10096090127168382806769157)
  ·
    refine ⟨1893016898844071776269217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10096090127168382806769157 1893016898844071776269217)
    ·
      refine ⟨1419762674133053832201913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1893016898844071776269217 1419762674133053832201913)
      ·
        refine ⟨1064822005599790374151435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1419762674133053832201913 1064822005599790374151435)
        ·
          refine ⟨1597233008399685561227153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064822005599790374151435 1597233008399685561227153)
          ·
            refine ⟨1197924756299764170920365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597233008399685561227153 1197924756299764170920365)
            ·
              refine ⟨449221783612411564095137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1197924756299764170920365 449221783612411564095137)
              ·
                refine ⟨336916337709308673071353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449221783612411564095137 336916337709308673071353)
                ·
                  refine ⟨252687253281981504803515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336916337709308673071353 252687253281981504803515)
                  ·
                    rfl

theorem cell20_553620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_553620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553620 prefixEnd_553620 := by exact prefixLift 553620
  have htrace : WordTrace (prefixWord ++ tailWord_553620) baseStart_553620 baseEnd_553620 := by
    simpa [prefixWord, tailWord_553620, baseEnd_553620] using wordTrace_append hprefix tailTrace_553620
  have hstable : (prefixWord ++ tailWord_553620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553620).length < 2 ^ (prefixWord ++ tailWord_553620).sum := by decide
  have hdescent : baseEnd_553620 < baseStart_553620 := by decide
  rcases family_descends (prefixWord ++ tailWord_553620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553662 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_553662 : Nat := 118140960795 + 553662 * 2 ^ 59
def prefixEnd_553662 : Nat := 4983230072969 + 3 ^ 40 * 553662 * 2
def baseEnd_553662 : Nat := 252706423226416025403343

theorem tailTrace_553662 : CollatzResearch.WordTrace tailWord_553662 prefixEnd_553662 252706423226416025403343 := by
  unfold tailWord_553662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524214015023075848320905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13462474746789737857711493 2524214015023075848320905)
  ·
    refine ⟨1893160511267306886240679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2524214015023075848320905 1893160511267306886240679)
    ·
      refine ⟨2839740766900960329361019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1893160511267306886240679 2839740766900960329361019)
      ·
        refine ⟨4259611150351440494041529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839740766900960329361019 4259611150351440494041529)
        ·
          refine ⟨3194708362763580370531147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4259611150351440494041529 3194708362763580370531147)
          ·
            refine ⟨4792062544145370555796721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194708362763580370531147 4792062544145370555796721)
            ·
              refine ⟨3594046908109027916847541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792062544145370555796721 3594046908109027916847541)
              ·
                refine ⟨336941897635221367204457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3594046908109027916847541 336941897635221367204457)
                ·
                  refine ⟨252706423226416025403343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336941897635221367204457 252706423226416025403343)
                  ·
                    rfl

theorem cell20_553662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_553662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553662 prefixEnd_553662 := by exact prefixLift 553662
  have htrace : WordTrace (prefixWord ++ tailWord_553662) baseStart_553662 baseEnd_553662 := by
    simpa [prefixWord, tailWord_553662, baseEnd_553662] using wordTrace_append hprefix tailTrace_553662
  have hstable : (prefixWord ++ tailWord_553662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553662).length < 2 ^ (prefixWord ++ tailWord_553662).sum := by decide
  have hdescent : baseEnd_553662 < baseStart_553662 := by decide
  rcases family_descends (prefixWord ++ tailWord_553662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553676 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_553676 : Nat := 118140960795 + 553676 * 2 ^ 59
def prefixEnd_553676 : Nat := 4983230072969 + 3 ^ 40 * 553676 * 2
def baseEnd_553676 : Nat := 252712813207894198936619

theorem tailTrace_553676 : CollatzResearch.WordTrace tailWord_553676 prefixEnd_553676 252712813207894198936619 := by
  unfold tailWord_553676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10097111371066943588788441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13462815161422591451717921 10097111371066943588788441)
  ·
    refine ⟨7572833528300207691591331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10097111371066943588788441 7572833528300207691591331)
    ·
      refine ⟨11359250292450311537386997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7572833528300207691591331 11359250292450311537386997)
      ·
        refine ⟨1064929714917216706630031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11359250292450311537386997 1064929714917216706630031)
        ·
          refine ⟨1597394572375825059945047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064929714917216706630031 1597394572375825059945047)
          ·
            refine ⟨2396091858563737589917571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597394572375825059945047 2396091858563737589917571)
            ·
              refine ⟨3594137787845606384876357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396091858563737589917571 3594137787845606384876357)
              ·
                refine ⟨673900835221051197164317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3594137787845606384876357 673900835221051197164317)
                ·
                  refine ⟨252712813207894198936619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673900835221051197164317 252712813207894198936619)
                  ·
                    rfl

theorem cell20_553676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_553676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553676 prefixEnd_553676 := by exact prefixLift 553676
  have htrace : WordTrace (prefixWord ++ tailWord_553676) baseStart_553676 baseEnd_553676 := by
    simpa [prefixWord, tailWord_553676, baseEnd_553676] using wordTrace_append hprefix tailTrace_553676
  have hstable : (prefixWord ++ tailWord_553676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553676).length < 2 ^ (prefixWord ++ tailWord_553676).sum := by decide
  have hdescent : baseEnd_553676 < baseStart_553676 := by decide
  rcases family_descends (prefixWord ++ tailWord_553676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_553680 : Nat := 118140960795 + 553680 * 2 ^ 59
def prefixEnd_553680 : Nat := 4983230072969 + 3 ^ 40 * 553680 * 2
def baseEnd_553680 : Nat := 252714638916887962803269

theorem tailTrace_553680 : CollatzResearch.WordTrace tailWord_553680 prefixEnd_553680 252714638916887962803269 := by
  unfold tailWord_553680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10097184317059697930361247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13462912422746263907148329 10097184317059697930361247)
  ·
    refine ⟨15145776475589546895541871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10097184317059697930361247 15145776475589546895541871)
    ·
      refine ⟨22718664713384320343312807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145776475589546895541871 22718664713384320343312807)
      ·
        refine ⟨34077997070076480514969211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22718664713384320343312807 34077997070076480514969211)
        ·
          refine ⟨51116995605114720772453817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34077997070076480514969211 51116995605114720772453817)
          ·
            refine ⟨38337746703836040579340363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51116995605114720772453817 38337746703836040579340363)
            ·
              refine ⟨57506620055754060869010545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38337746703836040579340363 57506620055754060869010545)
              ·
                refine ⟨43129965041815545651757909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57506620055754060869010545 43129965041815545651757909)
                ·
                  refine ⟨252714638916887962803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43129965041815545651757909 252714638916887962803269)
                  ·
                    rfl

theorem cell20_553680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_553680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553680 prefixEnd_553680 := by exact prefixLift 553680
  have htrace : WordTrace (prefixWord ++ tailWord_553680) baseStart_553680 baseEnd_553680 := by
    simpa [prefixWord, tailWord_553680, baseEnd_553680] using wordTrace_append hprefix tailTrace_553680
  have hstable : (prefixWord ++ tailWord_553680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553680).length < 2 ^ (prefixWord ++ tailWord_553680).sum := by decide
  have hdescent : baseEnd_553680 < baseStart_553680 := by decide
  rcases family_descends (prefixWord ++ tailWord_553680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553749 : List Nat := [1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_553749 : Nat := 118140960795 + 553749 * 2 ^ 59
def prefixEnd_553749 : Nat := 4983230072969 + 3 ^ 40 * 553749 * 2
def baseEnd_553749 : Nat := 84248710799010129834329

theorem tailTrace_553749 : CollatzResearch.WordTrace tailWord_553749 prefixEnd_553749 84248710799010129834329 := by
  unfold tailWord_553749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196885270869420644984301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13464590180579613763322867 20196885270869420644984301)
  ·
    refine ⟨7573831976576032741869113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20196885270869420644984301 7573831976576032741869113)
    ·
      refine ⟨5680373982432024556401835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7573831976576032741869113 5680373982432024556401835)
      ·
        refine ⟨8520560973648036834602753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680373982432024556401835 8520560973648036834602753)
        ·
          refine ⟨6390420730236027625952065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8520560973648036834602753 6390420730236027625952065)
          ·
            refine ⟨4792815547677020719464049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6390420730236027625952065 4792815547677020719464049)
            ·
              refine ⟨3594611660757765539598037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792815547677020719464049 3594611660757765539598037)
              ·
                refine ⟨84248710799010129834329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3594611660757765539598037 84248710799010129834329)
                ·
                  rfl

theorem cell20_553749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_553749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553749 prefixEnd_553749 := by exact prefixLift 553749
  have htrace : WordTrace (prefixWord ++ tailWord_553749) baseStart_553749 baseEnd_553749 := by
    simpa [prefixWord, tailWord_553749, baseEnd_553749] using wordTrace_append hprefix tailTrace_553749
  have hstable : (prefixWord ++ tailWord_553749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553749).length < 2 ^ (prefixWord ++ tailWord_553749).sum := by decide
  have hdescent : baseEnd_553749 < baseStart_553749 := by decide
  rcases family_descends (prefixWord ++ tailWord_553749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553793 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_553793 : Nat := 118140960795 + 553793 * 2 ^ 59
def prefixEnd_553793 : Nat := 4983230072969 + 3 ^ 40 * 553793 * 2
def baseEnd_553793 : Nat := 252766215195961792036141

theorem tailTrace_553793 : CollatzResearch.WordTrace tailWord_553793 prefixEnd_553793 252766215195961792036141 := by
  unfold tailWord_553793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20198490082710016159586033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13465660055140010773057355 20198490082710016159586033)
  ·
    refine ⟨15148867562032512119689525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20198490082710016159586033 15148867562032512119689525)
    ·
      refine ⟨1420206333940548011220893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15148867562032512119689525 1420206333940548011220893)
      ·
        refine ⟨532577375227705504207835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1420206333940548011220893 532577375227705504207835)
        ·
          refine ⟨798866062841558256311753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532577375227705504207835 798866062841558256311753)
          ·
            refine ⟨599149547131168692233815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798866062841558256311753 599149547131168692233815)
            ·
              refine ⟨898724320696753038350723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599149547131168692233815 898724320696753038350723)
              ·
                refine ⟨1348086481045129557526085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898724320696753038350723 1348086481045129557526085)
                ·
                  refine ⟨252766215195961792036141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348086481045129557526085 252766215195961792036141)
                  ·
                    rfl

theorem cell20_553793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_553793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553793 prefixEnd_553793 := by exact prefixLift 553793
  have htrace : WordTrace (prefixWord ++ tailWord_553793) baseStart_553793 baseEnd_553793 := by
    simpa [prefixWord, tailWord_553793, baseEnd_553793] using wordTrace_append hprefix tailTrace_553793
  have hstable : (prefixWord ++ tailWord_553793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553793).length < 2 ^ (prefixWord ++ tailWord_553793).sum := by decide
  have hdescent : baseEnd_553793 < baseStart_553793 := by decide
  rcases family_descends (prefixWord ++ tailWord_553793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553804 : List Nat := [2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_553804 : Nat := 118140960795 + 553804 * 2 ^ 59
def prefixEnd_553804 : Nat := 4983230072969 + 3 ^ 40 * 553804 * 2
def baseEnd_553804 : Nat := 84257078631898214223143

theorem tailTrace_553804 : CollatzResearch.WordTrace tailWord_553804 prefixEnd_553804 84257078631898214223143 := by
  unfold tailWord_553804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099445642835082519118233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13465927523780110025490977 10099445642835082519118233)
  ·
    refine ⟨7574584232126311889338675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10099445642835082519118233 7574584232126311889338675)
    ·
      refine ⟨11361876348189467834008013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574584232126311889338675 11361876348189467834008013)
      ·
        refine ⟨4260703630571050437753005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11361876348189467834008013 4260703630571050437753005)
        ·
          refine ⟨1597763861464143914157377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4260703630571050437753005 1597763861464143914157377)
          ·
            refine ⟨1198322896098107935618033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597763861464143914157377 1198322896098107935618033)
            ·
              refine ⟨898742172073580951713525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198322896098107935618033 898742172073580951713525)
              ·
                refine ⟨84257078631898214223143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 898742172073580951713525 84257078631898214223143)
                ·
                  rfl

theorem cell20_553804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_553804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553804 prefixEnd_553804 := by exact prefixLift 553804
  have htrace : WordTrace (prefixWord ++ tailWord_553804) baseStart_553804 baseEnd_553804 := by
    simpa [prefixWord, tailWord_553804, baseEnd_553804] using wordTrace_append hprefix tailTrace_553804
  have hstable : (prefixWord ++ tailWord_553804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553804).length < 2 ^ (prefixWord ++ tailWord_553804).sum := by decide
  have hdescent : baseEnd_553804 < baseStart_553804 := by decide
  rcases family_descends (prefixWord ++ tailWord_553804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553849 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_553849 : Nat := 118140960795 + 553849 * 2 ^ 59
def prefixEnd_553849 : Nat := 4983230072969 + 3 ^ 40 * 553849 * 2
def baseEnd_553849 : Nat := 252791775121874486169245

theorem tailTrace_553849 : CollatzResearch.WordTrace tailWord_553849 prefixEnd_553849 252791775121874486169245 := by
  unfold tailWord_553849
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200532570507137723624601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13467021713671425149083067 20200532570507137723624601)
  ·
    refine ⟨15150399427880353292718451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20200532570507137723624601 15150399427880353292718451)
    ·
      refine ⟨22725599141820529939077677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15150399427880353292718451 22725599141820529939077677)
      ·
        refine ⟨8522099678182698727154129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22725599141820529939077677 8522099678182698727154129)
        ·
          refine ⟨6391574758637024045365597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522099678182698727154129 6391574758637024045365597)
          ·
            refine ⟨2396840534488884017012099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6391574758637024045365597 2396840534488884017012099)
            ·
              refine ⟨3595260801733326025518149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396840534488884017012099 3595260801733326025518149)
              ·
                refine ⟨674111400324998629784653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3595260801733326025518149 674111400324998629784653)
                ·
                  refine ⟨252791775121874486169245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674111400324998629784653 252791775121874486169245)
                  ·
                    rfl

theorem cell20_553849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_553849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553849 prefixEnd_553849 := by exact prefixLift 553849
  have htrace : WordTrace (prefixWord ++ tailWord_553849) baseStart_553849 baseEnd_553849 := by
    simpa [prefixWord, tailWord_553849, baseEnd_553849] using wordTrace_append hprefix tailTrace_553849
  have hstable : (prefixWord ++ tailWord_553849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553849).length < 2 ^ (prefixWord ++ tailWord_553849).sum := by decide
  have hdescent : baseEnd_553849 < baseStart_553849 := by decide
  rcases family_descends (prefixWord ++ tailWord_553849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553866 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_553866 : Nat := 118140960795 + 553866 * 2 ^ 59
def prefixEnd_553866 : Nat := 4983230072969 + 3 ^ 40 * 553866 * 2
def baseEnd_553866 : Nat := 252799534385097982602509

theorem tailTrace_553866 : CollatzResearch.WordTrace tailWord_553866 prefixEnd_553866 252799534385097982602509 := by
  unfold tailWord_553866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050288152861387406748363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13467435074297033084662301 5050288152861387406748363)
  ·
    refine ⟨7575432229292081110122545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5050288152861387406748363 7575432229292081110122545)
    ·
      refine ⟨5681574171969060832591909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7575432229292081110122545 5681574171969060832591909)
      ·
        refine ⟨1065295157244198906110983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5681574171969060832591909 1065295157244198906110983)
        ·
          refine ⟨1597942735866298359166475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065295157244198906110983 1597942735866298359166475)
          ·
            refine ⟨2396914103799447538749713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597942735866298359166475 2396914103799447538749713)
            ·
              refine ⟨1797685577849585654062285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396914103799447538749713 1797685577849585654062285)
              ·
                refine ⟨674132091693594620273357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797685577849585654062285 674132091693594620273357)
                ·
                  refine ⟨252799534385097982602509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674132091693594620273357 252799534385097982602509)
                  ·
                    rfl

theorem cell20_553866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_553866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553866 prefixEnd_553866 := by exact prefixLift 553866
  have htrace : WordTrace (prefixWord ++ tailWord_553866) baseStart_553866 baseEnd_553866 := by
    simpa [prefixWord, tailWord_553866, baseEnd_553866] using wordTrace_append hprefix tailTrace_553866
  have hstable : (prefixWord ++ tailWord_553866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553866).length < 2 ^ (prefixWord ++ tailWord_553866).sum := by decide
  have hdescent : baseEnd_553866 < baseStart_553866 := by decide
  rcases family_descends (prefixWord ++ tailWord_553866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553890 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_553890 : Nat := 118140960795 + 553890 * 2 ^ 59
def prefixEnd_553890 : Nat := 4983230072969 + 3 ^ 40 * 553890 * 2
def baseEnd_553890 : Nat := 252810488639060565802411

theorem tailTrace_553890 : CollatzResearch.WordTrace tailWord_553890 prefixEnd_553890 252810488639060565802411 := by
  unfold tailWord_553890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050506990839650431466781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13468018642239067817244749 5050506990839650431466781)
  ·
    refine ⟨1893940121564868911800043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5050506990839650431466781 1893940121564868911800043)
    ·
      refine ⟨2840910182347303367700065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1893940121564868911800043 2840910182347303367700065)
      ·
        refine ⟨2130682636760477525775049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2840910182347303367700065 2130682636760477525775049)
        ·
          refine ⟨1598011977570358144331287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130682636760477525775049 1598011977570358144331287)
          ·
            refine ⟨2397017966355537216496931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598011977570358144331287 2397017966355537216496931)
            ·
              refine ⟨3595526949533305824745397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397017966355537216496931 3595526949533305824745397)
              ·
                refine ⟨337080651518747421069881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3595526949533305824745397 337080651518747421069881)
                ·
                  refine ⟨252810488639060565802411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337080651518747421069881 252810488639060565802411)
                  ·
                    rfl

theorem cell20_553890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_553890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553890 prefixEnd_553890 := by exact prefixLift 553890
  have htrace : WordTrace (prefixWord ++ tailWord_553890) baseStart_553890 baseEnd_553890 := by
    simpa [prefixWord, tailWord_553890, baseEnd_553890] using wordTrace_append hprefix tailTrace_553890
  have hstable : (prefixWord ++ tailWord_553890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553890).length < 2 ^ (prefixWord ++ tailWord_553890).sum := by decide
  have hdescent : baseEnd_553890 < baseStart_553890 := by decide
  rcases family_descends (prefixWord ++ tailWord_553890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553911 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 2]
def baseStart_553911 : Nat := 118140960795 + 553911 * 2 ^ 59
def prefixEnd_553911 : Nat := 4983230072969 + 3 ^ 40 * 553911 * 2
def baseEnd_553911 : Nat := 252820073611277826102325

theorem tailTrace_553911 : CollatzResearch.WordTrace tailWord_553911 prefixEnd_553911 252820073611277826102325 := by
  unfold tailWord_553911
  simp only [CollatzResearch.WordTrace]
  refine ⟨20202793896282522312381587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13468529264188348208254391 20202793896282522312381587)
  ·
    refine ⟨30304190844423783468572381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20202793896282522312381587 30304190844423783468572381)
    ·
      refine ⟨11364071566658918800714643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30304190844423783468572381 11364071566658918800714643)
      ·
        refine ⟨17046107349988378201071965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364071566658918800714643 17046107349988378201071965)
        ·
          refine ⟨6392290256245641825401987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17046107349988378201071965 6392290256245641825401987)
          ·
            refine ⟨9588435384368462738102981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6392290256245641825401987 9588435384368462738102981)
            ·
              refine ⟨1797831634569086763394309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9588435384368462738102981 1797831634569086763394309)
              ·
                refine ⟨337093431481703768136433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1797831634569086763394309 337093431481703768136433)
                ·
                  refine ⟨252820073611277826102325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337093431481703768136433 252820073611277826102325)
                  ·
                    rfl

theorem cell20_553911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2].length) (baseStart_553911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553911 prefixEnd_553911 := by exact prefixLift 553911
  have htrace : WordTrace (prefixWord ++ tailWord_553911) baseStart_553911 baseEnd_553911 := by
    simpa [prefixWord, tailWord_553911, baseEnd_553911] using wordTrace_append hprefix tailTrace_553911
  have hstable : (prefixWord ++ tailWord_553911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553911).length < 2 ^ (prefixWord ++ tailWord_553911).sum := by decide
  have hdescent : baseEnd_553911 < baseStart_553911 := by decide
  rcases family_descends (prefixWord ++ tailWord_553911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553932 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_553932 : Nat := 118140960795 + 553932 * 2 ^ 59
def prefixEnd_553932 : Nat := 4983230072969 + 3 ^ 40 * 553932 * 2
def baseEnd_553932 : Nat := 252829658583495086402239

theorem tailTrace_553932 : CollatzResearch.WordTrace tailWord_553932 prefixEnd_553932 252829658583495086402239 := by
  unfold tailWord_553932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101779914603221449448025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13469039886137628599264033 10101779914603221449448025)
  ·
    refine ⟨7576334935952416087086019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10101779914603221449448025 7576334935952416087086019)
    ·
      refine ⟨11364502403928624130629029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7576334935952416087086019 11364502403928624130629029)
      ·
        refine ⟨2130844200736617024492943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11364502403928624130629029 2130844200736617024492943)
        ·
          refine ⟨3196266301104925536739415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130844200736617024492943 3196266301104925536739415)
          ·
            refine ⟨4794399451657388305109123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196266301104925536739415 4794399451657388305109123)
            ·
              refine ⟨7191599177486082457663685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794399451657388305109123 7191599177486082457663685)
              ·
                refine ⟨1348424845778640460811941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7191599177486082457663685 1348424845778640460811941)
                ·
                  refine ⟨252829658583495086402239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348424845778640460811941 252829658583495086402239)
                  ·
                    rfl

theorem cell20_553932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_553932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553932 prefixEnd_553932 := by exact prefixLift 553932
  have htrace : WordTrace (prefixWord ++ tailWord_553932) baseStart_553932 baseEnd_553932 := by
    simpa [prefixWord, tailWord_553932, baseEnd_553932] using wordTrace_append hprefix tailTrace_553932
  have hstable : (prefixWord ++ tailWord_553932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553932).length < 2 ^ (prefixWord ++ tailWord_553932).sum := by decide
  have hdescent : baseEnd_553932 < baseStart_553932 := by decide
  rcases family_descends (prefixWord ++ tailWord_553932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553942 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_553942 : Nat := 118140960795 + 553942 * 2 ^ 59
def prefixEnd_553942 : Nat := 4983230072969 + 3 ^ 40 * 553942 * 2
def baseEnd_553942 : Nat := 252834222855979496068865

theorem tailTrace_553942 : CollatzResearch.WordTrace tailWord_553942 prefixEnd_553942 252834222855979496068865 := by
  unfold tailWord_553942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262745284948138412922505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13469283039446809737840053 1262745284948138412922505)
  ·
    refine ⟨947058963711103809691879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1262745284948138412922505 947058963711103809691879)
    ·
      refine ⟨1420588445566655714537819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947058963711103809691879 1420588445566655714537819)
      ·
        refine ⟨2130882668349983571806729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420588445566655714537819 2130882668349983571806729)
        ·
          refine ⟨1598162001262487678855047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130882668349983571806729 1598162001262487678855047)
          ·
            refine ⟨2397243001893731518282571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598162001262487678855047 2397243001893731518282571)
            ·
              refine ⟨3595864502840597277423857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397243001893731518282571 3595864502840597277423857)
              ·
                refine ⟨2696898377130447958067893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3595864502840597277423857 2696898377130447958067893)
                ·
                  refine ⟨252834222855979496068865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696898377130447958067893 252834222855979496068865)
                  ·
                    rfl

theorem cell20_553942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_553942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553942 prefixEnd_553942 := by exact prefixLift 553942
  have htrace : WordTrace (prefixWord ++ tailWord_553942) baseStart_553942 baseEnd_553942 := by
    simpa [prefixWord, tailWord_553942, baseEnd_553942] using wordTrace_append hprefix tailTrace_553942
  have hstable : (prefixWord ++ tailWord_553942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553942).length < 2 ^ (prefixWord ++ tailWord_553942).sum := by decide
  have hdescent : baseEnd_553942 < baseStart_553942 := by decide
  rcases family_descends (prefixWord ++ tailWord_553942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553966 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_553966 : Nat := 118140960795 + 553966 * 2 ^ 59
def prefixEnd_553966 : Nat := 4983230072969 + 3 ^ 40 * 553966 * 2
def baseEnd_553966 : Nat := 252845177109942079268767

theorem tailTrace_553966 : CollatzResearch.WordTrace tailWord_553966 prefixEnd_553966 252845177109942079268767 := by
  unfold tailWord_553966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525599988885408338204219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13469866607388844470422501 2525599988885408338204219)
  ·
    refine ⟨3788399983328112507306329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2525599988885408338204219 3788399983328112507306329)
    ·
      refine ⟨2841299987496084380479747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3788399983328112507306329 2841299987496084380479747)
      ·
        refine ⟨4261949981244126570719621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841299987496084380479747 4261949981244126570719621)
        ·
          refine ⟨799115621483273732009929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4261949981244126570719621 799115621483273732009929)
          ·
            refine ⟨599336716112455299007447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799115621483273732009929 599336716112455299007447)
            ·
              refine ⟨899005074168682948511171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599336716112455299007447 899005074168682948511171)
              ·
                refine ⟨1348507611253024422766757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899005074168682948511171 1348507611253024422766757)
                ·
                  refine ⟨252845177109942079268767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348507611253024422766757 252845177109942079268767)
                  ·
                    rfl

theorem cell20_553966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_553966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553966 prefixEnd_553966 := by exact prefixLift 553966
  have htrace : WordTrace (prefixWord ++ tailWord_553966) baseStart_553966 baseEnd_553966 := by
    simpa [prefixWord, tailWord_553966, baseEnd_553966] using wordTrace_append hprefix tailTrace_553966
  have hstable : (prefixWord ++ tailWord_553966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553966).length < 2 ^ (prefixWord ++ tailWord_553966).sum := by decide
  have hdescent : baseEnd_553966 < baseStart_553966 := by decide
  rcases family_descends (prefixWord ++ tailWord_553966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553977 : List Nat := [1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_553977 : Nat := 118140960795 + 553977 * 2 ^ 59
def prefixEnd_553977 : Nat := 4983230072969 + 3 ^ 40 * 553977 * 2
def baseEnd_553977 : Nat := 84283399269891643300685

theorem tailTrace_553977 : CollatzResearch.WordTrace tailWord_553977 prefixEnd_553977 84283399269891643300685 := by
  unfold tailWord_553977
  simp only [CollatzResearch.WordTrace]
  refine ⟨20205201114043415584284185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13470134076028943722856123 20205201114043415584284185)
  ·
    refine ⟨15153900835532561688213139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20205201114043415584284185 15153900835532561688213139)
    ·
      refine ⟨22730851253298842532319709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15153900835532561688213139 22730851253298842532319709)
      ·
        refine ⟨8524069219987065949619891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22730851253298842532319709 8524069219987065949619891)
        ·
          refine ⟨12786103829980598924429837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524069219987065949619891 12786103829980598924429837)
          ·
            refine ⟨4794788936242724596661189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12786103829980598924429837 4794788936242724596661189)
            ·
              refine ⟨899022925545510861873973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4794788936242724596661189 899022925545510861873973)
              ·
                refine ⟨84283399269891643300685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 899022925545510861873973 84283399269891643300685)
                ·
                  rfl

theorem cell20_553977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_553977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553977 prefixEnd_553977 := by exact prefixLift 553977
  have htrace : WordTrace (prefixWord ++ tailWord_553977) baseStart_553977 baseEnd_553977 := by
    simpa [prefixWord, tailWord_553977, baseEnd_553977] using wordTrace_append hprefix tailTrace_553977
  have hstable : (prefixWord ++ tailWord_553977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553977).length < 2 ^ (prefixWord ++ tailWord_553977).sum := by decide
  have hdescent : baseEnd_553977 < baseStart_553977 := by decide
  rcases family_descends (prefixWord ++ tailWord_553977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553980 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_553980 : Nat := 118140960795 + 553980 * 2 ^ 59
def prefixEnd_553980 : Nat := 4983230072969 + 3 ^ 40 * 553980 * 2
def baseEnd_553980 : Nat := 252851567091420252802043

theorem tailTrace_553980 : CollatzResearch.WordTrace tailWord_553980 prefixEnd_553980 252851567091420252802043 := by
  unfold tailWord_553980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102655266516273548321697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13470207022021698064428929 10102655266516273548321697)
  ·
    refine ⟨7576991449887205161241273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10102655266516273548321697 7576991449887205161241273)
    ·
      refine ⟨5682743587415403870930955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7576991449887205161241273 5682743587415403870930955)
      ·
        refine ⟨8524115381123105806396433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5682743587415403870930955 8524115381123105806396433)
        ·
          refine ⟨6393086535842329354797325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8524115381123105806396433 6393086535842329354797325)
          ·
            refine ⟨2397407450940873508048997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6393086535842329354797325 2397407450940873508048997)
            ·
              refine ⟨449513897051413782759187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2397407450940873508048997 449513897051413782759187)
              ·
                refine ⟨674270845577120674138781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449513897051413782759187 674270845577120674138781)
                ·
                  refine ⟨252851567091420252802043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674270845577120674138781 252851567091420252802043)
                  ·
                    rfl

theorem cell20_553980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_553980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_553980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_553980 prefixEnd_553980 := by exact prefixLift 553980
  have htrace : WordTrace (prefixWord ++ tailWord_553980) baseStart_553980 baseEnd_553980 := by
    simpa [prefixWord, tailWord_553980, baseEnd_553980] using wordTrace_append hprefix tailTrace_553980
  have hstable : (prefixWord ++ tailWord_553980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553980).length < 2 ^ (prefixWord ++ tailWord_553980).sum := by decide
  have hdescent : baseEnd_553980 < baseStart_553980 := by decide
  rcases family_descends (prefixWord ++ tailWord_553980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554018 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_554018 : Nat := 118140960795 + 554018 * 2 ^ 59
def prefixEnd_554018 : Nat := 4983230072969 + 3 ^ 40 * 554018 * 2
def baseEnd_554018 : Nat := 252868911326861009535221

theorem tailTrace_554018 : CollatzResearch.WordTrace tailWord_554018 prefixEnd_554018 252868911326861009535221 := by
  unfold tailWord_554018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051674126723719896631677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13471131004596586391017805 5051674126723719896631677)
  ·
    refine ⟨1894377797521394961236879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5051674126723719896631677 1894377797521394961236879)
    ·
      refine ⟨2841566696282092441855319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894377797521394961236879 2841566696282092441855319)
      ·
        refine ⟨4262350044423138662782979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841566696282092441855319 4262350044423138662782979)
        ·
          refine ⟨6393525066634707994174469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262350044423138662782979 6393525066634707994174469)
          ·
            refine ⟨1198785949994007748907713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6393525066634707994174469 1198785949994007748907713)
            ·
              refine ⟨899089462495505811680785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198785949994007748907713 899089462495505811680785)
              ·
                refine ⟨674317096871629358760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899089462495505811680785 674317096871629358760589)
                ·
                  refine ⟨252868911326861009535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674317096871629358760589 252868911326861009535221)
                  ·
                    rfl

theorem cell20_554018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_554018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554018 prefixEnd_554018 := by exact prefixLift 554018
  have htrace : WordTrace (prefixWord ++ tailWord_554018) baseStart_554018 baseEnd_554018 := by
    simpa [prefixWord, tailWord_554018, baseEnd_554018] using wordTrace_append hprefix tailTrace_554018
  have hstable : (prefixWord ++ tailWord_554018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554018).length < 2 ^ (prefixWord ++ tailWord_554018).sum := by decide
  have hdescent : baseEnd_554018 < baseStart_554018 := by decide
  rcases family_descends (prefixWord ++ tailWord_554018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554049 : List Nat := [1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_554049 : Nat := 118140960795 + 554049 * 2 ^ 59
def prefixEnd_554049 : Nat := 4983230072969 + 3 ^ 40 * 554049 * 2
def baseEnd_554049 : Nat := 84294353523854226500587

theorem tailTrace_554049 : CollatzResearch.WordTrace tailWord_554049 prefixEnd_554049 84294353523854226500587 := by
  unfold tailWord_554049
  simp only [CollatzResearch.WordTrace]
  refine ⟨20207827169782571880905201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13471884779855047920603467 20207827169782571880905201)
  ·
    refine ⟨15155870377336928910678901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20207827169782571880905201 15155870377336928910678901)
    ·
      refine ⟨1420862847875337085376147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15155870377336928910678901 1420862847875337085376147)
      ·
        refine ⟨2131294271813005628064221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420862847875337085376147 2131294271813005628064221)
        ·
          refine ⟨799235351929877110524083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2131294271813005628064221 799235351929877110524083)
          ·
            refine ⟨1198853027894815665786125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799235351929877110524083 1198853027894815665786125)
            ·
              refine ⟨449569885460555874669797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1198853027894815665786125 449569885460555874669797)
              ·
                refine ⟨84294353523854226500587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449569885460555874669797 84294353523854226500587)
                ·
                  rfl

theorem cell20_554049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_554049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554049 prefixEnd_554049 := by exact prefixLift 554049
  have htrace : WordTrace (prefixWord ++ tailWord_554049) baseStart_554049 baseEnd_554049 := by
    simpa [prefixWord, tailWord_554049, baseEnd_554049] using wordTrace_append hprefix tailTrace_554049
  have hstable : (prefixWord ++ tailWord_554049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554049).length < 2 ^ (prefixWord ++ tailWord_554049).sum := by decide
  have hdescent : baseEnd_554049 < baseStart_554049 := by decide
  rcases family_descends (prefixWord ++ tailWord_554049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554060 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_554060 : Nat := 118140960795 + 554060 * 2 ^ 59
def prefixEnd_554060 : Nat := 4983230072969 + 3 ^ 40 * 554060 * 2
def baseEnd_554060 : Nat := 252888081271295530135049

theorem tailTrace_554060 : CollatzResearch.WordTrace tailWord_554060 prefixEnd_554060 252888081271295530135049 := by
  unfold tailWord_554060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104114186371360379777817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13472152248495147173037089 10104114186371360379777817)
  ·
    refine ⟨7578085639778520284833363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10104114186371360379777817 7578085639778520284833363)
    ·
      refine ⟨11367128459667780427250045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578085639778520284833363 11367128459667780427250045)
      ·
        refine ⟨4262673172375417660218767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11367128459667780427250045 4262673172375417660218767)
        ·
          refine ⟨6394009758563126490328151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262673172375417660218767 6394009758563126490328151)
          ·
            refine ⟨9591014637844689735492227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394009758563126490328151 9591014637844689735492227)
            ·
              refine ⟨14386521956767034603238341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591014637844689735492227 14386521956767034603238341)
              ·
                refine ⟨2697472866893818988107189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14386521956767034603238341 2697472866893818988107189)
                ·
                  refine ⟨252888081271295530135049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2697472866893818988107189 252888081271295530135049)
                  ·
                    rfl

theorem cell20_554060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_554060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554060 prefixEnd_554060 := by exact prefixLift 554060
  have htrace : WordTrace (prefixWord ++ tailWord_554060) baseStart_554060 baseEnd_554060 := by
    simpa [prefixWord, tailWord_554060, baseEnd_554060] using wordTrace_append hprefix tailTrace_554060
  have hstable : (prefixWord ++ tailWord_554060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554060).length < 2 ^ (prefixWord ++ tailWord_554060).sum := by decide
  have hdescent : baseEnd_554060 < baseStart_554060 := by decide
  rcases family_descends (prefixWord ++ tailWord_554060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554110 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_554110 : Nat := 118140960795 + 554110 * 2 ^ 59
def prefixEnd_554110 : Nat := 4983230072969 + 3 ^ 40 * 554110 * 2
def baseEnd_554110 : Nat := 252910902633717578468179

theorem tailTrace_554110 : CollatzResearch.WordTrace tailWord_554110 prefixEnd_554110 252910902633717578468179 := by
  unfold tailWord_554110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526256502820197412359473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13473368015041052865917189 2526256502820197412359473)
  ·
    refine ⟨1894692377115148059269605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2526256502820197412359473 1894692377115148059269605)
    ·
      refine ⟨355254820709090261113051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1894692377115148059269605 355254820709090261113051)
      ·
        refine ⟨532882231063635391669577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355254820709090261113051 532882231063635391669577)
        ·
          refine ⟨399661673297726543752183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532882231063635391669577 399661673297726543752183)
          ·
            refine ⟨599492509946589815628275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399661673297726543752183 599492509946589815628275)
            ·
              refine ⟨899238764919884723442413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599492509946589815628275 899238764919884723442413)
              ·
                refine ⟨337214536844956771290905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899238764919884723442413 337214536844956771290905)
                ·
                  refine ⟨252910902633717578468179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337214536844956771290905 252910902633717578468179)
                  ·
                    rfl

theorem cell20_554110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_554110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554110 prefixEnd_554110 := by exact prefixLift 554110
  have htrace : WordTrace (prefixWord ++ tailWord_554110) baseStart_554110 baseEnd_554110 := by
    simpa [prefixWord, tailWord_554110, baseEnd_554110] using wordTrace_append hprefix tailTrace_554110
  have hstable : (prefixWord ++ tailWord_554110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554110).length < 2 ^ (prefixWord ++ tailWord_554110).sum := by decide
  have hdescent : baseEnd_554110 < baseStart_554110 := by decide
  rcases family_descends (prefixWord ++ tailWord_554110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554188 : List Nat := [2, 2, 1, 15]
def baseStart_554188 : Nat := 118140960795 + 554188 * 2 ^ 59
def prefixEnd_554188 : Nat := 4983230072969 + 3 ^ 40 * 554188 * 2
def baseEnd_554188 : Nat := 1040932115058008122913

theorem tailTrace_554188 : CollatzResearch.WordTrace tailWord_554188 prefixEnd_554188 1040932115058008122913 := by
  unfold tailWord_554188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10106448458139499310107609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13475264610852665746810145 10106448458139499310107609)
  ·
    refine ⟨7579836343604624482580707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10106448458139499310107609 7579836343604624482580707)
    ·
      refine ⟨11369754515406936723871061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7579836343604624482580707 11369754515406936723871061)
      ·
        refine ⟨1040932115058008122913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 11369754515406936723871061 1040932115058008122913)
        ·
          rfl

theorem cell20_554188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 15].length) (baseStart_554188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554188 prefixEnd_554188 := by exact prefixLift 554188
  have htrace : WordTrace (prefixWord ++ tailWord_554188) baseStart_554188 baseEnd_554188 := by
    simpa [prefixWord, tailWord_554188, baseEnd_554188] using wordTrace_append hprefix tailTrace_554188
  have hstable : (prefixWord ++ tailWord_554188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554188).length < 2 ^ (prefixWord ++ tailWord_554188).sum := by decide
  have hdescent : baseEnd_554188 < baseStart_554188 := by decide
  rcases family_descends (prefixWord ++ tailWord_554188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554190 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_554190 : Nat := 118140960795 + 554190 * 2 ^ 59
def prefixEnd_554190 : Nat := 4983230072969 + 3 ^ 40 * 554190 * 2
def baseEnd_554190 : Nat := 252947416813592855801185

theorem tailTrace_554190 : CollatzResearch.WordTrace tailWord_554190 prefixEnd_554190 252947416813592855801185 := by
  unfold tailWord_554190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526621232783969120223503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13475313241514501974525349 2526621232783969120223503)
  ·
    refine ⟨3789931849175953680335255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526621232783969120223503 3789931849175953680335255)
    ·
      refine ⟨5684897773763930520502883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789931849175953680335255 5684897773763930520502883)
      ·
        refine ⟨8527346660645895780754325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5684897773763930520502883 8527346660645895780754325)
        ·
          refine ⟨399719374717776364722859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8527346660645895780754325 399719374717776364722859)
          ·
            refine ⟨599579062076664547084289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399719374717776364722859 599579062076664547084289)
            ·
              refine ⟨449684296557498410313217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599579062076664547084289 449684296557498410313217)
              ·
                refine ⟨337263222418123807734913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449684296557498410313217 337263222418123807734913)
                ·
                  refine ⟨252947416813592855801185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337263222418123807734913 252947416813592855801185)
                  ·
                    rfl

theorem cell20_554190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_554190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554190 prefixEnd_554190 := by exact prefixLift 554190
  have htrace : WordTrace (prefixWord ++ tailWord_554190) baseStart_554190 baseEnd_554190 := by
    simpa [prefixWord, tailWord_554190, baseEnd_554190] using wordTrace_append hprefix tailTrace_554190
  have hstable : (prefixWord ++ tailWord_554190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554190).length < 2 ^ (prefixWord ++ tailWord_554190).sum := by decide
  have hdescent : baseEnd_554190 < baseStart_554190 := by decide
  rcases family_descends (prefixWord ++ tailWord_554190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554215 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_554215 : Nat := 118140960795 + 554215 * 2 ^ 59
def prefixEnd_554215 : Nat := 4983230072969 + 3 ^ 40 * 554215 * 2
def baseEnd_554215 : Nat := 252958827494803879967749

theorem tailTrace_554215 : CollatzResearch.WordTrace tailWord_554215 prefixEnd_554215 252958827494803879967749 := by
  unfold tailWord_554215
  simp only [CollatzResearch.WordTrace]
  refine ⟨20213881687181182231448099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13475921124787454820965399 20213881687181182231448099)
  ·
    refine ⟨30320822530771773347172149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20213881687181182231448099 30320822530771773347172149)
    ·
      refine ⟨2842577112259853751297389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30320822530771773347172149 2842577112259853751297389)
      ·
        refine ⟨1065966417097445156736521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2842577112259853751297389 1065966417097445156736521)
        ·
          refine ⟨799474812823083867552391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1065966417097445156736521 799474812823083867552391)
          ·
            refine ⟨1199212219234625801328587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799474812823083867552391 1199212219234625801328587)
            ·
              refine ⟨1798818328851938701992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199212219234625801328587 1798818328851938701992881)
              ·
                refine ⟨1349113746638954026494661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798818328851938701992881 1349113746638954026494661)
                ·
                  refine ⟨252958827494803879967749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349113746638954026494661 252958827494803879967749)
                  ·
                    rfl

theorem cell20_554215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_554215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554215 prefixEnd_554215 := by exact prefixLift 554215
  have htrace : WordTrace (prefixWord ++ tailWord_554215) baseStart_554215 baseEnd_554215 := by
    simpa [prefixWord, tailWord_554215, baseEnd_554215] using wordTrace_append hprefix tailTrace_554215
  have hstable : (prefixWord ++ tailWord_554215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554215).length < 2 ^ (prefixWord ++ tailWord_554215).sum := by decide
  have hdescent : baseEnd_554215 < baseStart_554215 := by decide
  rcases family_descends (prefixWord ++ tailWord_554215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554219 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_554219 : Nat := 118140960795 + 554219 * 2 ^ 59
def prefixEnd_554219 : Nat := 4983230072969 + 3 ^ 40 * 554219 * 2
def baseEnd_554219 : Nat := 252960653203797643834399

theorem tailTrace_554219 : CollatzResearch.WordTrace tailWord_554219 prefixEnd_554219 252960653203797643834399 := by
  unfold tailWord_554219
  simp only [CollatzResearch.WordTrace]
  refine ⟨20214027579166690914593711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13476018386111127276395807 20214027579166690914593711)
  ·
    refine ⟨30321041368750036371890567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20214027579166690914593711 30321041368750036371890567)
    ·
      refine ⟨45481562053125054557835851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30321041368750036371890567 45481562053125054557835851)
      ·
        refine ⟨68222343079687581836753777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45481562053125054557835851 68222343079687581836753777)
        ·
          refine ⟨51166757309765686377565333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68222343079687581836753777 51166757309765686377565333)
          ·
            refine ⟨2398441748895266548948375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51166757309765686377565333 2398441748895266548948375)
            ·
              refine ⟨3597662623342899823422563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398441748895266548948375 3597662623342899823422563)
              ·
                refine ⟨5396493935014349735133845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597662623342899823422563 5396493935014349735133845)
                ·
                  refine ⟨252960653203797643834399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5396493935014349735133845 252960653203797643834399)
                  ·
                    rfl

theorem cell20_554219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_554219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554219 prefixEnd_554219 := by exact prefixLift 554219
  have htrace : WordTrace (prefixWord ++ tailWord_554219) baseStart_554219 baseEnd_554219 := by
    simpa [prefixWord, tailWord_554219, baseEnd_554219] using wordTrace_append hprefix tailTrace_554219
  have hstable : (prefixWord ++ tailWord_554219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554219).length < 2 ^ (prefixWord ++ tailWord_554219).sum := by decide
  have hdescent : baseEnd_554219 < baseStart_554219 := by decide
  rcases family_descends (prefixWord ++ tailWord_554219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554242 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_554242 : Nat := 118140960795 + 554242 * 2 ^ 59
def prefixEnd_554242 : Nat := 4983230072969 + 3 ^ 40 * 554242 * 2
def baseEnd_554242 : Nat := 252971151030511786067639

theorem tailTrace_554242 : CollatzResearch.WordTrace tailWord_554242 prefixEnd_554242 252971151030511786067639 := by
  unfold tailWord_554242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053716614520841460670245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13476577638722243895120653 5053716614520841460670245)
  ·
    refine ⟨947571865222657773875671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5053716614520841460670245 947571865222657773875671)
    ·
      refine ⟨1421357797833986660813507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947571865222657773875671 1421357797833986660813507)
      ·
        refine ⟨2132036696750979991220261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421357797833986660813507 2132036696750979991220261)
        ·
          refine ⟨399756880640808748353799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2132036696750979991220261 399756880640808748353799)
          ·
            refine ⟨599635320961213122530699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399756880640808748353799 599635320961213122530699)
            ·
              refine ⟨899452981441819683796049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599635320961213122530699 899452981441819683796049)
              ·
                refine ⟨674589736081364762847037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899452981441819683796049 674589736081364762847037)
                ·
                  refine ⟨252971151030511786067639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674589736081364762847037 252971151030511786067639)
                  ·
                    rfl

theorem cell20_554242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_554242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554242 prefixEnd_554242 := by exact prefixLift 554242
  have htrace : WordTrace (prefixWord ++ tailWord_554242) baseStart_554242 baseEnd_554242 := by
    simpa [prefixWord, tailWord_554242, baseEnd_554242] using wordTrace_append hprefix tailTrace_554242
  have hstable : (prefixWord ++ tailWord_554242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554242).length < 2 ^ (prefixWord ++ tailWord_554242).sum := by decide
  have hdescent : baseEnd_554242 < baseStart_554242 := by decide
  rcases family_descends (prefixWord ++ tailWord_554242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554291 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 2]
def baseStart_554291 : Nat := 118140960795 + 554291 * 2 ^ 59
def prefixEnd_554291 : Nat := 4983230072969 + 3 ^ 40 * 554291 * 2
def baseEnd_554291 : Nat := 252993515965685393434105

theorem tailTrace_554291 : CollatzResearch.WordTrace tailWord_554291 prefixEnd_554291 252993515965685393434105 := by
  unfold tailWord_554291
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216653634905847211214727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13477769089937231474143151 20216653634905847211214727)
  ·
    refine ⟨30324980452358770816822091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20216653634905847211214727 30324980452358770816822091)
    ·
      refine ⟨45487470678538156225233137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30324980452358770816822091 45487470678538156225233137)
      ·
        refine ⟨34115603008903617168924853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45487470678538156225233137 34115603008903617168924853)
        ·
          refine ⟨3198337782084714109586705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34115603008903617168924853 3198337782084714109586705)
          ·
            refine ⟨2398753336563535582190029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198337782084714109586705 2398753336563535582190029)
            ·
              refine ⟨899532501211325843321261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2398753336563535582190029 899532501211325843321261)
              ·
                refine ⟨337324687954247191245473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899532501211325843321261 337324687954247191245473)
                ·
                  refine ⟨252993515965685393434105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337324687954247191245473 252993515965685393434105)
                  ·
                    rfl

theorem cell20_554291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2].length) (baseStart_554291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554291 prefixEnd_554291 := by exact prefixLift 554291
  have htrace : WordTrace (prefixWord ++ tailWord_554291) baseStart_554291 baseEnd_554291 := by
    simpa [prefixWord, tailWord_554291, baseEnd_554291] using wordTrace_append hprefix tailTrace_554291
  have hstable : (prefixWord ++ tailWord_554291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554291).length < 2 ^ (prefixWord ++ tailWord_554291).sum := by decide
  have hdescent : baseEnd_554291 < baseStart_554291 := by decide
  rcases family_descends (prefixWord ++ tailWord_554291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554294 : List Nat := [5, 1, 2, 3, 2, 1, 6]
def baseStart_554294 : Nat := 118140960795 + 554294 * 2 ^ 59
def prefixEnd_554294 : Nat := 4983230072969 + 3 ^ 40 * 554294 * 2
def baseEnd_554294 : Nat := 28110542805270079592677

theorem tailTrace_554294 : CollatzResearch.WordTrace tailWord_554294 prefixEnd_554294 28110542805270079592677 := by
  unfold tailWord_554294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263547690868436170223371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13477842035929985815715957 1263547690868436170223371)
  ·
    refine ⟨1895321536302654255335057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263547690868436170223371 1895321536302654255335057)
    ·
      refine ⟨1421491152226990691501293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895321536302654255335057 1421491152226990691501293)
      ·
        refine ⟨533059182085121509312985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1421491152226990691501293 533059182085121509312985)
        ·
          refine ⟨399794386563841131984739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533059182085121509312985 399794386563841131984739)
          ·
            refine ⟨599691579845761697977109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399794386563841131984739 599691579845761697977109)
            ·
              refine ⟨28110542805270079592677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 599691579845761697977109 28110542805270079592677)
              ·
                rfl

theorem cell20_554294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_554294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554294 prefixEnd_554294 := by exact prefixLift 554294
  have htrace : WordTrace (prefixWord ++ tailWord_554294) baseStart_554294 baseEnd_554294 := by
    simpa [prefixWord, tailWord_554294, baseEnd_554294] using wordTrace_append hprefix tailTrace_554294
  have hstable : (prefixWord ++ tailWord_554294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554294).length < 2 ^ (prefixWord ++ tailWord_554294).sum := by decide
  have hdescent : baseEnd_554294 < baseStart_554294 := by decide
  rcases family_descends (prefixWord ++ tailWord_554294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554305 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_554305 : Nat := 118140960795 + 554305 * 2 ^ 59
def prefixEnd_554305 : Nat := 4983230072969 + 3 ^ 40 * 554305 * 2
def baseEnd_554305 : Nat := 252999905947163566967381

theorem tailTrace_554305 : CollatzResearch.WordTrace tailWord_554305 prefixEnd_554305 252999905947163566967381 := by
  unfold tailWord_554305
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217164256855127602224369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13478109504570085068149579 20217164256855127602224369)
  ·
    refine ⟨15162873192641345701668277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20217164256855127602224369 15162873192641345701668277)
    ·
      refine ⟨1421519361810126159531401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15162873192641345701668277 1421519361810126159531401)
      ·
        refine ⟨1066139521357594619648551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1421519361810126159531401 1066139521357594619648551)
        ·
          refine ⟨1599209282036391929472827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066139521357594619648551 1599209282036391929472827)
          ·
            refine ⟨2398813923054587894209241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599209282036391929472827 2398813923054587894209241)
            ·
              refine ⟨1799110442290940920656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398813923054587894209241 1799110442290940920656931)
              ·
                refine ⟨2698665663436411380985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799110442290940920656931 2698665663436411380985397)
                ·
                  refine ⟨252999905947163566967381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698665663436411380985397 252999905947163566967381)
                  ·
                    rfl

theorem cell20_554305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_554305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554305 prefixEnd_554305 := by exact prefixLift 554305
  have htrace : WordTrace (prefixWord ++ tailWord_554305) baseStart_554305 baseEnd_554305 := by
    simpa [prefixWord, tailWord_554305, baseEnd_554305] using wordTrace_append hprefix tailTrace_554305
  have hstable : (prefixWord ++ tailWord_554305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554305).length < 2 ^ (prefixWord ++ tailWord_554305).sum := by decide
  have hdescent : baseEnd_554305 < baseStart_554305 := by decide
  rcases family_descends (prefixWord ++ tailWord_554305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554308 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_554308 : Nat := 118140960795 + 554308 * 2 ^ 59
def prefixEnd_554308 : Nat := 4983230072969 + 3 ^ 40 * 554308 * 2
def baseEnd_554308 : Nat := 253001275228908889867369

theorem tailTrace_554308 : CollatzResearch.WordTrace tailWord_554308 prefixEnd_554308 253001275228908889867369 := by
  unfold tailWord_554308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108636837922129557291789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13478182450562839409722385 10108636837922129557291789)
  ·
    refine ⟨3790738814220798583984421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10108636837922129557291789 3790738814220798583984421)
    ·
      refine ⟨710763527666399734497079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3790738814220798583984421 710763527666399734497079)
      ·
        refine ⟨1066145291499599601745619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710763527666399734497079 1066145291499599601745619)
        ·
          refine ⟨1599217937249399402618429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066145291499599601745619 1599217937249399402618429)
          ·
            refine ⟨599706726468524775981911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599217937249399402618429 599706726468524775981911)
            ·
              refine ⟨899560089702787163972867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599706726468524775981911 899560089702787163972867)
              ·
                refine ⟨1349340134554180745959301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899560089702787163972867 1349340134554180745959301)
                ·
                  refine ⟨253001275228908889867369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349340134554180745959301 253001275228908889867369)
                  ·
                    rfl

theorem cell20_554308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_554308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554308 prefixEnd_554308 := by exact prefixLift 554308
  have htrace : WordTrace (prefixWord ++ tailWord_554308) baseStart_554308 baseEnd_554308 := by
    simpa [prefixWord, tailWord_554308, baseEnd_554308] using wordTrace_append hprefix tailTrace_554308
  have hstable : (prefixWord ++ tailWord_554308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554308).length < 2 ^ (prefixWord ++ tailWord_554308).sum := by decide
  have hdescent : baseEnd_554308 < baseStart_554308 := by decide
  rcases family_descends (prefixWord ++ tailWord_554308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554357 : List Nat := [1, 3, 4, 1, 3, 8]
def baseStart_554357 : Nat := 118140960795 + 554357 * 2 ^ 59
def prefixEnd_554357 : Nat := 4983230072969 + 3 ^ 40 * 554357 * 2
def baseEnd_554357 : Nat := 9371245932003055453105

theorem tailTrace_554357 : CollatzResearch.WordTrace tailWord_554357 prefixEnd_554357 9371245932003055453105 := by
  unfold tailWord_554357
  simp only [CollatzResearch.WordTrace]
  refine ⟨20219060852666740483117325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13479373901777826988744883 20219060852666740483117325)
  ·
    refine ⟨7582147819750027681168997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20219060852666740483117325 7582147819750027681168997)
    ·
      refine ⟨1421652716203130190219187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7582147819750027681168997 1421652716203130190219187)
      ·
        refine ⟨2132479074304695285328781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421652716203130190219187 2132479074304695285328781)
        ·
          refine ⟨799679652864260731998293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2132479074304695285328781 799679652864260731998293)
          ·
            refine ⟨9371245932003055453105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 799679652864260731998293 9371245932003055453105)
            ·
              rfl

theorem cell20_554357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_554357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554357 prefixEnd_554357 := by exact prefixLift 554357
  have htrace : WordTrace (prefixWord ++ tailWord_554357) baseStart_554357 baseEnd_554357 := by
    simpa [prefixWord, tailWord_554357, baseEnd_554357] using wordTrace_append hprefix tailTrace_554357
  have hstable : (prefixWord ++ tailWord_554357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554357).length < 2 ^ (prefixWord ++ tailWord_554357).sum := by decide
  have hdescent : baseEnd_554357 < baseStart_554357 := by decide
  rcases family_descends (prefixWord ++ tailWord_554357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554388 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_554388 : Nat := 118140960795 + 554388 * 2 ^ 59
def prefixEnd_554388 : Nat := 4983230072969 + 3 ^ 40 * 554388 * 2
def baseEnd_554388 : Nat := 253037789408784167200375

theorem tailTrace_554388 : CollatzResearch.WordTrace tailWord_554388 prefixEnd_554388 253037789408784167200375 := by
  unfold tailWord_554388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10110095757777216388747909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13480127677036288518330545 10110095757777216388747909)
  ·
    refine ⟨1895642954583228072890233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10110095757777216388747909 1895642954583228072890233)
    ·
      refine ⟨1421732215937421054667675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895642954583228072890233 1421732215937421054667675)
      ·
        refine ⟨2132598323906131582001513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421732215937421054667675 2132598323906131582001513)
        ·
          refine ⟨1599448742929598686501135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2132598323906131582001513 1599448742929598686501135)
          ·
            refine ⟨2399173114394398029751703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599448742929598686501135 2399173114394398029751703)
            ·
              refine ⟨3598759671591597044627555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399173114394398029751703 3598759671591597044627555)
              ·
                refine ⟨5398139507387395566941333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598759671591597044627555 5398139507387395566941333)
                ·
                  refine ⟨253037789408784167200375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5398139507387395566941333 253037789408784167200375)
                  ·
                    rfl

theorem cell20_554388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_554388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554388 prefixEnd_554388 := by exact prefixLift 554388
  have htrace : WordTrace (prefixWord ++ tailWord_554388) baseStart_554388 baseEnd_554388 := by
    simpa [prefixWord, tailWord_554388, baseEnd_554388] using wordTrace_append hprefix tailTrace_554388
  have hstable : (prefixWord ++ tailWord_554388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554388).length < 2 ^ (prefixWord ++ tailWord_554388).sum := by decide
  have hdescent : baseEnd_554388 < baseStart_554388 := by decide
  rcases family_descends (prefixWord ++ tailWord_554388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554447 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_554447 : Nat := 118140960795 + 554447 * 2 ^ 59
def prefixEnd_554447 : Nat := 4983230072969 + 3 ^ 40 * 554447 * 2
def baseEnd_554447 : Nat := 253064718616442184233467

theorem tailTrace_554447 : CollatzResearch.WordTrace tailWord_554447 prefixEnd_554447 253064718616442184233467 := by
  unfold tailWord_554447
  simp only [CollatzResearch.WordTrace]
  refine ⟨20222343422340685853893595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13481562281560457235929063 20222343422340685853893595)
  ·
    refine ⟨30333515133511028780840393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20222343422340685853893595 30333515133511028780840393)
    ·
      refine ⟨22750136350133271585630295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30333515133511028780840393 22750136350133271585630295)
      ·
        refine ⟨34125204525199907378445443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22750136350133271585630295 34125204525199907378445443)
        ·
          refine ⟨51187806787799861067668165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34125204525199907378445443 51187806787799861067668165)
          ·
            refine ⟨9597713772712473950187781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51187806787799861067668165 9597713772712473950187781)
            ·
              refine ⟨1799571332383588865660209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9597713772712473950187781 1799571332383588865660209)
              ·
                refine ⟨1349678499287691649245157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799571332383588865660209 1349678499287691649245157)
                ·
                  refine ⟨253064718616442184233467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349678499287691649245157 253064718616442184233467)
                  ·
                    rfl

theorem cell20_554447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_554447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554447 prefixEnd_554447 := by exact prefixLift 554447
  have htrace : WordTrace (prefixWord ++ tailWord_554447) baseStart_554447 baseEnd_554447 := by
    simpa [prefixWord, tailWord_554447, baseEnd_554447] using wordTrace_append hprefix tailTrace_554447
  have hstable : (prefixWord ++ tailWord_554447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554447).length < 2 ^ (prefixWord ++ tailWord_554447).sum := by decide
  have hdescent : baseEnd_554447 < baseStart_554447 := by decide
  rcases family_descends (prefixWord ++ tailWord_554447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554464 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_554464 : Nat := 118140960795 + 554464 * 2 ^ 59
def prefixEnd_554464 : Nat := 4983230072969 + 3 ^ 40 * 554464 * 2
def baseEnd_554464 : Nat := 253072477879665680666731

theorem tailTrace_554464 : CollatzResearch.WordTrace tailWord_554464 prefixEnd_554464 253072477879665680666731 := by
  unfold tailWord_554464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111481731639548878631223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13481975642186065171508297 10111481731639548878631223)
  ·
    refine ⟨15167222597459323317946835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111481731639548878631223 15167222597459323317946835)
    ·
      refine ⟨22750833896188984976920253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15167222597459323317946835 22750833896188984976920253)
      ·
        refine ⟨8531562711070869366345095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22750833896188984976920253 8531562711070869366345095)
        ·
          refine ⟨12797344066606304049517643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531562711070869366345095 12797344066606304049517643)
          ·
            refine ⟨19196016099909456074276465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12797344066606304049517643 19196016099909456074276465)
            ·
              refine ⟨14397012074932092055707349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19196016099909456074276465 14397012074932092055707349)
              ·
                refine ⟨337429970506220907555641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14397012074932092055707349 337429970506220907555641)
                ·
                  refine ⟨253072477879665680666731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337429970506220907555641 253072477879665680666731)
                  ·
                    rfl

theorem cell20_554464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_554464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554464 prefixEnd_554464 := by exact prefixLift 554464
  have htrace : WordTrace (prefixWord ++ tailWord_554464) baseStart_554464 baseEnd_554464 := by
    simpa [prefixWord, tailWord_554464, baseEnd_554464] using wordTrace_append hprefix tailTrace_554464
  have hstable : (prefixWord ++ tailWord_554464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554464).length < 2 ^ (prefixWord ++ tailWord_554464).sum := by decide
  have hdescent : baseEnd_554464 < baseStart_554464 := by decide
  rcases family_descends (prefixWord ++ tailWord_554464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554471 : List Nat := [1, 1, 5, 2, 1, 4, 6]
def baseStart_554471 : Nat := 118140960795 + 554471 * 2 ^ 59
def prefixEnd_554471 : Nat := 4983230072969 + 3 ^ 40 * 554471 * 2
def baseEnd_554471 : Nat := 28119519207822751937041

theorem tailTrace_554471 : CollatzResearch.WordTrace tailWord_554471 prefixEnd_554471 28119519207822751937041 := by
  unfold tailWord_554471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223218774253737952767267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13482145849502491968511511 20223218774253737952767267)
  ·
    refine ⟨30334828161380606929150901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20223218774253737952767267 30334828161380606929150901)
    ·
      refine ⟨2843890140129431899607897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30334828161380606929150901 2843890140129431899607897)
      ·
        refine ⟨2132917605097073924705923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2843890140129431899607897 2132917605097073924705923)
        ·
          refine ⟨3199376407645610887058885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132917605097073924705923 3199376407645610887058885)
          ·
            refine ⟨599883076433552041323541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3199376407645610887058885 599883076433552041323541)
            ·
              refine ⟨28119519207822751937041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 599883076433552041323541 28119519207822751937041)
              ·
                rfl

theorem cell20_554471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_554471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554471 prefixEnd_554471 := by exact prefixLift 554471
  have htrace : WordTrace (prefixWord ++ tailWord_554471) baseStart_554471 baseEnd_554471 := by
    simpa [prefixWord, tailWord_554471, baseEnd_554471] using wordTrace_append hprefix tailTrace_554471
  have hstable : (prefixWord ++ tailWord_554471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554471).length < 2 ^ (prefixWord ++ tailWord_554471).sum := by decide
  have hdescent : baseEnd_554471 < baseStart_554471 := by decide
  rcases family_descends (prefixWord ++ tailWord_554471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554477 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 2]
def baseStart_554477 : Nat := 118140960795 + 554477 * 2 ^ 59
def prefixEnd_554477 : Nat := 4983230072969 + 3 ^ 40 * 554477 * 2
def baseEnd_554477 : Nat := 253078411433895413233345

theorem tailTrace_554477 : CollatzResearch.WordTrace tailWord_554477 prefixEnd_554477 253078411433895413233345 := by
  unfold tailWord_554477
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223437612232000977485685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13482291741488000651657123 20223437612232000977485685)
  ·
    refine ⟨1895947276146750091639283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20223437612232000977485685 1895947276146750091639283)
    ·
      refine ⟨2843920914220125137458925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895947276146750091639283 2843920914220125137458925)
      ·
        refine ⟨1066470342832546926547097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2843920914220125137458925 1066470342832546926547097)
        ·
          refine ⟨799852757124410194910323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066470342832546926547097 799852757124410194910323)
          ·
            refine ⟨1199779135686615292365485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799852757124410194910323 1199779135686615292365485)
            ·
              refine ⟨449917175882480734637057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1199779135686615292365485 449917175882480734637057)
              ·
                refine ⟨337437881911860550977793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449917175882480734637057 337437881911860550977793)
                ·
                  refine ⟨253078411433895413233345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337437881911860550977793 253078411433895413233345)
                  ·
                    rfl

theorem cell20_554477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_554477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554477 prefixEnd_554477 := by exact prefixLift 554477
  have htrace : WordTrace (prefixWord ++ tailWord_554477) baseStart_554477 baseEnd_554477 := by
    simpa [prefixWord, tailWord_554477, baseEnd_554477] using wordTrace_append hprefix tailTrace_554477
  have hstable : (prefixWord ++ tailWord_554477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554477).length < 2 ^ (prefixWord ++ tailWord_554477).sum := by decide
  have hdescent : baseEnd_554477 < baseStart_554477 := by decide
  rcases family_descends (prefixWord ++ tailWord_554477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554478 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_554478 : Nat := 118140960795 + 554478 * 2 ^ 59
def prefixEnd_554478 : Nat := 4983230072969 + 3 ^ 40 * 554478 * 2
def baseEnd_554478 : Nat := 253078867861143854200007

theorem tailTrace_554478 : CollatzResearch.WordTrace tailWord_554478 prefixEnd_554478 253078867861143854200007 := by
  unfold tailWord_554478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527934260653547268534011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13482316056818918765514725 2527934260653547268534011)
  ·
    refine ⟨3791901390980320902801017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527934260653547268534011 3791901390980320902801017)
    ·
      refine ⟨2843926043235240677100763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3791901390980320902801017 2843926043235240677100763)
      ·
        refine ⟨4265889064852861015651145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843926043235240677100763 4265889064852861015651145)
        ·
          refine ⟨3199416798639645761738359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4265889064852861015651145 3199416798639645761738359)
          ·
            refine ⟨4799125197959468642607539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199416798639645761738359 4799125197959468642607539)
            ·
              refine ⟨7198687796939202963911309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799125197959468642607539 7198687796939202963911309)
              ·
                refine ⟨2699507923852201111466741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7198687796939202963911309 2699507923852201111466741)
                ·
                  refine ⟨253078867861143854200007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699507923852201111466741 253078867861143854200007)
                  ·
                    rfl

theorem cell20_554478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_554478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_554478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_554478 prefixEnd_554478 := by exact prefixLift 554478
  have htrace : WordTrace (prefixWord ++ tailWord_554478) baseStart_554478 baseEnd_554478 := by
    simpa [prefixWord, tailWord_554478, baseEnd_554478] using wordTrace_append hprefix tailTrace_554478
  have hstable : (prefixWord ++ tailWord_554478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554478).length < 2 ^ (prefixWord ++ tailWord_554478).sum := by decide
  have hdescent : baseEnd_554478 < baseStart_554478 := by decide
  rcases family_descends (prefixWord ++ tailWord_554478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
