import V185TrunkScan22Chunk071

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_646386 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_646386 : Nat := 118140960795 + 646386 * 2 ^ 59
def prefixEnd_646386 : Nat := 4983230072969 + 3 ^ 40 * 646386 * 2
def baseEnd_646386 : Nat := 221271137558142163668221

theorem tailTrace_646386 : CollatzResearch.WordTrace tailWord_646386 prefixEnd_646386 221271137558142163668221 := by
  unfold tailWord_646386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893908559065347696249753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15717089490840927189999341 5893908559065347696249753)
  ·
    refine ⟨4420431419299010772187315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5893908559065347696249753 4420431419299010772187315)
    ·
      refine ⟨6630647128948516158280973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4420431419299010772187315 6630647128948516158280973)
      ·
        refine ⟨2486492673355693559355365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6630647128948516158280973 2486492673355693559355365)
        ·
          refine ⟨466217376254192542379131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2486492673355693559355365 466217376254192542379131)
          ·
            refine ⟨699326064381288813568697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466217376254192542379131 699326064381288813568697)
            ·
              refine ⟨524494548285966610176523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699326064381288813568697 524494548285966610176523)
              ·
                refine ⟨786741822428949915264785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524494548285966610176523 786741822428949915264785)
                ·
                  refine ⟨590056366821712436448589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 786741822428949915264785 590056366821712436448589)
                  ·
                    refine ⟨221271137558142163668221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590056366821712436448589 221271137558142163668221)
                    ·
                      rfl

theorem cell22_646386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_646386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646386 prefixEnd_646386 := by exact prefixLift 646386
  have htrace : WordTrace (prefixWord ++ tailWord_646386) baseStart_646386 baseEnd_646386 := by
    simpa [prefixWord, tailWord_646386, baseEnd_646386] using wordTrace_append hprefix tailTrace_646386
  have hstable : (prefixWord ++ tailWord_646386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646386).length < 2 ^ (prefixWord ++ tailWord_646386).sum := by decide
  have hdescent : baseEnd_646386 < baseStart_646386 := by decide
  rcases family_descends (prefixWord ++ tailWord_646386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646393 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 5]
def baseStart_646393 : Nat := 118140960795 + 646393 * 2 ^ 59
def prefixEnd_646393 : Nat := 4983230072969 + 3 ^ 40 * 646393 * 2
def baseEnd_646393 : Nat := 73757844600398826247733

theorem tailTrace_646393 : CollatzResearch.WordTrace tailWord_646393 prefixEnd_646393 73757844600398826247733 := by
  unfold tailWord_646393
  simp only [CollatzResearch.WordTrace]
  refine ⟨23575889547236030980503833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15717259698157353987002555 23575889547236030980503833)
  ·
    refine ⟨17681917160427023235377875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23575889547236030980503833 17681917160427023235377875)
    ·
      refine ⟨26522875740640534853066813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17681917160427023235377875 26522875740640534853066813)
      ·
        refine ⟨9946078402740200569900055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26522875740640534853066813 9946078402740200569900055)
        ·
          refine ⟨14919117604110300854850083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9946078402740200569900055 14919117604110300854850083)
          ·
            refine ⟨22378676406165451282275125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14919117604110300854850083 22378676406165451282275125)
            ·
              refine ⟨2098000913078011057713293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22378676406165451282275125 2098000913078011057713293)
              ·
                refine ⟨786750342404254146642485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2098000913078011057713293 786750342404254146642485)
                ·
                  refine ⟨73757844600398826247733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786750342404254146642485 73757844600398826247733)
                  ·
                    rfl

theorem cell22_646393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_646393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646393 prefixEnd_646393 := by exact prefixLift 646393
  have htrace : WordTrace (prefixWord ++ tailWord_646393) baseStart_646393 baseEnd_646393 := by
    simpa [prefixWord, tailWord_646393, baseEnd_646393] using wordTrace_append hprefix tailTrace_646393
  have hstable : (prefixWord ++ tailWord_646393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646393).length < 2 ^ (prefixWord ++ tailWord_646393).sum := by decide
  have hdescent : baseEnd_646393 < baseStart_646393 := by decide
  rcases family_descends (prefixWord ++ tailWord_646393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646431 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 1, 3]
def baseStart_646431 : Nat := 118140960795 + 646431 * 2 ^ 59
def prefixEnd_646431 : Nat := 4983230072969 + 3 ^ 40 * 646431 * 2
def baseEnd_646431 : Nat := 221286541977777046293083

theorem tailTrace_646431 : CollatzResearch.WordTrace tailWord_646431 prefixEnd_646431 221286541977777046293083 := by
  unfold tailWord_646431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23577275521098363470387147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15718183680732242313591431 23577275521098363470387147)
  ·
    refine ⟨35365913281647545205580721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23577275521098363470387147 35365913281647545205580721)
    ·
      refine ⟨26524434961235658904185541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35365913281647545205580721 26524434961235658904185541)
      ·
        refine ⟨4973331555231686044534789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26524434961235658904185541 4973331555231686044534789)
        ·
          refine ⟨932499666605941133350273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4973331555231686044534789 932499666605941133350273)
          ·
            refine ⟨699374749954455850012705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932499666605941133350273 699374749954455850012705)
            ·
              refine ⟨524531062465841887509529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699374749954455850012705 524531062465841887509529)
              ·
                refine ⟨393398296849381415632147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524531062465841887509529 393398296849381415632147)
                ·
                  refine ⟨590097445274072123448221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393398296849381415632147 590097445274072123448221)
                  ·
                    refine ⟨221286541977777046293083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590097445274072123448221 221286541977777046293083)
                    ·
                      rfl

theorem cell22_646431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_646431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646431 prefixEnd_646431 := by exact prefixLift 646431
  have htrace : WordTrace (prefixWord ++ tailWord_646431) baseStart_646431 baseEnd_646431 := by
    simpa [prefixWord, tailWord_646431, baseEnd_646431] using wordTrace_append hprefix tailTrace_646431
  have hstable : (prefixWord ++ tailWord_646431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646431).length < 2 ^ (prefixWord ++ tailWord_646431).sum := by decide
  have hdescent : baseEnd_646431 < baseStart_646431 := by decide
  rcases family_descends (prefixWord ++ tailWord_646431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646440 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_646440 : Nat := 118140960795 + 646440 * 2 ^ 59
def prefixEnd_646440 : Nat := 4983230072969 + 3 ^ 40 * 646440 * 2
def baseEnd_646440 : Nat := 221289622861704022818055

theorem tailTrace_646440 : CollatzResearch.WordTrace tailWord_646440 prefixEnd_646440 221289622861704022818055 := by
  unfold tailWord_646440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788801889032879003732387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15718402518710505338309849 11788801889032879003732387)
  ·
    refine ⟨17683202833549318505598581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11788801889032879003732387 17683202833549318505598581)
    ·
      refine ⟨1657800265645248609899867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17683202833549318505598581 1657800265645248609899867)
      ·
        refine ⟨2486700398467872914849801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657800265645248609899867 2486700398467872914849801)
        ·
          refine ⟨1865025298850904686137351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486700398467872914849801 1865025298850904686137351)
          ·
            refine ⟨2797537948276357029206027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865025298850904686137351 2797537948276357029206027)
            ·
              refine ⟨4196306922414535543809041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797537948276357029206027 4196306922414535543809041)
              ·
                refine ⟨3147230191810901657856781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196306922414535543809041 3147230191810901657856781)
                ·
                  refine ⟨1180211321929088121696293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3147230191810901657856781 1180211321929088121696293)
                  ·
                    refine ⟨221289622861704022818055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1180211321929088121696293 221289622861704022818055)
                    ·
                      rfl

theorem cell22_646440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_646440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646440 prefixEnd_646440 := by exact prefixLift 646440
  have htrace : WordTrace (prefixWord ++ tailWord_646440) baseStart_646440 baseEnd_646440 := by
    simpa [prefixWord, tailWord_646440, baseEnd_646440] using wordTrace_append hprefix tailTrace_646440
  have hstable : (prefixWord ++ tailWord_646440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646440).length < 2 ^ (prefixWord ++ tailWord_646440).sum := by decide
  have hdescent : baseEnd_646440 < baseStart_646440 := by decide
  rcases family_descends (prefixWord ++ tailWord_646440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646487 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 2, 3]
def baseStart_646487 : Nat := 118140960795 + 646487 * 2 ^ 59
def prefixEnd_646487 : Nat := 4983230072969 + 3 ^ 40 * 646487 * 2
def baseEnd_646487 : Nat := 221305711922211566892911

theorem tailTrace_646487 : CollatzResearch.WordTrace tailWord_646487 prefixEnd_646487 221305711922211566892911 := by
  unfold tailWord_646487
  simp only [CollatzResearch.WordTrace]
  refine ⟨23579318008895485034425715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15719545339263656689617143 23579318008895485034425715)
  ·
    refine ⟨35368977013343227551638573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23579318008895485034425715 35368977013343227551638573)
    ·
      refine ⟨13263366380003710331864465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35368977013343227551638573 13263366380003710331864465)
      ·
        refine ⟨9947524785002782748898349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263366380003710331864465 9947524785002782748898349)
        ·
          refine ⟨3730321794376043530836881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9947524785002782748898349 3730321794376043530836881)
          ·
            refine ⟨2797741345782032648127661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730321794376043530836881 2797741345782032648127661)
            ·
              refine ⟨1049153004668262243047873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2797741345782032648127661 1049153004668262243047873)
              ·
                refine ⟨786864753501196682285905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049153004668262243047873 786864753501196682285905)
                ·
                  refine ⟨590148565125897511714429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 786864753501196682285905 590148565125897511714429)
                  ·
                    refine ⟨221305711922211566892911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590148565125897511714429 221305711922211566892911)
                    ·
                      rfl

theorem cell22_646487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_646487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646487 prefixEnd_646487 := by exact prefixLift 646487
  have htrace : WordTrace (prefixWord ++ tailWord_646487) baseStart_646487 baseEnd_646487 := by
    simpa [prefixWord, tailWord_646487, baseEnd_646487] using wordTrace_append hprefix tailTrace_646487
  have hstable : (prefixWord ++ tailWord_646487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646487).length < 2 ^ (prefixWord ++ tailWord_646487).sum := by decide
  have hdescent : baseEnd_646487 < baseStart_646487 := by decide
  rcases family_descends (prefixWord ++ tailWord_646487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646504 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_646504 : Nat := 118140960795 + 646504 * 2 ^ 59
def prefixEnd_646504 : Nat := 4983230072969 + 3 ^ 40 * 646504 * 2
def baseEnd_646504 : Nat := 221311531369629189217859

theorem tailTrace_646504 : CollatzResearch.WordTrace tailWord_646504 prefixEnd_646504 221311531369629189217859 := by
  unfold tailWord_646504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11789969024916948468897283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15719958699889264625196377 11789969024916948468897283)
  ·
    refine ⟨17684953537375422703345925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11789969024916948468897283 17684953537375422703345925)
    ·
      refine ⟨3315928788257891756877361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17684953537375422703345925 3315928788257891756877361)
      ·
        refine ⟨2486946591193418817658021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3315928788257891756877361 2486946591193418817658021)
        ·
          refine ⟨466302485848766028310879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2486946591193418817658021 466302485848766028310879)
          ·
            refine ⟨699453728773149042466319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466302485848766028310879 699453728773149042466319)
            ·
              refine ⟨1049180593159723563699479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699453728773149042466319 1049180593159723563699479)
              ·
                refine ⟨1573770889739585345549219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049180593159723563699479 1573770889739585345549219)
                ·
                  refine ⟨2360656334609378018323829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573770889739585345549219 2360656334609378018323829)
                  ·
                    refine ⟨221311531369629189217859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2360656334609378018323829 221311531369629189217859)
                    ·
                      rfl

theorem cell22_646504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_646504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646504 prefixEnd_646504 := by exact prefixLift 646504
  have htrace : WordTrace (prefixWord ++ tailWord_646504) baseStart_646504 baseEnd_646504 := by
    simpa [prefixWord, tailWord_646504, baseEnd_646504] using wordTrace_append hprefix tailTrace_646504
  have hstable : (prefixWord ++ tailWord_646504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646504).length < 2 ^ (prefixWord ++ tailWord_646504).sum := by decide
  have hdescent : baseEnd_646504 < baseStart_646504 := by decide
  rcases family_descends (prefixWord ++ tailWord_646504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646513 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_646513 : Nat := 118140960795 + 646513 * 2 ^ 59
def prefixEnd_646513 : Nat := 4983230072969 + 3 ^ 40 * 646513 * 2
def baseEnd_646513 : Nat := 221314612253556165742831

theorem tailTrace_646513 : CollatzResearch.WordTrace tailWord_646513 prefixEnd_646513 221314612253556165742831 := by
  unfold tailWord_646513
  simp only [CollatzResearch.WordTrace]
  refine ⟨23580266306801291474872193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15720177537867527649914795 23580266306801291474872193)
  ·
    refine ⟨17685199730100968606154145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23580266306801291474872193 17685199730100968606154145)
    ·
      refine ⟨13263899797575726454615609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17685199730100968606154145 13263899797575726454615609)
      ·
        refine ⟨9947924848181794840961707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263899797575726454615609 9947924848181794840961707)
        ·
          refine ⟨14921887272272692261442561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947924848181794840961707 14921887272272692261442561)
          ·
            refine ⟨11191415454204519196081921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14921887272272692261442561 11191415454204519196081921)
            ·
              refine ⟨8393561590653389397061441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11191415454204519196081921 8393561590653389397061441)
              ·
                refine ⟨6295171192990042047796081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393561590653389397061441 6295171192990042047796081)
                ·
                  refine ⟨4721378394742531535847061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295171192990042047796081 4721378394742531535847061)
                  ·
                    refine ⟨221314612253556165742831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4721378394742531535847061 221314612253556165742831)
                    ·
                      rfl

theorem cell22_646513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_646513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646513 prefixEnd_646513 := by exact prefixLift 646513
  have htrace : WordTrace (prefixWord ++ tailWord_646513) baseStart_646513 baseEnd_646513 := by
    simpa [prefixWord, tailWord_646513, baseEnd_646513] using wordTrace_append hprefix tailTrace_646513
  have hstable : (prefixWord ++ tailWord_646513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646513).length < 2 ^ (prefixWord ++ tailWord_646513).sum := by decide
  have hdescent : baseEnd_646513 < baseStart_646513 := by decide
  rcases family_descends (prefixWord ++ tailWord_646513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646562 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_646562 : Nat := 118140960795 + 646562 * 2 ^ 59
def prefixEnd_646562 : Nat := 4983230072969 + 3 ^ 40 * 646562 * 2
def baseEnd_646562 : Nat := 73777128651645457089227

theorem tailTrace_646562 : CollatzResearch.WordTrace tailWord_646562 prefixEnd_646562 73777128651645457089227 := by
  unfold tailWord_646562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895513370905943210851485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15721368989082515228937293 5895513370905943210851485)
  ·
    refine ⟨2210817514089728704069307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5895513370905943210851485 2210817514089728704069307)
    ·
      refine ⟨3316226271134593056103961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210817514089728704069307 3316226271134593056103961)
      ·
        refine ⟨2487169703350944792077971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316226271134593056103961 2487169703350944792077971)
        ·
          refine ⟨3730754555026417188116957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487169703350944792077971 3730754555026417188116957)
          ·
            refine ⟨1399032958134906445543859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3730754555026417188116957 1399032958134906445543859)
            ·
              refine ⟨2098549437202359668315789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399032958134906445543859 2098549437202359668315789)
              ·
                refine ⟨786956038950884875618421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2098549437202359668315789 786956038950884875618421)
                ·
                  refine ⟨73777128651645457089227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786956038950884875618421 73777128651645457089227)
                  ·
                    rfl

theorem cell22_646562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_646562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646562 prefixEnd_646562 := by exact prefixLift 646562
  have htrace : WordTrace (prefixWord ++ tailWord_646562) baseStart_646562 baseEnd_646562 := by
    simpa [prefixWord, tailWord_646562, baseEnd_646562] using wordTrace_append hprefix tailTrace_646562
  have hstable : (prefixWord ++ tailWord_646562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646562).length < 2 ^ (prefixWord ++ tailWord_646562).sum := by decide
  have hdescent : baseEnd_646562 < baseStart_646562 := by decide
  rcases family_descends (prefixWord ++ tailWord_646562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646757 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_646757 : Nat := 118140960795 + 646757 * 2 ^ 59
def prefixEnd_646757 : Nat := 4983230072969 + 3 ^ 40 * 646757 * 2
def baseEnd_646757 : Nat := 221398138440020862642083

theorem tailTrace_646757 : CollatzResearch.WordTrace tailWord_646757 prefixEnd_646757 221398138440020862642083 := by
  unfold tailWord_646757
  simp only [CollatzResearch.WordTrace]
  refine ⟨23589165717917321146754525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15726110478611547431169683 23589165717917321146754525)
  ·
    refine ⟨8845937144218995430032947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23589165717917321146754525 8845937144218995430032947)
    ·
      refine ⟨13268905716328493145049421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8845937144218995430032947 13268905716328493145049421)
      ·
        refine ⟨4975839643623184929393533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13268905716328493145049421 4975839643623184929393533)
        ·
          refine ⟨1865939866358694348522575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4975839643623184929393533 1865939866358694348522575)
          ·
            refine ⟨2798909799538041522783863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865939866358694348522575 2798909799538041522783863)
            ·
              refine ⟨4198364699307062284175795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798909799538041522783863 4198364699307062284175795)
              ·
                refine ⟨6297547048960593426263693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198364699307062284175795 6297547048960593426263693)
                ·
                  refine ⟨2361580143360222534848885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6297547048960593426263693 2361580143360222534848885)
                  ·
                    refine ⟨221398138440020862642083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2361580143360222534848885 221398138440020862642083)
                    ·
                      rfl

theorem cell22_646757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_646757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646757 prefixEnd_646757 := by exact prefixLift 646757
  have htrace : WordTrace (prefixWord ++ tailWord_646757) baseStart_646757 baseEnd_646757 := by
    simpa [prefixWord, tailWord_646757, baseEnd_646757] using wordTrace_append hprefix tailTrace_646757
  have hstable : (prefixWord ++ tailWord_646757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646757).length < 2 ^ (prefixWord ++ tailWord_646757).sum := by decide
  have hdescent : baseEnd_646757 < baseStart_646757 := by decide
  rcases family_descends (prefixWord ++ tailWord_646757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646847 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_646847 : Nat := 118140960795 + 646847 * 2 ^ 59
def prefixEnd_646847 : Nat := 4983230072969 + 3 ^ 40 * 646847 * 2
def baseEnd_646847 : Nat := 221428947279290627891807

theorem tailTrace_646847 : CollatzResearch.WordTrace tailWord_646847 prefixEnd_646847 221428947279290627891807 := by
  unfold tailWord_646847
  simp only [CollatzResearch.WordTrace]
  refine ⟨23592448287591266517530795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15728298858394177678353863 23592448287591266517530795)
  ·
    refine ⟨35388672431386899776296193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23592448287591266517530795 35388672431386899776296193)
    ·
      refine ⟨26541504323540174832222145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35388672431386899776296193 26541504323540174832222145)
      ·
        refine ⟨19906128242655131124166609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26541504323540174832222145 19906128242655131124166609)
        ·
          refine ⟨14929596181991348343124957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19906128242655131124166609 14929596181991348343124957)
          ·
            refine ⟨5598598568246755628671859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14929596181991348343124957 5598598568246755628671859)
            ·
              refine ⟨8397897852370133443007789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598598568246755628671859 8397897852370133443007789)
              ·
                refine ⟨3149211694638800041127921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8397897852370133443007789 3149211694638800041127921)
                ·
                  refine ⟨2361908770979100030845941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149211694638800041127921 2361908770979100030845941)
                  ·
                    refine ⟨221428947279290627891807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2361908770979100030845941 221428947279290627891807)
                    ·
                      rfl

theorem cell22_646847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_646847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646847 prefixEnd_646847 := by exact prefixLift 646847
  have htrace : WordTrace (prefixWord ++ tailWord_646847) baseStart_646847 baseEnd_646847 := by
    simpa [prefixWord, tailWord_646847, baseEnd_646847] using wordTrace_append hprefix tailTrace_646847
  have hstable : (prefixWord ++ tailWord_646847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646847).length < 2 ^ (prefixWord ++ tailWord_646847).sum := by decide
  have hdescent : baseEnd_646847 < baseStart_646847 := by decide
  rcases family_descends (prefixWord ++ tailWord_646847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646879 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 1, 4]
def baseStart_646879 : Nat := 118140960795 + 646879 * 2 ^ 59
def prefixEnd_646879 : Nat := 4983230072969 + 3 ^ 40 * 646879 * 2
def baseEnd_646879 : Nat := 221439901533253211091709

theorem tailTrace_646879 : CollatzResearch.WordTrace tailWord_646879 prefixEnd_646879 221439901533253211091709 := by
  unfold tailWord_646879
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593615423475335982695691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729076948983557321797127 23593615423475335982695691)
  ·
    refine ⟨35390423135213003974043537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23593615423475335982695691 35390423135213003974043537)
    ·
      refine ⟨26542817351409752980532653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35390423135213003974043537 26542817351409752980532653)
      ·
        refine ⟨9953556506778657367699745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26542817351409752980532653 9953556506778657367699745)
        ·
          refine ⟨7465167380083993025774809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9953556506778657367699745 7465167380083993025774809)
          ·
            refine ⟨5598875535062994769331107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7465167380083993025774809 5598875535062994769331107)
            ·
              refine ⟨8398313302594492153996661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598875535062994769331107 8398313302594492153996661)
              ·
                refine ⟨787341872118233639437187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8398313302594492153996661 787341872118233639437187)
                ·
                  refine ⟨1181012808177350459155781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787341872118233639437187 1181012808177350459155781)
                  ·
                    refine ⟨221439901533253211091709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181012808177350459155781 221439901533253211091709)
                    ·
                      rfl

theorem cell22_646879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_646879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646879 prefixEnd_646879 := by exact prefixLift 646879
  have htrace : WordTrace (prefixWord ++ tailWord_646879) baseStart_646879 baseEnd_646879 := by
    simpa [prefixWord, tailWord_646879, baseEnd_646879] using wordTrace_append hprefix tailTrace_646879
  have hstable : (prefixWord ++ tailWord_646879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646879).length < 2 ^ (prefixWord ++ tailWord_646879).sum := by decide
  have hdescent : baseEnd_646879 < baseStart_646879 := by decide
  rcases family_descends (prefixWord ++ tailWord_646879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646887 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 1, 3]
def baseStart_646887 : Nat := 118140960795 + 646887 * 2 ^ 59
def prefixEnd_646887 : Nat := 4983230072969 + 3 ^ 40 * 646887 * 2
def baseEnd_646887 : Nat := 221442640096743856891685

theorem tailTrace_646887 : CollatzResearch.WordTrace tailWord_646887 prefixEnd_646887 221442640096743856891685 := by
  unfold tailWord_646887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593907207446353348986915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729271471630902232657943 23593907207446353348986915)
  ·
    refine ⟨35390860811169530023480373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23593907207446353348986915 35390860811169530023480373)
    ·
      refine ⟨3317893201047143439701285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35390860811169530023480373 3317893201047143439701285)
      ·
        refine ⟨622104975196339394943991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3317893201047143439701285 622104975196339394943991)
        ·
          refine ⟨933157462794509092415987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622104975196339394943991 933157462794509092415987)
          ·
            refine ⟨1399736194191763638623981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933157462794509092415987 1399736194191763638623981)
            ·
              refine ⟨524901072821911364483993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399736194191763638623981 524901072821911364483993)
              ·
                refine ⟨393675804616433523362995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524901072821911364483993 393675804616433523362995)
                ·
                  refine ⟨590513706924650285044493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393675804616433523362995 590513706924650285044493)
                  ·
                    refine ⟨221442640096743856891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590513706924650285044493 221442640096743856891685)
                    ·
                      rfl

theorem cell22_646887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_646887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646887 prefixEnd_646887 := by exact prefixLift 646887
  have htrace : WordTrace (prefixWord ++ tailWord_646887) baseStart_646887 baseEnd_646887 := by
    simpa [prefixWord, tailWord_646887, baseEnd_646887] using wordTrace_append hprefix tailTrace_646887
  have hstable : (prefixWord ++ tailWord_646887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646887).length < 2 ^ (prefixWord ++ tailWord_646887).sum := by decide
  have hdescent : baseEnd_646887 < baseStart_646887 := by decide
  rcases family_descends (prefixWord ++ tailWord_646887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646900 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_646900 : Nat := 118140960795 + 646900 * 2 ^ 59
def prefixEnd_646900 : Nat := 4983230072969 + 3 ^ 40 * 646900 * 2
def baseEnd_646900 : Nat := 73815696754138718772215

theorem tailTrace_646900 : CollatzResearch.WordTrace tailWord_646900 prefixEnd_646900 73815696754138718772215 := by
  unfold tailWord_646900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797190678199628284605077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15729587570932837712806769 11797190678199628284605077)
  ·
    refine ⟨552993313040607575840863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11797190678199628284605077 552993313040607575840863)
    ·
      refine ⟨829489969560911363761295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552993313040607575840863 829489969560911363761295)
      ·
        refine ⟨1244234954341367045641943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829489969560911363761295 1244234954341367045641943)
        ·
          refine ⟨1866352431512050568462915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244234954341367045641943 1866352431512050568462915)
          ·
            refine ⟨2799528647268075852694373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866352431512050568462915 2799528647268075852694373)
            ·
              refine ⟨524911621362764222380195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2799528647268075852694373 524911621362764222380195)
              ·
                refine ⟨787367432044146333570293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524911621362764222380195 787367432044146333570293)
                ·
                  refine ⟨73815696754138718772215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 787367432044146333570293 73815696754138718772215)
                  ·
                    rfl

theorem cell22_646900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_646900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646900 prefixEnd_646900 := by exact prefixLift 646900
  have htrace : WordTrace (prefixWord ++ tailWord_646900) baseStart_646900 baseEnd_646900 := by
    simpa [prefixWord, tailWord_646900, baseEnd_646900] using wordTrace_append hprefix tailTrace_646900
  have hstable : (prefixWord ++ tailWord_646900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646900).length < 2 ^ (prefixWord ++ tailWord_646900).sum := by decide
  have hdescent : baseEnd_646900 < baseStart_646900 := by decide
  rcases family_descends (prefixWord ++ tailWord_646900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646907 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_646907 : Nat := 118140960795 + 646907 * 2 ^ 59
def prefixEnd_646907 : Nat := 4983230072969 + 3 ^ 40 * 646907 * 2
def baseEnd_646907 : Nat := 221449486505470471391623

theorem tailTrace_646907 : CollatzResearch.WordTrace tailWord_646907 prefixEnd_646907 221449486505470471391623 := by
  unfold tailWord_646907
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594636667373896764714975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729757778249264509809983 23594636667373896764714975)
  ·
    refine ⟨35391955001060845147072463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23594636667373896764714975 35391955001060845147072463)
    ·
      refine ⟨53087932501591267720608695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35391955001060845147072463 53087932501591267720608695)
      ·
        refine ⟨79631898752386901580913043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53087932501591267720608695 79631898752386901580913043)
        ·
          refine ⟨119447848128580352371369565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79631898752386901580913043 119447848128580352371369565)
          ·
            refine ⟨44792943048217632139263587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119447848128580352371369565 44792943048217632139263587)
            ·
              refine ⟨67189414572326448208895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44792943048217632139263587 67189414572326448208895381)
              ·
                refine ⟨3149503808077802259791971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67189414572326448208895381 3149503808077802259791971)
                ·
                  refine ⟨4724255712116703389687957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149503808077802259791971 4724255712116703389687957)
                  ·
                    refine ⟨221449486505470471391623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4724255712116703389687957 221449486505470471391623)
                    ·
                      rfl

theorem cell22_646907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_646907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646907 prefixEnd_646907 := by exact prefixLift 646907
  have htrace : WordTrace (prefixWord ++ tailWord_646907) baseStart_646907 baseEnd_646907 := by
    simpa [prefixWord, tailWord_646907, baseEnd_646907] using wordTrace_append hprefix tailTrace_646907
  have hstable : (prefixWord ++ tailWord_646907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646907).length < 2 ^ (prefixWord ++ tailWord_646907).sum := by decide
  have hdescent : baseEnd_646907 < baseStart_646907 := by decide
  rcases family_descends (prefixWord ++ tailWord_646907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646909 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_646909 : Nat := 118140960795 + 646909 * 2 ^ 59
def prefixEnd_646909 : Nat := 4983230072969 + 3 ^ 40 * 646909 * 2
def baseEnd_646909 : Nat := 221450171146343132841617

theorem tailTrace_646909 : CollatzResearch.WordTrace tailWord_646909 prefixEnd_646909 221450171146343132841617 := by
  unfold tailWord_646909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594709613366651106287781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729806408911100737525187 23594709613366651106287781)
  ·
    refine ⟨4424008052506247082428959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23594709613366651106287781 4424008052506247082428959)
    ·
      refine ⟨6636012078759370623643439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424008052506247082428959 6636012078759370623643439)
      ·
        refine ⟨9954018118139055935465159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636012078759370623643439 9954018118139055935465159)
        ·
          refine ⟨14931027177208583903197739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954018118139055935465159 14931027177208583903197739)
          ·
            refine ⟨22396540765812875854796609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931027177208583903197739 22396540765812875854796609)
            ·
              refine ⟨16797405574359656891097457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22396540765812875854796609 16797405574359656891097457)
              ·
                refine ⟨12598054180769742668323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16797405574359656891097457 12598054180769742668323093)
                ·
                  refine ⟨590533789723581687577645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12598054180769742668323093 590533789723581687577645)
                  ·
                    refine ⟨221450171146343132841617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590533789723581687577645 221450171146343132841617)
                    ·
                      rfl

theorem cell22_646909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_646909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646909 prefixEnd_646909 := by exact prefixLift 646909
  have htrace : WordTrace (prefixWord ++ tailWord_646909) baseStart_646909 baseEnd_646909 := by
    simpa [prefixWord, tailWord_646909, baseEnd_646909] using wordTrace_append hprefix tailTrace_646909
  have hstable : (prefixWord ++ tailWord_646909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646909).length < 2 ^ (prefixWord ++ tailWord_646909).sum := by decide
  have hdescent : baseEnd_646909 < baseStart_646909 := by decide
  rcases family_descends (prefixWord ++ tailWord_646909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646924 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_646924 : Nat := 118140960795 + 646924 * 2 ^ 59
def prefixEnd_646924 : Nat := 4983230072969 + 3 ^ 40 * 646924 * 2
def baseEnd_646924 : Nat := 221455305952888093716571

theorem tailTrace_646924 : CollatzResearch.WordTrace tailWord_646924 prefixEnd_646924 221455305952888093716571 := by
  unfold tailWord_646924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797628354156154334041913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15730171138874872445389217 11797628354156154334041913)
  ·
    refine ⟨8848221265617115750531435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11797628354156154334041913 8848221265617115750531435)
    ·
      refine ⟨13272331898425673625797153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848221265617115750531435 13272331898425673625797153)
      ·
        refine ⟨9954248923819255219347865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13272331898425673625797153 9954248923819255219347865)
        ·
          refine ⟨7465686692864441414510899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954248923819255219347865 7465686692864441414510899)
          ·
            refine ⟨11198530039296662121766349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465686692864441414510899 11198530039296662121766349)
            ·
              refine ⟨4199448764736248295662381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11198530039296662121766349 4199448764736248295662381)
              ·
                refine ⟨1574793286776093110873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199448764736248295662381 1574793286776093110873393)
                ·
                  refine ⟨1181094965082069833155045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574793286776093110873393 1181094965082069833155045)
                  ·
                    refine ⟨221455305952888093716571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181094965082069833155045 221455305952888093716571)
                    ·
                      rfl

theorem cell22_646924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_646924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646924 prefixEnd_646924 := by exact prefixLift 646924
  have htrace : WordTrace (prefixWord ++ tailWord_646924) baseStart_646924 baseEnd_646924 := by
    simpa [prefixWord, tailWord_646924, baseEnd_646924] using wordTrace_append hprefix tailTrace_646924
  have hstable : (prefixWord ++ tailWord_646924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646924).length < 2 ^ (prefixWord ++ tailWord_646924).sum := by decide
  have hdescent : baseEnd_646924 < baseStart_646924 := by decide
  rcases family_descends (prefixWord ++ tailWord_646924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646930 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_646930 : Nat := 118140960795 + 646930 * 2 ^ 59
def prefixEnd_646930 : Nat := 4983230072969 + 3 ^ 40 * 646930 * 2
def baseEnd_646930 : Nat := 221457359875506078066553

theorem tailTrace_646930 : CollatzResearch.WordTrace tailWord_646930 prefixEnd_646930 221457359875506078066553 := by
  unfold tailWord_646930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898868886572642923200561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15730317030860381128534829 5898868886572642923200561)
  ·
    refine ⟨4424151664929482192400421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5898868886572642923200561 4424151664929482192400421)
    ·
      refine ⟨829528437174277911075079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4424151664929482192400421 829528437174277911075079)
      ·
        refine ⟨1244292655761416866612619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829528437174277911075079 1244292655761416866612619)
        ·
          refine ⟨1866438983642125299918929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244292655761416866612619 1866438983642125299918929)
          ·
            refine ⟨1399829237731593974939197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866438983642125299918929 1399829237731593974939197)
            ·
              refine ⟨524935964149347740602199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1399829237731593974939197 524935964149347740602199)
              ·
                refine ⟨787403946224021610903299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524935964149347740602199 787403946224021610903299)
                ·
                  refine ⟨1181105919336032416354949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787403946224021610903299 1181105919336032416354949)
                  ·
                    refine ⟨221457359875506078066553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181105919336032416354949 221457359875506078066553)
                    ·
                      rfl

theorem cell22_646930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_646930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646930 prefixEnd_646930 := by exact prefixLift 646930
  have htrace : WordTrace (prefixWord ++ tailWord_646930) baseStart_646930 baseEnd_646930 := by
    simpa [prefixWord, tailWord_646930, baseEnd_646930] using wordTrace_append hprefix tailTrace_646930
  have hstable : (prefixWord ++ tailWord_646930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646930).length < 2 ^ (prefixWord ++ tailWord_646930).sum := by decide
  have hdescent : baseEnd_646930 < baseStart_646930 := by decide
  rcases family_descends (prefixWord ++ tailWord_646930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_646937 : Nat := 118140960795 + 646937 * 2 ^ 59
def prefixEnd_646937 : Nat := 4983230072969 + 3 ^ 40 * 646937 * 2
def baseEnd_646937 : Nat := 221459756118560393141531

theorem tailTrace_646937 : CollatzResearch.WordTrace tailWord_646937 prefixEnd_646937 221459756118560393141531 := by
  unfold tailWord_646937
  simp only [CollatzResearch.WordTrace]
  refine ⟨23595730857265211888307065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15730487238176807925538043 23595730857265211888307065)
  ·
    refine ⟨17696798142948908916230299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23595730857265211888307065 17696798142948908916230299)
    ·
      refine ⟨26545197214423363374345449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696798142948908916230299 26545197214423363374345449)
      ·
        refine ⟨19908897910817522530759087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26545197214423363374345449 19908897910817522530759087)
        ·
          refine ⟨29863346866226283796138631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19908897910817522530759087 29863346866226283796138631)
          ·
            refine ⟨44795020299339425694207947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29863346866226283796138631 44795020299339425694207947)
            ·
              refine ⟨67192530449009138541311921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44795020299339425694207947 67192530449009138541311921)
              ·
                refine ⟨50394397836756853905983941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67192530449009138541311921 50394397836756853905983941)
                ·
                  refine ⟨9448949594391910107371989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50394397836756853905983941 9448949594391910107371989)
                  ·
                    refine ⟨221459756118560393141531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9448949594391910107371989 221459756118560393141531)
                    ·
                      rfl

theorem cell22_646937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_646937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_646937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_646937 prefixEnd_646937 := by exact prefixLift 646937
  have htrace : WordTrace (prefixWord ++ tailWord_646937) baseStart_646937 baseEnd_646937 := by
    simpa [prefixWord, tailWord_646937, baseEnd_646937] using wordTrace_append hprefix tailTrace_646937
  have hstable : (prefixWord ++ tailWord_646937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646937).length < 2 ^ (prefixWord ++ tailWord_646937).sum := by decide
  have hdescent : baseEnd_646937 < baseStart_646937 := by decide
  rcases family_descends (prefixWord ++ tailWord_646937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647061 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_647061 : Nat := 118140960795 + 647061 * 2 ^ 59
def prefixEnd_647061 : Nat := 4983230072969 + 3 ^ 40 * 647061 * 2
def baseEnd_647061 : Nat := 221502203852665403041151

theorem tailTrace_647061 : CollatzResearch.WordTrace tailWord_647061 prefixEnd_647061 221502203852665403041151 := by
  unfold tailWord_647061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600253508815981065821037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15733502339210654043880691 23600253508815981065821037)
  ·
    refine ⟨8850095065805992899682889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23600253508815981065821037 8850095065805992899682889)
    ·
      refine ⟨6637571299354494674762167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8850095065805992899682889 6637571299354494674762167)
      ·
        refine ⟨9956356949031742012143251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6637571299354494674762167 9956356949031742012143251)
        ·
          refine ⟨14934535423547613018214877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9956356949031742012143251 14934535423547613018214877)
          ·
            refine ⟨5600450783830354881830579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14934535423547613018214877 5600450783830354881830579)
            ·
              refine ⟨8400676175745532322745869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600450783830354881830579 8400676175745532322745869)
              ·
                refine ⟨3150253565904574621029701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400676175745532322745869 3150253565904574621029701)
                ·
                  refine ⟨590672543607107741443069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3150253565904574621029701 590672543607107741443069)
                  ·
                    refine ⟨221502203852665403041151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590672543607107741443069 221502203852665403041151)
                    ·
                      rfl

theorem cell22_647061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_647061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647061 prefixEnd_647061 := by exact prefixLift 647061
  have htrace : WordTrace (prefixWord ++ tailWord_647061) baseStart_647061 baseEnd_647061 := by
    simpa [prefixWord, tailWord_647061, baseEnd_647061] using wordTrace_append hprefix tailTrace_647061
  have hstable : (prefixWord ++ tailWord_647061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647061).length < 2 ^ (prefixWord ++ tailWord_647061).sum := by decide
  have hdescent : baseEnd_647061 < baseStart_647061 := by decide
  rcases family_descends (prefixWord ++ tailWord_647061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647093 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_647093 : Nat := 118140960795 + 647093 * 2 ^ 59
def prefixEnd_647093 : Nat := 4983230072969 + 3 ^ 40 * 647093 * 2
def baseEnd_647093 : Nat := 221513158106627986241053

theorem tailTrace_647093 : CollatzResearch.WordTrace tailWord_647093 prefixEnd_647093 221513158106627986241053 := by
  unfold tailWord_647093
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601420644700050530985933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15734280429800033687323955 23601420644700050530985933)
  ·
    refine ⟨8850532741762518949119725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23601420644700050530985933 8850532741762518949119725)
    ·
      refine ⟨3318949778160944605919897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8850532741762518949119725 3318949778160944605919897)
      ·
        refine ⟨2489212333620708454439923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3318949778160944605919897 2489212333620708454439923)
        ·
          refine ⟨3733818500431062681659885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489212333620708454439923 3733818500431062681659885)
          ·
            refine ⟨1400181937661648505622457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3733818500431062681659885 1400181937661648505622457)
            ·
              refine ⟨1050136453246236379216843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400181937661648505622457 1050136453246236379216843)
              ·
                refine ⟨1575204679869354568825265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050136453246236379216843 1575204679869354568825265)
                ·
                  refine ⟨1181403509902015926618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575204679869354568825265 1181403509902015926618949)
                  ·
                    refine ⟨221513158106627986241053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181403509902015926618949 221513158106627986241053)
                    ·
                      rfl

theorem cell22_647093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_647093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647093 prefixEnd_647093 := by exact prefixLift 647093
  have htrace : WordTrace (prefixWord ++ tailWord_647093) baseStart_647093 baseEnd_647093 := by
    simpa [prefixWord, tailWord_647093, baseEnd_647093] using wordTrace_append hprefix tailTrace_647093
  have hstable : (prefixWord ++ tailWord_647093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647093).length < 2 ^ (prefixWord ++ tailWord_647093).sum := by decide
  have hdescent : baseEnd_647093 < baseStart_647093 := by decide
  rcases family_descends (prefixWord ++ tailWord_647093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647228 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_647228 : Nat := 118140960795 + 647228 * 2 ^ 59
def prefixEnd_647228 : Nat := 4983230072969 + 3 ^ 40 * 647228 * 2
def baseEnd_647228 : Nat := 221559371365532634115639

theorem tailTrace_647228 : CollatzResearch.WordTrace tailWord_647228 prefixEnd_647228 221559371365532634115639 := by
  unfold tailWord_647228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803172249605484293575169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15737562999473979058100225 11803172249605484293575169)
  ·
    refine ⟨8852379187204113220181377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11803172249605484293575169 8852379187204113220181377)
    ·
      refine ⟨6639284390403084915136033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8852379187204113220181377 6639284390403084915136033)
      ·
        refine ⟨4979463292802313686352025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6639284390403084915136033 4979463292802313686352025)
        ·
          refine ⟨3734597469601735264764019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4979463292802313686352025 3734597469601735264764019)
          ·
            refine ⟨5601896204402602897146029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734597469601735264764019 5601896204402602897146029)
            ·
              refine ⟨2100711076650976086429761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5601896204402602897146029 2100711076650976086429761)
              ·
                refine ⟨1575533307488232064822321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100711076650976086429761 1575533307488232064822321)
                ·
                  refine ⟨1181649980616174048616741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575533307488232064822321 1181649980616174048616741)
                  ·
                    refine ⟨221559371365532634115639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181649980616174048616741 221559371365532634115639)
                    ·
                      rfl

theorem cell22_647228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_647228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647228 prefixEnd_647228 := by exact prefixLift 647228
  have htrace : WordTrace (prefixWord ++ tailWord_647228) baseStart_647228 baseEnd_647228 := by
    simpa [prefixWord, tailWord_647228, baseEnd_647228] using wordTrace_append hprefix tailTrace_647228
  have hstable : (prefixWord ++ tailWord_647228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647228).length < 2 ^ (prefixWord ++ tailWord_647228).sum := by decide
  have hdescent : baseEnd_647228 < baseStart_647228 := by decide
  rcases family_descends (prefixWord ++ tailWord_647228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647258 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_647258 : Nat := 118140960795 + 647258 * 2 ^ 59
def prefixEnd_647258 : Nat := 4983230072969 + 3 ^ 40 * 647258 * 2
def baseEnd_647258 : Nat := 221569640978622555865547

theorem tailTrace_647258 : CollatzResearch.WordTrace tailWord_647258 prefixEnd_647258 221569640978622555865547 := by
  unfold tailWord_647258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901859672275570927685607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15738292459401522473828285 5901859672275570927685607)
  ·
    refine ⟨8852789508413356391528411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901859672275570927685607 8852789508413356391528411)
    ·
      refine ⟨13279184262620034587292617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852789508413356391528411 13279184262620034587292617)
      ·
        refine ⟨9959388196965025940469463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13279184262620034587292617 9959388196965025940469463)
        ·
          refine ⟨14939082295447538910704195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9959388196965025940469463 14939082295447538910704195)
          ·
            refine ⟨22408623443171308366056293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14939082295447538910704195 22408623443171308366056293)
            ·
              refine ⟨4201616895594620318635555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22408623443171308366056293 4201616895594620318635555)
              ·
                refine ⟨6302425343391930477953333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201616895594620318635555 6302425343391930477953333)
                ·
                  refine ⟨590852375942993482308125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6302425343391930477953333 590852375942993482308125)
                  ·
                    refine ⟨221569640978622555865547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590852375942993482308125 221569640978622555865547)
                    ·
                      rfl

theorem cell22_647258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_647258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647258 prefixEnd_647258 := by exact prefixLift 647258
  have htrace : WordTrace (prefixWord ++ tailWord_647258) baseStart_647258 baseEnd_647258 := by
    simpa [prefixWord, tailWord_647258, baseEnd_647258] using wordTrace_append hprefix tailTrace_647258
  have hstable : (prefixWord ++ tailWord_647258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647258).length < 2 ^ (prefixWord ++ tailWord_647258).sum := by decide
  have hdescent : baseEnd_647258 < baseStart_647258 := by decide
  rcases family_descends (prefixWord ++ tailWord_647258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647292 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_647292 : Nat := 118140960795 + 647292 * 2 ^ 59
def prefixEnd_647292 : Nat := 4983230072969 + 3 ^ 40 * 647292 * 2
def baseEnd_647292 : Nat := 221581279873457800515443

theorem tailTrace_647292 : CollatzResearch.WordTrace tailWord_647292 prefixEnd_647292 221581279873457800515443 := by
  unfold tailWord_647292
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804339385489553758740065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15739119180652738344986753 11804339385489553758740065)
  ·
    refine ⟨8853254539117165319055049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11804339385489553758740065 8853254539117165319055049)
    ·
      refine ⟨6639940904337873989291287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8853254539117165319055049 6639940904337873989291287)
      ·
        refine ⟨9959911356506810983936931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639940904337873989291287 9959911356506810983936931)
        ·
          refine ⟨14939867034760216475905397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9959911356506810983936931 14939867034760216475905397)
          ·
            refine ⟨1400612534508770294616131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14939867034760216475905397 1400612534508770294616131)
            ·
              refine ⟨2100918801763155441924197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400612534508770294616131 2100918801763155441924197)
              ·
                refine ⟨393922275330591645360787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2100918801763155441924197 393922275330591645360787)
                ·
                  refine ⟨590883412995887468041181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393922275330591645360787 590883412995887468041181)
                  ·
                    refine ⟨221581279873457800515443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590883412995887468041181 221581279873457800515443)
                    ·
                      rfl

theorem cell22_647292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_647292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647292 prefixEnd_647292 := by exact prefixLift 647292
  have htrace : WordTrace (prefixWord ++ tailWord_647292) baseStart_647292 baseEnd_647292 := by
    simpa [prefixWord, tailWord_647292, baseEnd_647292] using wordTrace_append hprefix tailTrace_647292
  have hstable : (prefixWord ++ tailWord_647292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647292).length < 2 ^ (prefixWord ++ tailWord_647292).sum := by decide
  have hdescent : baseEnd_647292 < baseStart_647292 := by decide
  rcases family_descends (prefixWord ++ tailWord_647292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647326 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_647326 : Nat := 118140960795 + 647326 * 2 ^ 59
def prefixEnd_647326 : Nat := 4983230072969 + 3 ^ 40 * 647326 * 2
def baseEnd_647326 : Nat := 221592918768293045165339

theorem tailTrace_647326 : CollatzResearch.WordTrace tailWord_647326 prefixEnd_647326 221592918768293045165339 := by
  unfold tailWord_647326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951239856606991415527229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15739945901903954216145221 2951239856606991415527229)
  ·
    refine ⟨1106714946227621780822711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2951239856606991415527229 1106714946227621780822711)
    ·
      refine ⟨1660072419341432671234067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106714946227621780822711 1660072419341432671234067)
      ·
        refine ⟨2490108629012149006851101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660072419341432671234067 2490108629012149006851101)
        ·
          refine ⟨933790735879555877569163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2490108629012149006851101 933790735879555877569163)
          ·
            refine ⟨1400686103819333816353745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933790735879555877569163 1400686103819333816353745)
            ·
              refine ⟨1050514577864500362265309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400686103819333816353745 1050514577864500362265309)
              ·
                refine ⟨393942966699187635849491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050514577864500362265309 393942966699187635849491)
                ·
                  refine ⟨590914450048781453774237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393942966699187635849491 590914450048781453774237)
                  ·
                    refine ⟨221592918768293045165339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590914450048781453774237 221592918768293045165339)
                    ·
                      rfl

theorem cell22_647326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_647326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647326 prefixEnd_647326 := by exact prefixLift 647326
  have htrace : WordTrace (prefixWord ++ tailWord_647326) baseStart_647326 baseEnd_647326 := by
    simpa [prefixWord, tailWord_647326, baseEnd_647326] using wordTrace_append hprefix tailTrace_647326
  have hstable : (prefixWord ++ tailWord_647326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647326).length < 2 ^ (prefixWord ++ tailWord_647326).sum := by decide
  have hdescent : baseEnd_647326 < baseStart_647326 := by decide
  rcases family_descends (prefixWord ++ tailWord_647326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647365 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_647365 : Nat := 118140960795 + 647365 * 2 ^ 59
def prefixEnd_647365 : Nat := 4983230072969 + 3 ^ 40 * 647365 * 2
def baseEnd_647365 : Nat := 221606269265309943440219

theorem tailTrace_647365 : CollatzResearch.WordTrace tailWord_647365 prefixEnd_647365 221606269265309943440219 := by
  unfold tailWord_647365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23611341299714640984887549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15740894199809760656591699 23611341299714640984887549)
  ·
    refine ⟨8854252987392990369332831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23611341299714640984887549 8854252987392990369332831)
    ·
      refine ⟨13281379481089485553999247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854252987392990369332831 13281379481089485553999247)
      ·
        refine ⟨19922069221634228330998871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281379481089485553999247 19922069221634228330998871)
        ·
          refine ⟨29883103832451342496498307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19922069221634228330998871 29883103832451342496498307)
          ·
            refine ⟨44824655748677013744747461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29883103832451342496498307 44824655748677013744747461)
            ·
              refine ⟨8404622952876940077140149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44824655748677013744747461 8404622952876940077140149)
              ·
                refine ⟨787933401832213132231889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8404622952876940077140149 787933401832213132231889)
                ·
                  refine ⟨590950051374159849173917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 787933401832213132231889 590950051374159849173917)
                  ·
                    refine ⟨221606269265309943440219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590950051374159849173917 221606269265309943440219)
                    ·
                      rfl

theorem cell22_647365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_647365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647365 prefixEnd_647365 := by exact prefixLift 647365
  have htrace : WordTrace (prefixWord ++ tailWord_647365) baseStart_647365 baseEnd_647365 := by
    simpa [prefixWord, tailWord_647365, baseEnd_647365] using wordTrace_append hprefix tailTrace_647365
  have hstable : (prefixWord ++ tailWord_647365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647365).length < 2 ^ (prefixWord ++ tailWord_647365).sum := by decide
  have hdescent : baseEnd_647365 < baseStart_647365 := by decide
  rcases family_descends (prefixWord ++ tailWord_647365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647500 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_647500 : Nat := 118140960795 + 647500 * 2 ^ 59
def prefixEnd_647500 : Nat := 4983230072969 + 3 ^ 40 * 647500 * 2
def baseEnd_647500 : Nat := 221652482524214591314805

theorem tailTrace_647500 : CollatzResearch.WordTrace tailWord_647500 prefixEnd_647500 221652482524214591314805 := by
  unfold tailWord_647500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808132577112779520525977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15744176769483706027367969 11808132577112779520525977)
  ·
    refine ⟨8856099432834584640394483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11808132577112779520525977 8856099432834584640394483)
    ·
      refine ⟨13284149149251876960591725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856099432834584640394483 13284149149251876960591725)
      ·
        refine ⟨4981555930969453860221897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13284149149251876960591725 4981555930969453860221897)
        ·
          refine ⟨3736166948227090395166423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981555930969453860221897 3736166948227090395166423)
          ·
            refine ⟨5604250422340635592749635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736166948227090395166423 5604250422340635592749635)
            ·
              refine ⟨8406375633510953389124453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604250422340635592749635 8406375633510953389124453)
              ·
                refine ⟨1576195431283303760460835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8406375633510953389124453 1576195431283303760460835)
                ·
                  refine ⟨2364293146924955640691253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576195431283303760460835 2364293146924955640691253)
                  ·
                    refine ⟨221652482524214591314805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2364293146924955640691253 221652482524214591314805)
                    ·
                      rfl

theorem cell22_647500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_647500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647500 prefixEnd_647500 := by exact prefixLift 647500
  have htrace : WordTrace (prefixWord ++ tailWord_647500) baseStart_647500 baseEnd_647500 := by
    simpa [prefixWord, tailWord_647500, baseEnd_647500] using wordTrace_append hprefix tailTrace_647500
  have hstable : (prefixWord ++ tailWord_647500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647500).length < 2 ^ (prefixWord ++ tailWord_647500).sum := by decide
  have hdescent : baseEnd_647500 < baseStart_647500 := by decide
  rcases family_descends (prefixWord ++ tailWord_647500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647504 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_647504 : Nat := 118140960795 + 647504 * 2 ^ 59
def prefixEnd_647504 : Nat := 4983230072969 + 3 ^ 40 * 647504 * 2
def baseEnd_647504 : Nat := 221653851805959914214793

theorem tailTrace_647504 : CollatzResearch.WordTrace tailWord_647504 prefixEnd_647504 221653851805959914214793 := by
  unfold tailWord_647504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808205523105533862098783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15744274030807378482798377 11808205523105533862098783)
  ·
    refine ⟨17712308284658300793148175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11808205523105533862098783 17712308284658300793148175)
    ·
      refine ⟨26568462426987451189722263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17712308284658300793148175 26568462426987451189722263)
      ·
        refine ⟨39852693640481176784583395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26568462426987451189722263 39852693640481176784583395)
        ·
          refine ⟨59779040460721765176875093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39852693640481176784583395 59779040460721765176875093)
          ·
            refine ⟨700535630399083185666505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 59779040460721765176875093 700535630399083185666505)
            ·
              refine ⟨525401722799312389249879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700535630399083185666505 525401722799312389249879)
              ·
                refine ⟨788102584198968583874819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525401722799312389249879 788102584198968583874819)
                ·
                  refine ⟨1182153876298452875812229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788102584198968583874819 1182153876298452875812229)
                  ·
                    refine ⟨221653851805959914214793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182153876298452875812229 221653851805959914214793)
                    ·
                      rfl

theorem cell22_647504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_647504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647504 prefixEnd_647504 := by exact prefixLift 647504
  have htrace : WordTrace (prefixWord ++ tailWord_647504) baseStart_647504 baseEnd_647504 := by
    simpa [prefixWord, tailWord_647504, baseEnd_647504] using wordTrace_append hprefix tailTrace_647504
  have hstable : (prefixWord ++ tailWord_647504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647504).length < 2 ^ (prefixWord ++ tailWord_647504).sum := by decide
  have hdescent : baseEnd_647504 < baseStart_647504 := by decide
  rcases family_descends (prefixWord ++ tailWord_647504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647547 : List Nat := [1, 1, 1, 1, 1, 9, 2, 6]
def baseStart_647547 : Nat := 118140960795 + 647547 * 2 ^ 59
def prefixEnd_647547 : Nat := 4983230072969 + 3 ^ 40 * 647547 * 2
def baseEnd_647547 : Nat := 24629841287191348376629

theorem tailTrace_647547 : CollatzResearch.WordTrace tailWord_647547 prefixEnd_647547 24629841287191348376629 := by
  unfold tailWord_647547
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617979385055286068012895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15745319590036857378675263 23617979385055286068012895)
  ·
    refine ⟨35426969077582929102019343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23617979385055286068012895 35426969077582929102019343)
    ·
      refine ⟨53140453616374393653029015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35426969077582929102019343 53140453616374393653029015)
      ·
        refine ⟨79710680424561590479543523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53140453616374393653029015 79710680424561590479543523)
        ·
          refine ⟨119566020636842385719315285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79710680424561590479543523 119566020636842385719315285)
          ·
            refine ⟨700582152168998353824113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 119566020636842385719315285 700582152168998353824113)
            ·
              refine ⟨525436614126748765368085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700582152168998353824113 525436614126748765368085)
              ·
                refine ⟨24629841287191348376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 525436614126748765368085 24629841287191348376629)
                ·
                  rfl

theorem cell22_647547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 6].length) (baseStart_647547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647547 prefixEnd_647547 := by exact prefixLift 647547
  have htrace : WordTrace (prefixWord ++ tailWord_647547) baseStart_647547 baseEnd_647547 := by
    simpa [prefixWord, tailWord_647547, baseEnd_647547] using wordTrace_append hprefix tailTrace_647547
  have hstable : (prefixWord ++ tailWord_647547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647547).length < 2 ^ (prefixWord ++ tailWord_647547).sum := by decide
  have hdescent : baseEnd_647547 < baseStart_647547 := by decide
  rcases family_descends (prefixWord ++ tailWord_647547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647575 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 7]
def baseStart_647575 : Nat := 118140960795 + 647575 * 2 ^ 59
def prefixEnd_647575 : Nat := 4983230072969 + 3 ^ 40 * 647575 * 2
def baseEnd_647575 : Nat := 73892718852313131896525

theorem tailTrace_647575 : CollatzResearch.WordTrace tailWord_647575 prefixEnd_647575 73892718852313131896525 := by
  unfold tailWord_647575
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619000628953846850032179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15746000419302564566688119 23619000628953846850032179)
  ·
    refine ⟨35428500943430770275048269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23619000628953846850032179 35428500943430770275048269)
    ·
      refine ⟨13285687853786538853143101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35428500943430770275048269 13285687853786538853143101)
      ·
        refine ⟨4982132945169952069928663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13285687853786538853143101 4982132945169952069928663)
        ·
          refine ⟨7473199417754928104892995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982132945169952069928663 7473199417754928104892995)
          ·
            refine ⟨11209799126632392157339493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473199417754928104892995 11209799126632392157339493)
            ·
              refine ⟨2101837336243573529501155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11209799126632392157339493 2101837336243573529501155)
              ·
                refine ⟨3152756004365360294251733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101837336243573529501155 3152756004365360294251733)
                ·
                  refine ⟨73892718852313131896525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3152756004365360294251733 73892718852313131896525)
                  ·
                    rfl

theorem cell22_647575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_647575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647575 prefixEnd_647575 := by exact prefixLift 647575
  have htrace : WordTrace (prefixWord ++ tailWord_647575) baseStart_647575 baseEnd_647575 := by
    simpa [prefixWord, tailWord_647575, baseEnd_647575] using wordTrace_append hprefix tailTrace_647575
  have hstable : (prefixWord ++ tailWord_647575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647575).length < 2 ^ (prefixWord ++ tailWord_647575).sum := by decide
  have hdescent : baseEnd_647575 < baseStart_647575 := by decide
  rcases family_descends (prefixWord ++ tailWord_647575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647585 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_647585 : Nat := 118140960795 + 647585 * 2 ^ 59
def prefixEnd_647585 : Nat := 4983230072969 + 3 ^ 40 * 647585 * 2
def baseEnd_647585 : Nat := 221681579761302702939545

theorem tailTrace_647585 : CollatzResearch.WordTrace tailWord_647585 prefixEnd_647585 221681579761302702939545 := by
  unfold tailWord_647585
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619365358917618557896209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15746243572611745705264139 23619365358917618557896209)
  ·
    refine ⟨17714524019188213918422157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23619365358917618557896209 17714524019188213918422157)
    ·
      refine ⟨6642946507195580219408309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17714524019188213918422157 6642946507195580219408309)
      ·
        refine ⟨622776235049585645569529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6642946507195580219408309 622776235049585645569529)
        ·
          refine ⟨467082176287189234177147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622776235049585645569529 467082176287189234177147)
          ·
            refine ⟨700623264430783851265721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467082176287189234177147 700623264430783851265721)
            ·
              refine ⟨525467448323087888449291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700623264430783851265721 525467448323087888449291)
              ·
                refine ⟨788201172484631832673937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525467448323087888449291 788201172484631832673937)
                ·
                  refine ⟨591150879363473874505453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788201172484631832673937 591150879363473874505453)
                  ·
                    refine ⟨221681579761302702939545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591150879363473874505453 221681579761302702939545)
                    ·
                      rfl

theorem cell22_647585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_647585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647585 prefixEnd_647585 := by exact prefixLift 647585
  have htrace : WordTrace (prefixWord ++ tailWord_647585) baseStart_647585 baseEnd_647585 := by
    simpa [prefixWord, tailWord_647585, baseEnd_647585] using wordTrace_append hprefix tailTrace_647585
  have hstable : (prefixWord ++ tailWord_647585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647585).length < 2 ^ (prefixWord ++ tailWord_647585).sum := by decide
  have hdescent : baseEnd_647585 < baseStart_647585 := by decide
  rcases family_descends (prefixWord ++ tailWord_647585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647652 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_647652 : Nat := 118140960795 + 647652 * 2 ^ 59
def prefixEnd_647652 : Nat := 4983230072969 + 3 ^ 40 * 647652 * 2
def baseEnd_647652 : Nat := 221704515230536861514339

theorem tailTrace_647652 : CollatzResearch.WordTrace tailWord_647652 prefixEnd_647652 221704515230536861514339 := by
  unfold tailWord_647652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810904524837444500292605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15747872699783259333723473 11810904524837444500292605)
  ·
    refine ⟨4429089196814041687609727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11810904524837444500292605 4429089196814041687609727)
    ·
      refine ⟨6643633795221062531414591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429089196814041687609727 6643633795221062531414591)
      ·
        refine ⟨9965450692831593797121887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643633795221062531414591 9965450692831593797121887)
        ·
          refine ⟨14948176039247390695682831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9965450692831593797121887 14948176039247390695682831)
          ·
            refine ⟨22422264058871086043524247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14948176039247390695682831 22422264058871086043524247)
            ·
              refine ⟨33633396088306629065286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22422264058871086043524247 33633396088306629065286371)
              ·
                refine ⟨50450094132459943597929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33633396088306629065286371 50450094132459943597929557)
                ·
                  refine ⟨591212040614764964038237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 50450094132459943597929557 591212040614764964038237)
                  ·
                    refine ⟨221704515230536861514339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591212040614764964038237 221704515230536861514339)
                    ·
                      rfl

theorem cell22_647652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_647652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647652 prefixEnd_647652 := by exact prefixLift 647652
  have htrace : WordTrace (prefixWord ++ tailWord_647652) baseStart_647652 baseEnd_647652 := by
    simpa [prefixWord, tailWord_647652, baseEnd_647652] using wordTrace_append hprefix tailTrace_647652
  have hstable : (prefixWord ++ tailWord_647652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647652).length < 2 ^ (prefixWord ++ tailWord_647652).sum := by decide
  have hdescent : baseEnd_647652 < baseStart_647652 := by decide
  rcases family_descends (prefixWord ++ tailWord_647652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647680 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_647680 : Nat := 118140960795 + 647680 * 2 ^ 59
def prefixEnd_647680 : Nat := 4983230072969 + 3 ^ 40 * 647680 * 2
def baseEnd_647680 : Nat := 221714100202754121814253

theorem tailTrace_647680 : CollatzResearch.WordTrace tailWord_647680 prefixEnd_647680 221714100202754121814253 := by
  unfold tailWord_647680
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811415146786724891302247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15748553529048966521736329 11811415146786724891302247)
  ·
    refine ⟨17717122720180087336953371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811415146786724891302247 17717122720180087336953371)
    ·
      refine ⟨26575684080270131005430057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17717122720180087336953371 26575684080270131005430057)
      ·
        refine ⟨19931763060202598254072543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26575684080270131005430057 19931763060202598254072543)
        ·
          refine ⟨29897644590303897381108815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19931763060202598254072543 29897644590303897381108815)
          ·
            refine ⟨44846466885455846071663223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29897644590303897381108815 44846466885455846071663223)
            ·
              refine ⟨67269700328183769107494835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44846466885455846071663223 67269700328183769107494835)
              ·
                refine ⟨100904550492275653661242253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67269700328183769107494835 100904550492275653661242253)
                ·
                  refine ⟨37839206434603370122965845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100904550492275653661242253 37839206434603370122965845)
                  ·
                    refine ⟨221714100202754121814253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37839206434603370122965845 221714100202754121814253)
                    ·
                      rfl

theorem cell22_647680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_647680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647680 prefixEnd_647680 := by exact prefixLift 647680
  have htrace : WordTrace (prefixWord ++ tailWord_647680) baseStart_647680 baseEnd_647680 := by
    simpa [prefixWord, tailWord_647680, baseEnd_647680] using wordTrace_append hprefix tailTrace_647680
  have hstable : (prefixWord ++ tailWord_647680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647680).length < 2 ^ (prefixWord ++ tailWord_647680).sum := by decide
  have hdescent : baseEnd_647680 < baseStart_647680 := by decide
  rcases family_descends (prefixWord ++ tailWord_647680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647703 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 5]
def baseStart_647703 : Nat := 118140960795 + 647703 * 2 ^ 59
def prefixEnd_647703 : Nat := 4983230072969 + 3 ^ 40 * 647703 * 2
def baseEnd_647703 : Nat := 221721973572789728489183

theorem tailTrace_647703 : CollatzResearch.WordTrace tailWord_647703 prefixEnd_647703 221721973572789728489183 := by
  unfold tailWord_647703
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623669172490124710691763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15749112781660083140461175 23623669172490124710691763)
  ·
    refine ⟨35435503758735187066037645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623669172490124710691763 35435503758735187066037645)
    ·
      refine ⟨13288313909525695149764117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35435503758735187066037645 13288313909525695149764117)
      ·
        refine ⟨622889714509016960145193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13288313909525695149764117 622889714509016960145193)
        ·
          refine ⟨467167285881762720108895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622889714509016960145193 467167285881762720108895)
          ·
            refine ⟨700750928822644080163343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467167285881762720108895 700750928822644080163343)
            ·
              refine ⟨1051126393233966120245015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700750928822644080163343 1051126393233966120245015)
              ·
                refine ⟨1576689589850949180367523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051126393233966120245015 1576689589850949180367523)
                ·
                  refine ⟨2365034384776423770551285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576689589850949180367523 2365034384776423770551285)
                  ·
                    refine ⟨221721973572789728489183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2365034384776423770551285 221721973572789728489183)
                    ·
                      rfl

theorem cell22_647703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_647703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647703 prefixEnd_647703 := by exact prefixLift 647703
  have htrace : WordTrace (prefixWord ++ tailWord_647703) baseStart_647703 baseEnd_647703 := by
    simpa [prefixWord, tailWord_647703, baseEnd_647703] using wordTrace_append hprefix tailTrace_647703
  have hstable : (prefixWord ++ tailWord_647703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647703).length < 2 ^ (prefixWord ++ tailWord_647703).sum := by decide
  have hdescent : baseEnd_647703 < baseStart_647703 := by decide
  rcases family_descends (prefixWord ++ tailWord_647703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647761 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 5]
def baseStart_647761 : Nat := 118140960795 + 647761 * 2 ^ 59
def prefixEnd_647761 : Nat := 4983230072969 + 3 ^ 40 * 647761 * 2
def baseEnd_647761 : Nat := 73913942719365636846335

theorem tailTrace_647761 : CollatzResearch.WordTrace tailWord_647761 prefixEnd_647761 73913942719365636846335 := by
  unfold tailWord_647761
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625784606280000616303137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15750523070853333744202091 23625784606280000616303137)
  ·
    refine ⟨17719338454710000462227353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23625784606280000616303137 17719338454710000462227353)
    ·
      refine ⟨13289503841032500346670515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17719338454710000462227353 13289503841032500346670515)
      ·
        refine ⟨19934255761548750520005773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289503841032500346670515 19934255761548750520005773)
        ·
          refine ⟨7475345910580781445002165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19934255761548750520005773 7475345910580781445002165)
          ·
            refine ⟨700813679116948260468953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7475345910580781445002165 700813679116948260468953)
            ·
              refine ⟨525610259337711195351715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700813679116948260468953 525610259337711195351715)
              ·
                refine ⟨788415389006566793027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525610259337711195351715 788415389006566793027573)
                ·
                  refine ⟨73913942719365636846335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788415389006566793027573 73913942719365636846335)
                  ·
                    rfl

theorem cell22_647761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_647761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647761 prefixEnd_647761 := by exact prefixLift 647761
  have htrace : WordTrace (prefixWord ++ tailWord_647761) baseStart_647761 baseEnd_647761 := by
    simpa [prefixWord, tailWord_647761, baseEnd_647761] using wordTrace_append hprefix tailTrace_647761
  have hstable : (prefixWord ++ tailWord_647761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647761).length < 2 ^ (prefixWord ++ tailWord_647761).sum := by decide
  have hdescent : baseEnd_647761 < baseStart_647761 := by decide
  rcases family_descends (prefixWord ++ tailWord_647761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647804 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_647804 : Nat := 118140960795 + 647804 * 2 ^ 59
def prefixEnd_647804 : Nat := 4983230072969 + 3 ^ 40 * 647804 * 2
def baseEnd_647804 : Nat := 221756547936859131713873

theorem tailTrace_647804 : CollatzResearch.WordTrace tailWord_647804 prefixEnd_647804 221756547936859131713873 := by
  unfold tailWord_647804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813676472562109480059233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15751568630082812640078977 11813676472562109480059233)
  ·
    refine ⟨8860257354421582110044425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11813676472562109480059233 8860257354421582110044425)
    ·
      refine ⟨6645193015816186582533319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8860257354421582110044425 6645193015816186582533319)
      ·
        refine ⟨9967789523724279873799979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6645193015816186582533319 9967789523724279873799979)
        ·
          refine ⟨14951684285586419810699969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9967789523724279873799979 14951684285586419810699969)
          ·
            refine ⟨11213763214189814858024977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14951684285586419810699969 11213763214189814858024977)
            ·
              refine ⟨8410322410642361143518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213763214189814858024977 8410322410642361143518733)
              ·
                refine ⟨3153870903990885428819525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8410322410642361143518733 3153870903990885428819525)
                ·
                  refine ⟨591350794498291017903661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3153870903990885428819525 591350794498291017903661)
                  ·
                    refine ⟨221756547936859131713873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591350794498291017903661 221756547936859131713873)
                    ·
                      rfl

theorem cell22_647804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_647804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647804 prefixEnd_647804 := by exact prefixLift 647804
  have htrace : WordTrace (prefixWord ++ tailWord_647804) baseStart_647804 baseEnd_647804 := by
    simpa [prefixWord, tailWord_647804, baseEnd_647804] using wordTrace_append hprefix tailTrace_647804
  have hstable : (prefixWord ++ tailWord_647804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647804).length < 2 ^ (prefixWord ++ tailWord_647804).sum := by decide
  have hdescent : baseEnd_647804 < baseStart_647804 := by decide
  rcases family_descends (prefixWord ++ tailWord_647804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647810 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_647810 : Nat := 118140960795 + 647810 * 2 ^ 59
def prefixEnd_647810 : Nat := 4983230072969 + 3 ^ 40 * 647810 * 2
def baseEnd_647810 : Nat := 221758601859477116063855

theorem tailTrace_647810 : CollatzResearch.WordTrace tailWord_647810 prefixEnd_647810 221758601859477116063855 := by
  unfold tailWord_647810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906892945775620496209221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15751714522068321323224589 5906892945775620496209221)
  ·
    refine ⟨1107542427332928843039229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5906892945775620496209221 1107542427332928843039229)
    ·
      refine ⟨415328410249848316139711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1107542427332928843039229 415328410249848316139711)
      ·
        refine ⟨622992615374772474209567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415328410249848316139711 622992615374772474209567)
        ·
          refine ⟨934488923062158711314351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622992615374772474209567 934488923062158711314351)
          ·
            refine ⟨1401733384593238066971527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934488923062158711314351 1401733384593238066971527)
            ·
              refine ⟨2102600076889857100457291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401733384593238066971527 2102600076889857100457291)
              ·
                refine ⟨3153900115334785650685937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102600076889857100457291 3153900115334785650685937)
                ·
                  refine ⟨2365425086501089238014453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153900115334785650685937 2365425086501089238014453)
                  ·
                    refine ⟨221758601859477116063855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2365425086501089238014453 221758601859477116063855)
                    ·
                      rfl

theorem cell22_647810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_647810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647810 prefixEnd_647810 := by exact prefixLift 647810
  have htrace : WordTrace (prefixWord ++ tailWord_647810) baseStart_647810 baseEnd_647810 := by
    simpa [prefixWord, tailWord_647810, baseEnd_647810] using wordTrace_append hprefix tailTrace_647810
  have hstable : (prefixWord ++ tailWord_647810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647810).length < 2 ^ (prefixWord ++ tailWord_647810).sum := by decide
  have hdescent : baseEnd_647810 < baseStart_647810 := by decide
  rcases family_descends (prefixWord ++ tailWord_647810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647836 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_647836 : Nat := 118140960795 + 647836 * 2 ^ 59
def prefixEnd_647836 : Nat := 4983230072969 + 3 ^ 40 * 647836 * 2
def baseEnd_647836 : Nat := 221767502190821714913775

theorem tailTrace_647836 : CollatzResearch.WordTrace tailWord_647836 prefixEnd_647836 221767502190821714913775 := by
  unfold tailWord_647836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814260040504144212641681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15752346720672192283522241 11814260040504144212641681)
  ·
    refine ⟨8860695030378108159481261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11814260040504144212641681 8860695030378108159481261)
    ·
      refine ⟨3322760636391790559805473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8860695030378108159481261 3322760636391790559805473)
      ·
        refine ⟨2492070477293842919854105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3322760636391790559805473 2492070477293842919854105)
        ·
          refine ⟨1869052857970382189890579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492070477293842919854105 1869052857970382189890579)
          ·
            refine ⟨2803579286955573284835869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869052857970382189890579 2803579286955573284835869)
            ·
              refine ⟨1051342232608339981813451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803579286955573284835869 1051342232608339981813451)
              ·
                refine ⟨1577013348912509972720177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051342232608339981813451 1577013348912509972720177)
                ·
                  refine ⟨1182760011684382479540133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577013348912509972720177 1182760011684382479540133)
                  ·
                    refine ⟨221767502190821714913775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182760011684382479540133 221767502190821714913775)
                    ·
                      rfl

theorem cell22_647836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_647836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647836 prefixEnd_647836 := by exact prefixLift 647836
  have htrace : WordTrace (prefixWord ++ tailWord_647836) baseStart_647836 baseEnd_647836 := by
    simpa [prefixWord, tailWord_647836, baseEnd_647836] using wordTrace_append hprefix tailTrace_647836
  have hstable : (prefixWord ++ tailWord_647836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647836).length < 2 ^ (prefixWord ++ tailWord_647836).sum := by decide
  have hdescent : baseEnd_647836 < baseStart_647836 := by decide
  rcases family_descends (prefixWord ++ tailWord_647836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647866 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_647866 : Nat := 118140960795 + 647866 * 2 ^ 59
def prefixEnd_647866 : Nat := 4983230072969 + 3 ^ 40 * 647866 * 2
def baseEnd_647866 : Nat := 221777771803911636663683

theorem tailTrace_647866 : CollatzResearch.WordTrace tailWord_647866 prefixEnd_647866 221777771803911636663683 := by
  unfold tailWord_647866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907403567724900887218863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15753076180599735699250301 5907403567724900887218863)
  ·
    refine ⟨8861105351587351330828295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5907403567724900887218863 8861105351587351330828295)
    ·
      refine ⟨13291658027381026996242443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8861105351587351330828295 13291658027381026996242443)
      ·
        refine ⟨19937487041071540494363665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291658027381026996242443 19937487041071540494363665)
        ·
          refine ⟨14953115280803655370772749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19937487041071540494363665 14953115280803655370772749)
          ·
            refine ⟨5607418230301370764039781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14953115280803655370772749 5607418230301370764039781)
            ·
              refine ⟨1051390918181507018257459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5607418230301370764039781 1051390918181507018257459)
              ·
                refine ⟨1577086377272260527386189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051390918181507018257459 1577086377272260527386189)
                ·
                  refine ⟨591407391477097697769821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577086377272260527386189 591407391477097697769821)
                  ·
                    refine ⟨221777771803911636663683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591407391477097697769821 221777771803911636663683)
                    ·
                      rfl

theorem cell22_647866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_647866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647866 prefixEnd_647866 := by exact prefixLift 647866
  have htrace : WordTrace (prefixWord ++ tailWord_647866) baseStart_647866 baseEnd_647866 := by
    simpa [prefixWord, tailWord_647866, baseEnd_647866] using wordTrace_append hprefix tailTrace_647866
  have hstable : (prefixWord ++ tailWord_647866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647866).length < 2 ^ (prefixWord ++ tailWord_647866).sum := by decide
  have hdescent : baseEnd_647866 < baseStart_647866 := by decide
  rcases family_descends (prefixWord ++ tailWord_647866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647885 : List Nat := [1, 6, 2, 1, 2, 2, 2, 6]
def baseStart_647885 : Nat := 118140960795 + 647885 * 2 ^ 59
def prefixEnd_647885 : Nat := 4983230072969 + 3 ^ 40 * 647885 * 2
def baseEnd_647885 : Nat := 24642697321355768937625

theorem tailTrace_647885 : CollatzResearch.WordTrace tailWord_647885 prefixEnd_647885 24642697321355768937625 := by
  unfold tailWord_647885
  simp only [CollatzResearch.WordTrace]
  refine ⟨23630307257830769793817109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15753538171887179862544739 23630307257830769793817109)
  ·
    refine ⟨1107670652710817334085177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23630307257830769793817109 1107670652710817334085177)
    ·
      refine ⟨830752989533113000563883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107670652710817334085177 830752989533113000563883)
      ·
        refine ⟨1246129484299669500845825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830752989533113000563883 1246129484299669500845825)
        ·
          refine ⟨934597113224752125634369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1246129484299669500845825 934597113224752125634369)
          ·
            refine ⟨700947834918564094225777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934597113224752125634369 700947834918564094225777)
            ·
              refine ⟨525710876188923070669333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700947834918564094225777 525710876188923070669333)
              ·
                refine ⟨24642697321355768937625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 525710876188923070669333 24642697321355768937625)
                ·
                  rfl

theorem cell22_647885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 6].length) (baseStart_647885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647885 prefixEnd_647885 := by exact prefixLift 647885
  have htrace : WordTrace (prefixWord ++ tailWord_647885) baseStart_647885 baseEnd_647885 := by
    simpa [prefixWord, tailWord_647885, baseEnd_647885] using wordTrace_append hprefix tailTrace_647885
  have hstable : (prefixWord ++ tailWord_647885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647885).length < 2 ^ (prefixWord ++ tailWord_647885).sum := by decide
  have hdescent : baseEnd_647885 < baseStart_647885 := by decide
  rcases family_descends (prefixWord ++ tailWord_647885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647926 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_647926 : Nat := 118140960795 + 647926 * 2 ^ 59
def prefixEnd_647926 : Nat := 4983230072969 + 3 ^ 40 * 647926 * 2
def baseEnd_647926 : Nat := 221798311030091480163499

theorem tailTrace_647926 : CollatzResearch.WordTrace tailWord_647926 prefixEnd_647926 221798311030091480163499 := by
  unfold tailWord_647926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476987665667639612253727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15754535100454822530706421 1476987665667639612253727)
  ·
    refine ⟨2215481498501459418380591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476987665667639612253727 2215481498501459418380591)
    ·
      refine ⟨3323222247752189127570887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215481498501459418380591 3323222247752189127570887)
      ·
        refine ⟨4984833371628283691356331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323222247752189127570887 4984833371628283691356331)
        ·
          refine ⟨7477250057442425537034497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984833371628283691356331 7477250057442425537034497)
          ·
            refine ⟨5607937543081819152775873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477250057442425537034497 5607937543081819152775873)
            ·
              refine ⟨4205953157311364364581905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5607937543081819152775873 4205953157311364364581905)
              ·
                refine ⟨3154464867983523273436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205953157311364364581905 3154464867983523273436429)
                ·
                  refine ⟨1182924325493821227538661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3154464867983523273436429 1182924325493821227538661)
                  ·
                    refine ⟨221798311030091480163499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182924325493821227538661 221798311030091480163499)
                    ·
                      rfl

theorem cell22_647926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_647926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647926 prefixEnd_647926 := by exact prefixLift 647926
  have htrace : WordTrace (prefixWord ++ tailWord_647926) baseStart_647926 baseEnd_647926 := by
    simpa [prefixWord, tailWord_647926, baseEnd_647926] using wordTrace_append hprefix tailTrace_647926
  have hstable : (prefixWord ++ tailWord_647926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647926).length < 2 ^ (prefixWord ++ tailWord_647926).sum := by decide
  have hdescent : baseEnd_647926 < baseStart_647926 := by decide
  rcases family_descends (prefixWord ++ tailWord_647926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647939 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_647939 : Nat := 118140960795 + 647939 * 2 ^ 59
def prefixEnd_647939 : Nat := 4983230072969 + 3 ^ 40 * 647939 * 2
def baseEnd_647939 : Nat := 221802761195763779588459

theorem tailTrace_647939 : CollatzResearch.WordTrace tailWord_647939 prefixEnd_647939 221802761195763779588459 := by
  unfold tailWord_647939
  simp only [CollatzResearch.WordTrace]
  refine ⟨23632276799635137016282871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15754851199756758010855247 23632276799635137016282871)
  ·
    refine ⟨35448415199452705524424307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23632276799635137016282871 35448415199452705524424307)
    ·
      refine ⟨53172622799179058286636461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35448415199452705524424307 53172622799179058286636461)
      ·
        refine ⟨19939733549692146857488673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53172622799179058286636461 19939733549692146857488673)
        ·
          refine ⟨14954800162269110143116505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19939733549692146857488673 14954800162269110143116505)
          ·
            refine ⟨11216100121701832607337379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14954800162269110143116505 11216100121701832607337379)
            ·
              refine ⟨16824150182552748911006069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11216100121701832607337379 16824150182552748911006069)
              ·
                refine ⟨1577264079614320210406819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16824150182552748911006069 1577264079614320210406819)
                ·
                  refine ⟨2365896119421480315610229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577264079614320210406819 2365896119421480315610229)
                  ·
                    refine ⟨221802761195763779588459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2365896119421480315610229 221802761195763779588459)
                    ·
                      rfl

theorem cell22_647939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_647939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647939 prefixEnd_647939 := by exact prefixLift 647939
  have htrace : WordTrace (prefixWord ++ tailWord_647939) baseStart_647939 baseEnd_647939 := by
    simpa [prefixWord, tailWord_647939, baseEnd_647939] using wordTrace_append hprefix tailTrace_647939
  have hstable : (prefixWord ++ tailWord_647939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647939).length < 2 ^ (prefixWord ++ tailWord_647939).sum := by decide
  have hdescent : baseEnd_647939 < baseStart_647939 := by decide
  rcases family_descends (prefixWord ++ tailWord_647939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647943 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 1, 4]
def baseStart_647943 : Nat := 118140960795 + 647943 * 2 ^ 59
def prefixEnd_647943 : Nat := 4983230072969 + 3 ^ 40 * 647943 * 2
def baseEnd_647943 : Nat := 221804130477509102488447

theorem tailTrace_647943 : CollatzResearch.WordTrace tailWord_647943 prefixEnd_647943 221804130477509102488447 := by
  unfold tailWord_647943
  simp only [CollatzResearch.WordTrace]
  refine ⟨23632422691620645699428483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15754948461080430466285655 23632422691620645699428483)
  ·
    refine ⟨35448634037430968549142725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23632422691620645699428483 35448634037430968549142725)
    ·
      refine ⟨6646618882018306602964261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35448634037430968549142725 6646618882018306602964261)
      ·
        refine ⟨1246241040378432488055799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6646618882018306602964261 1246241040378432488055799)
        ·
          refine ⟨1869361560567648732083699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246241040378432488055799 1869361560567648732083699)
          ·
            refine ⟨2804042340851473098125549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869361560567648732083699 2804042340851473098125549)
            ·
              refine ⟨1051515877819302411797081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804042340851473098125549 1051515877819302411797081)
              ·
                refine ⟨788636908364476808847811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051515877819302411797081 788636908364476808847811)
                ·
                  refine ⟨1182955362546715213271717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788636908364476808847811 1182955362546715213271717)
                  ·
                    refine ⟨221804130477509102488447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182955362546715213271717 221804130477509102488447)
                    ·
                      rfl

theorem cell22_647943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_647943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647943 prefixEnd_647943 := by exact prefixLift 647943
  have htrace : WordTrace (prefixWord ++ tailWord_647943) baseStart_647943 baseEnd_647943 := by
    simpa [prefixWord, tailWord_647943, baseEnd_647943] using wordTrace_append hprefix tailTrace_647943
  have hstable : (prefixWord ++ tailWord_647943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647943).length < 2 ^ (prefixWord ++ tailWord_647943).sum := by decide
  have hdescent : baseEnd_647943 < baseStart_647943 := by decide
  rcases family_descends (prefixWord ++ tailWord_647943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647973 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_647973 : Nat := 118140960795 + 647973 * 2 ^ 59
def prefixEnd_647973 : Nat := 4983230072969 + 3 ^ 40 * 647973 * 2
def baseEnd_647973 : Nat := 221814400090599024238355

theorem tailTrace_647973 : CollatzResearch.WordTrace tailWord_647973 prefixEnd_647973 221814400090599024238355 := by
  unfold tailWord_647973
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633516881511960823020573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15755677921007973882013715 23633516881511960823020573)
  ·
    refine ⟨8862568830566985308632715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23633516881511960823020573 8862568830566985308632715)
    ·
      refine ⟨13293853245850477962949073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862568830566985308632715 13293853245850477962949073)
      ·
        refine ⟨9970389934387858472211805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13293853245850477962949073 9970389934387858472211805)
        ·
          refine ⟨3738896225395446927079427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9970389934387858472211805 3738896225395446927079427)
          ·
            refine ⟨5608344338093170390619141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738896225395446927079427 5608344338093170390619141)
            ·
              refine ⟨1051564563392469448241089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5608344338093170390619141 1051564563392469448241089)
              ·
                refine ⟨788673422544352086180817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051564563392469448241089 788673422544352086180817)
                ·
                  refine ⟨591505066908264064635613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788673422544352086180817 591505066908264064635613)
                  ·
                    refine ⟨221814400090599024238355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591505066908264064635613 221814400090599024238355)
                    ·
                      rfl

theorem cell22_647973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_647973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647973 prefixEnd_647973 := by exact prefixLift 647973
  have htrace : WordTrace (prefixWord ++ tailWord_647973) baseStart_647973 baseEnd_647973 := by
    simpa [prefixWord, tailWord_647973, baseEnd_647973] using wordTrace_append hprefix tailTrace_647973
  have hstable : (prefixWord ++ tailWord_647973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647973).length < 2 ^ (prefixWord ++ tailWord_647973).sum := by decide
  have hdescent : baseEnd_647973 < baseStart_647973 := by decide
  rcases family_descends (prefixWord ++ tailWord_647973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647990 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_647990 : Nat := 118140960795 + 647990 * 2 ^ 59
def prefixEnd_647990 : Nat := 4983230072969 + 3 ^ 40 * 647990 * 2
def baseEnd_647990 : Nat := 221820219538016646563303

theorem tailTrace_647990 : CollatzResearch.WordTrace tailWord_647990 prefixEnd_647990 221820219538016646563303 := by
  unfold tailWord_647990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477133557653148295399339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15756091281633581817592949 1477133557653148295399339)
  ·
    refine ⟨2215700336479722443099009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1477133557653148295399339 2215700336479722443099009)
    ·
      refine ⟨1661775252359791832324257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2215700336479722443099009 1661775252359791832324257)
      ·
        refine ⟨1246331439269843874243193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1661775252359791832324257 1246331439269843874243193)
        ·
          refine ⟨934748579452382905682395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1246331439269843874243193 934748579452382905682395)
          ·
            refine ⟨1402122869178574358523593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934748579452382905682395 1402122869178574358523593)
            ·
              refine ⟨1051592151883930768892695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402122869178574358523593 1051592151883930768892695)
              ·
                refine ⟨1577388227825896153339043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051592151883930768892695 1577388227825896153339043)
                ·
                  refine ⟨2366082341738844230008565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577388227825896153339043 2366082341738844230008565)
                  ·
                    refine ⟨221820219538016646563303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2366082341738844230008565 221820219538016646563303)
                    ·
                      rfl

theorem cell22_647990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_647990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_647990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_647990 prefixEnd_647990 := by exact prefixLift 647990
  have htrace : WordTrace (prefixWord ++ tailWord_647990) baseStart_647990 baseEnd_647990 := by
    simpa [prefixWord, tailWord_647990, baseEnd_647990] using wordTrace_append hprefix tailTrace_647990
  have hstable : (prefixWord ++ tailWord_647990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647990).length < 2 ^ (prefixWord ++ tailWord_647990).sum := by decide
  have hdescent : baseEnd_647990 < baseStart_647990 := by decide
  rcases family_descends (prefixWord ++ tailWord_647990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648035 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 1, 3]
def baseStart_648035 : Nat := 118140960795 + 648035 * 2 ^ 59
def prefixEnd_648035 : Nat := 4983230072969 + 3 ^ 40 * 648035 * 2
def baseEnd_648035 : Nat := 221835623957651529188165

theorem tailTrace_648035 : CollatzResearch.WordTrace tailWord_648035 prefixEnd_648035 221835623957651529188165 := by
  unfold tailWord_648035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23635778207287345411777559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15757185471524896941185039 23635778207287345411777559)
  ·
    refine ⟨35453667310931018117666339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23635778207287345411777559 35453667310931018117666339)
    ·
      refine ⟨53180500966396527176499509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35453667310931018117666339 53180500966396527176499509)
      ·
        refine ⟨4985671965599674422796829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53180500966396527176499509 4985671965599674422796829)
        ·
          refine ⟨1869626987099877908548811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4985671965599674422796829 1869626987099877908548811)
          ·
            refine ⟨2804440480649816862823217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869626987099877908548811 2804440480649816862823217)
            ·
              refine ⟨2103330360487362647117413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804440480649816862823217 2103330360487362647117413)
              ·
                refine ⟨394374442591380496334515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2103330360487362647117413 394374442591380496334515)
                ·
                  refine ⟨591561663887070744501773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394374442591380496334515 591561663887070744501773)
                  ·
                    refine ⟨221835623957651529188165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591561663887070744501773 221835623957651529188165)
                    ·
                      rfl

theorem cell22_648035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 3].length) (baseStart_648035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648035 prefixEnd_648035 := by exact prefixLift 648035
  have htrace : WordTrace (prefixWord ++ tailWord_648035) baseStart_648035 baseEnd_648035 := by
    simpa [prefixWord, tailWord_648035, baseEnd_648035] using wordTrace_append hprefix tailTrace_648035
  have hstable : (prefixWord ++ tailWord_648035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648035).length < 2 ^ (prefixWord ++ tailWord_648035).sum := by decide
  have hdescent : baseEnd_648035 < baseStart_648035 := by decide
  rcases family_descends (prefixWord ++ tailWord_648035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648061 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_648061 : Nat := 118140960795 + 648061 * 2 ^ 59
def prefixEnd_648061 : Nat := 4983230072969 + 3 ^ 40 * 648061 * 2
def baseEnd_648061 : Nat := 221844524288996128038085

theorem tailTrace_648061 : CollatzResearch.WordTrace tailWord_648061 prefixEnd_648061 221844524288996128038085 := by
  unfold tailWord_648061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636726505193151852224037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15757817670128767901482691 23636726505193151852224037)
  ·
    refine ⟨4431886219723715972292007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23636726505193151852224037 4431886219723715972292007)
    ·
      refine ⟨6647829329585573958438011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431886219723715972292007 6647829329585573958438011)
      ·
        refine ⟨9971743994378360937657017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647829329585573958438011 9971743994378360937657017)
        ·
          refine ⟨7478807995783770703242763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9971743994378360937657017 7478807995783770703242763)
          ·
            refine ⟨11218211993675656054864145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478807995783770703242763 11218211993675656054864145)
            ·
              refine ⟨8413658995256742041148109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11218211993675656054864145 8413658995256742041148109)
              ·
                refine ⟨3155122123221278265430541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8413658995256742041148109 3155122123221278265430541)
                ·
                  refine ⟨1183170796207979349536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3155122123221278265430541 1183170796207979349536453)
                  ·
                    refine ⟨221844524288996128038085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183170796207979349536453 221844524288996128038085)
                    ·
                      rfl

theorem cell22_648061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_648061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648061 prefixEnd_648061 := by exact prefixLift 648061
  have htrace : WordTrace (prefixWord ++ tailWord_648061) baseStart_648061 baseEnd_648061 := by
    simpa [prefixWord, tailWord_648061, baseEnd_648061] using wordTrace_append hprefix tailTrace_648061
  have hstable : (prefixWord ++ tailWord_648061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648061).length < 2 ^ (prefixWord ++ tailWord_648061).sum := by decide
  have hdescent : baseEnd_648061 < baseStart_648061 := by decide
  rcases family_descends (prefixWord ++ tailWord_648061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648108 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_648108 : Nat := 118140960795 + 648108 * 2 ^ 59
def prefixEnd_648108 : Nat := 4983230072969 + 3 ^ 40 * 648108 * 2
def baseEnd_648108 : Nat := 221860613349503672112941

theorem tailTrace_648108 : CollatzResearch.WordTrace tailWord_648108 prefixEnd_648108 221860613349503672112941 := by
  unfold tailWord_648108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819220368011439439592489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15758960490681919252789985 11819220368011439439592489)
  ·
    refine ⟨8864415276008579579694367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11819220368011439439592489 8864415276008579579694367)
    ·
      refine ⟨13296622914012869369541551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864415276008579579694367 13296622914012869369541551)
      ·
        refine ⟨19944934371019304054312327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13296622914012869369541551 19944934371019304054312327)
        ·
          refine ⟨29917401556528956081468491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19944934371019304054312327 29917401556528956081468491)
          ·
            refine ⟨44876102334793434122202737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29917401556528956081468491 44876102334793434122202737)
            ·
              refine ⟨33657076751095075591652053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44876102334793434122202737 33657076751095075591652053)
              ·
                refine ⟨788837736353790834179345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33657076751095075591652053 788837736353790834179345)
                ·
                  refine ⟨591628302265343125634509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788837736353790834179345 591628302265343125634509)
                  ·
                    refine ⟨221860613349503672112941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591628302265343125634509 221860613349503672112941)
                    ·
                      rfl

theorem cell22_648108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_648108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648108 prefixEnd_648108 := by exact prefixLift 648108
  have htrace : WordTrace (prefixWord ++ tailWord_648108) baseStart_648108 baseEnd_648108 := by
    simpa [prefixWord, tailWord_648108, baseEnd_648108] using wordTrace_append hprefix tailTrace_648108
  have hstable : (prefixWord ++ tailWord_648108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648108).length < 2 ^ (prefixWord ++ tailWord_648108).sum := by decide
  have hdescent : baseEnd_648108 < baseStart_648108 := by decide
  rcases family_descends (prefixWord ++ tailWord_648108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648121 : List Nat := [1, 2, 1, 4, 2, 2, 2, 8]
def baseStart_648121 : Nat := 118140960795 + 648121 * 2 ^ 59
def prefixEnd_648121 : Nat := 4983230072969 + 3 ^ 40 * 648121 * 2
def baseEnd_648121 : Nat := 24651673723908441281989

theorem tailTrace_648121 : CollatzResearch.WordTrace tailWord_648121 prefixEnd_648121 24651673723908441281989 := by
  unfold tailWord_648121
  simp only [CollatzResearch.WordTrace]
  refine ⟨23638914884975782099408217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15759276589983854732938811 23638914884975782099408217)
  ·
    refine ⟨17729186163731836574556163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23638914884975782099408217 17729186163731836574556163)
    ·
      refine ⟨26593779245597754861834245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17729186163731836574556163 26593779245597754861834245)
      ·
        refine ⟨4986333608549579036593921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26593779245597754861834245 4986333608549579036593921)
        ·
          refine ⟨3739750206412184277445441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986333608549579036593921 3739750206412184277445441)
          ·
            refine ⟨2804812654809138208084081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739750206412184277445441 2804812654809138208084081)
            ·
              refine ⟨2103609491106853656063061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804812654809138208084081 2103609491106853656063061)
              ·
                refine ⟨24651673723908441281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2103609491106853656063061 24651673723908441281989)
                ·
                  rfl

theorem cell22_648121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 8].length) (baseStart_648121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648121 prefixEnd_648121 := by exact prefixLift 648121
  have htrace : WordTrace (prefixWord ++ tailWord_648121) baseStart_648121 baseEnd_648121 := by
    simpa [prefixWord, tailWord_648121, baseEnd_648121] using wordTrace_append hprefix tailTrace_648121
  have hstable : (prefixWord ++ tailWord_648121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648121).length < 2 ^ (prefixWord ++ tailWord_648121).sum := by decide
  have hdescent : baseEnd_648121 < baseStart_648121 := by decide
  rcases family_descends (prefixWord ++ tailWord_648121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648170 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_648170 : Nat := 118140960795 + 648170 * 2 ^ 59
def prefixEnd_648170 : Nat := 4983230072969 + 3 ^ 40 * 648170 * 2
def baseEnd_648170 : Nat := 221881837216556177062751

theorem tailTrace_648170 : CollatzResearch.WordTrace tailWord_648170 prefixEnd_648170 221881837216556177062751 := by
  unfold tailWord_648170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910175515449565866985491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15760468041198842311961309 5910175515449565866985491)
  ·
    refine ⟨8865263273174348800478237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910175515449565866985491 8865263273174348800478237)
    ·
      refine ⟨3324473727440380800179339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8865263273174348800478237 3324473727440380800179339)
      ·
        refine ⟨4986710591160571200269009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324473727440380800179339 4986710591160571200269009)
        ·
          refine ⟨3740032943370428400201757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986710591160571200269009 3740032943370428400201757)
          ·
            refine ⟨1402512353763910650075659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3740032943370428400201757 1402512353763910650075659)
            ·
              refine ⟨2103768530645865975113489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402512353763910650075659 2103768530645865975113489)
              ·
                refine ⟨1577826397984399481335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103768530645865975113489 1577826397984399481335117)
                ·
                  refine ⟨591684899244149805500669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577826397984399481335117 591684899244149805500669)
                  ·
                    refine ⟨221881837216556177062751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591684899244149805500669 221881837216556177062751)
                    ·
                      rfl

theorem cell22_648170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_648170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648170 prefixEnd_648170 := by exact prefixLift 648170
  have htrace : WordTrace (prefixWord ++ tailWord_648170) baseStart_648170 baseEnd_648170 := by
    simpa [prefixWord, tailWord_648170, baseEnd_648170] using wordTrace_append hprefix tailTrace_648170
  have hstable : (prefixWord ++ tailWord_648170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648170).length < 2 ^ (prefixWord ++ tailWord_648170).sum := by decide
  have hdescent : baseEnd_648170 < baseStart_648170 := by decide
  rcases family_descends (prefixWord ++ tailWord_648170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648180 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_648180 : Nat := 118140960795 + 648180 * 2 ^ 59
def prefixEnd_648180 : Nat := 4983230072969 + 3 ^ 40 * 648180 * 2
def baseEnd_648180 : Nat := 221885260420919484312721

theorem tailTrace_648180 : CollatzResearch.WordTrace tailWord_648180 prefixEnd_648180 221885260420919484312721 := by
  unfold tailWord_648180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820533395881017587902997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15760711194508023450537329 11820533395881017587902997)
  ·
    refine ⟨554087502931922699432953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11820533395881017587902997 554087502931922699432953)
    ·
      refine ⟨415565627198942024574715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 554087502931922699432953 415565627198942024574715)
      ·
        refine ⟨623348440798413036862073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415565627198942024574715 623348440798413036862073)
        ·
          refine ⟨467511330598809777646555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623348440798413036862073 467511330598809777646555)
          ·
            refine ⟨701266995898214666469833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467511330598809777646555 701266995898214666469833)
            ·
              refine ⟨525950246923660999852375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701266995898214666469833 525950246923660999852375)
              ·
                refine ⟨788925370385491499778563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525950246923660999852375 788925370385491499778563)
                ·
                  refine ⟨1183388055578237249667845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788925370385491499778563 1183388055578237249667845)
                  ·
                    refine ⟨221885260420919484312721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183388055578237249667845 221885260420919484312721)
                    ·
                      rfl

theorem cell22_648180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_648180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648180 prefixEnd_648180 := by exact prefixLift 648180
  have htrace : WordTrace (prefixWord ++ tailWord_648180) baseStart_648180 baseEnd_648180 := by
    simpa [prefixWord, tailWord_648180, baseEnd_648180] using wordTrace_append hprefix tailTrace_648180
  have hstable : (prefixWord ++ tailWord_648180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648180).length < 2 ^ (prefixWord ++ tailWord_648180).sum := by decide
  have hdescent : baseEnd_648180 < baseStart_648180 := by decide
  rcases family_descends (prefixWord ++ tailWord_648180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648200 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_648200 : Nat := 118140960795 + 648200 * 2 ^ 59
def prefixEnd_648200 : Nat := 4983230072969 + 3 ^ 40 * 648200 * 2
def baseEnd_648200 : Nat := 73964035609882032937553

theorem tailTrace_648200 : CollatzResearch.WordTrace tailWord_648200 prefixEnd_648200 73964035609882032937553 := by
  unfold tailWord_648200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820898125844789295767027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15761197501126385727689369 11820898125844789295767027)
  ·
    refine ⟨17731347188767183943650541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11820898125844789295767027 17731347188767183943650541)
    ·
      refine ⟨6649255195787693978868953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17731347188767183943650541 6649255195787693978868953)
      ·
        refine ⟨4986941396840770484151715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649255195787693978868953 4986941396840770484151715)
        ·
          refine ⟨7480412095261155726227573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986941396840770484151715 7480412095261155726227573)
          ·
            refine ⟨701288633930733349333835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7480412095261155726227573 701288633930733349333835)
            ·
              refine ⟨1051932950896100024000753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701288633930733349333835 1051932950896100024000753)
              ·
                refine ⟨788949713172075018000565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051932950896100024000753 788949713172075018000565)
                ·
                  refine ⟨73964035609882032937553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788949713172075018000565 73964035609882032937553)
                  ·
                    rfl

theorem cell22_648200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_648200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648200 prefixEnd_648200 := by exact prefixLift 648200
  have htrace : WordTrace (prefixWord ++ tailWord_648200) baseStart_648200 baseEnd_648200 := by
    simpa [prefixWord, tailWord_648200, baseEnd_648200] using wordTrace_append hprefix tailTrace_648200
  have hstable : (prefixWord ++ tailWord_648200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648200).length < 2 ^ (prefixWord ++ tailWord_648200).sum := by decide
  have hdescent : baseEnd_648200 < baseStart_648200 := by decide
  rcases family_descends (prefixWord ++ tailWord_648200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648262 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_648262 : Nat := 118140960795 + 648262 * 2 ^ 59
def prefixEnd_648262 : Nat := 4983230072969 + 3 ^ 40 * 648262 * 2
def baseEnd_648262 : Nat := 73971110232232867920823

theorem tailTrace_648262 : CollatzResearch.WordTrace tailWord_648262 prefixEnd_648262 73971110232232867920823 := by
  unfold tailWord_648262
  simp only [CollatzResearch.WordTrace]
  refine ⟨738876799295780099384095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15762705051643308786860693 738876799295780099384095)
  ·
    refine ⟨1108315198943670149076143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738876799295780099384095 1108315198943670149076143)
    ·
      refine ⟨1662472798415505223614215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108315198943670149076143 1662472798415505223614215)
      ·
        refine ⟨2493709197623257835421323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662472798415505223614215 2493709197623257835421323)
        ·
          refine ⟨3740563796434886753131985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493709197623257835421323 3740563796434886753131985)
          ·
            refine ⟨2805422847326165064848989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3740563796434886753131985 2805422847326165064848989)
            ·
              refine ⟨1052033567747311899318371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2805422847326165064848989 1052033567747311899318371)
              ·
                refine ⟨1578050351620967848977557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052033567747311899318371 1578050351620967848977557)
                ·
                  refine ⟨73971110232232867920823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1578050351620967848977557 73971110232232867920823)
                  ·
                    rfl

theorem cell22_648262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_648262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648262 prefixEnd_648262 := by exact prefixLift 648262
  have htrace : WordTrace (prefixWord ++ tailWord_648262) baseStart_648262 baseEnd_648262 := by
    simpa [prefixWord, tailWord_648262, baseEnd_648262] using wordTrace_append hprefix tailTrace_648262
  have hstable : (prefixWord ++ tailWord_648262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648262).length < 2 ^ (prefixWord ++ tailWord_648262).sum := by decide
  have hdescent : baseEnd_648262 < baseStart_648262 := by decide
  rcases family_descends (prefixWord ++ tailWord_648262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648290 : List Nat := [3, 3, 2, 2, 1, 1, 2, 8]
def baseStart_648290 : Nat := 118140960795 + 648290 * 2 ^ 59
def prefixEnd_648290 : Nat := 4983230072969 + 3 ^ 40 * 648290 * 2
def baseEnd_648290 : Nat := 24658101740990651562487

theorem tailTrace_648290 : CollatzResearch.WordTrace tailWord_648290 prefixEnd_648290 24658101740990651562487 := by
  unfold tailWord_648290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911269705340880990577581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15763385880909015974873549 5911269705340880990577581)
  ·
    refine ⟨2216726139502830371466593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5911269705340880990577581 2216726139502830371466593)
    ·
      refine ⟨1662544604627122778599945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2216726139502830371466593 1662544604627122778599945)
      ·
        refine ⟨1246908453470342083949959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662544604627122778599945 1246908453470342083949959)
        ·
          refine ⟨1870362680205513125924939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246908453470342083949959 1870362680205513125924939)
          ·
            refine ⟨2805544020308269688887409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870362680205513125924939 2805544020308269688887409)
            ·
              refine ⟨2104158015231202266665557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805544020308269688887409 2104158015231202266665557)
              ·
                refine ⟨24658101740990651562487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2104158015231202266665557 24658101740990651562487)
                ·
                  rfl

theorem cell22_648290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_648290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648290 prefixEnd_648290 := by exact prefixLift 648290
  have htrace : WordTrace (prefixWord ++ tailWord_648290) baseStart_648290 baseEnd_648290 := by
    simpa [prefixWord, tailWord_648290, baseEnd_648290] using wordTrace_append hprefix tailTrace_648290
  have hstable : (prefixWord ++ tailWord_648290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648290).length < 2 ^ (prefixWord ++ tailWord_648290).sum := by decide
  have hdescent : baseEnd_648290 < baseStart_648290 := by decide
  rcases family_descends (prefixWord ++ tailWord_648290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648380 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_648380 : Nat := 118140960795 + 648380 * 2 ^ 59
def prefixEnd_648380 : Nat := 4983230072969 + 3 ^ 40 * 648380 * 2
def baseEnd_648380 : Nat := 73984574836061876437369

theorem tailTrace_648380 : CollatzResearch.WordTrace tailWord_648380 prefixEnd_648380 73984574836061876437369 := by
  unfold tailWord_648380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824180695518734666543297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15765574260691646222057729 11824180695518734666543297)
  ·
    refine ⟨8868135521639050999907473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11824180695518734666543297 8868135521639050999907473)
    ·
      refine ⟨6651101641229288249930605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8868135521639050999907473 6651101641229288249930605)
      ·
        refine ⟨2494163115460983093723977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6651101641229288249930605 2494163115460983093723977)
        ·
          refine ⟨1870622336595737320292983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494163115460983093723977 1870622336595737320292983)
          ·
            refine ⟨2805933504893605980439475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870622336595737320292983 2805933504893605980439475)
            ·
              refine ⟨4208900257340408970659213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805933504893605980439475 4208900257340408970659213)
              ·
                refine ⟨1578337596502653363997205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4208900257340408970659213 1578337596502653363997205)
                ·
                  refine ⟨73984574836061876437369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1578337596502653363997205 73984574836061876437369)
                  ·
                    rfl

theorem cell22_648380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_648380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648380 prefixEnd_648380 := by exact prefixLift 648380
  have htrace : WordTrace (prefixWord ++ tailWord_648380) baseStart_648380 baseEnd_648380 := by
    simpa [prefixWord, tailWord_648380, baseEnd_648380] using wordTrace_append hprefix tailTrace_648380
  have hstable : (prefixWord ++ tailWord_648380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648380).length < 2 ^ (prefixWord ++ tailWord_648380).sum := by decide
  have hdescent : baseEnd_648380 < baseStart_648380 := by decide
  rcases family_descends (prefixWord ++ tailWord_648380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648410 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_648410 : Nat := 118140960795 + 648410 * 2 ^ 59
def prefixEnd_648410 : Nat := 4983230072969 + 3 ^ 40 * 648410 * 2
def baseEnd_648410 : Nat := 221963994121275551062015

theorem tailTrace_648410 : CollatzResearch.WordTrace tailWord_648410 prefixEnd_648410 221963994121275551062015 := by
  unfold tailWord_648410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912363895232196114169671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15766303720619189637785789 5912363895232196114169671)
  ·
    refine ⟨8868545842848294171254507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912363895232196114169671 8868545842848294171254507)
    ·
      refine ⟨13302818764272441256881761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868545842848294171254507 13302818764272441256881761)
      ·
        refine ⟨9977114073204330942661321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13302818764272441256881761 9977114073204330942661321)
        ·
          refine ⟨7482835554903248206995991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9977114073204330942661321 7482835554903248206995991)
          ·
            refine ⟨11224253332354872310493987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482835554903248206995991 11224253332354872310493987)
            ·
              refine ⟨16836379998532308465740981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11224253332354872310493987 16836379998532308465740981)
              ·
                refine ⟨1578410624862403918663217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16836379998532308465740981 1578410624862403918663217)
                ·
                  refine ⟨1183807968646802938997413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578410624862403918663217 1183807968646802938997413)
                  ·
                    refine ⟨221963994121275551062015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183807968646802938997413 221963994121275551062015)
                    ·
                      rfl

theorem cell22_648410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_648410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648410 prefixEnd_648410 := by exact prefixLift 648410
  have htrace : WordTrace (prefixWord ++ tailWord_648410) baseStart_648410 baseEnd_648410 := by
    simpa [prefixWord, tailWord_648410, baseEnd_648410] using wordTrace_append hprefix tailTrace_648410
  have hstable : (prefixWord ++ tailWord_648410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648410).length < 2 ^ (prefixWord ++ tailWord_648410).sum := by decide
  have hdescent : baseEnd_648410 < baseStart_648410 := by decide
  rcases family_descends (prefixWord ++ tailWord_648410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648446 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_648446 : Nat := 118140960795 + 648446 * 2 ^ 59
def prefixEnd_648446 : Nat := 4983230072969 + 3 ^ 40 * 648446 * 2
def baseEnd_648446 : Nat := 221976317656983457161905

theorem tailTrace_648446 : CollatzResearch.WordTrace tailWord_648446 prefixEnd_648446 221976317656983457161905 := by
  unfold tailWord_648446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956346076099795325623649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15767179072532241736659461 2956346076099795325623649)
  ·
    refine ⟨2217259557074846494217737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2956346076099795325623649 2217259557074846494217737)
    ·
      refine ⟨1662944667806134870663303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2217259557074846494217737 1662944667806134870663303)
      ·
        refine ⟨2494417001709202305994955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662944667806134870663303 2494417001709202305994955)
        ·
          refine ⟨3741625502563803458992433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494417001709202305994955 3741625502563803458992433)
          ·
            refine ⟨2806219126922852594244325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741625502563803458992433 2806219126922852594244325)
            ·
              refine ⟨526166086298034861420811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2806219126922852594244325 526166086298034861420811)
              ·
                refine ⟨789249129447052292131217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526166086298034861420811 789249129447052292131217)
                ·
                  refine ⟨591936847085289219098413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789249129447052292131217 591936847085289219098413)
                  ·
                    refine ⟨221976317656983457161905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591936847085289219098413 221976317656983457161905)
                    ·
                      rfl

theorem cell22_648446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_648446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648446 prefixEnd_648446 := by exact prefixLift 648446
  have htrace : WordTrace (prefixWord ++ tailWord_648446) baseStart_648446 baseEnd_648446 := by
    simpa [prefixWord, tailWord_648446, baseEnd_648446] using wordTrace_append hprefix tailTrace_648446
  have hstable : (prefixWord ++ tailWord_648446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648446).length < 2 ^ (prefixWord ++ tailWord_648446).sum := by decide
  have hdescent : baseEnd_648446 < baseStart_648446 := by decide
  rcases family_descends (prefixWord ++ tailWord_648446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648525 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_648525 : Nat := 118140960795 + 648525 * 2 ^ 59
def prefixEnd_648525 : Nat := 4983230072969 + 3 ^ 40 * 648525 * 2
def baseEnd_648525 : Nat := 222003360971453584436663

theorem tailTrace_648525 : CollatzResearch.WordTrace tailWord_648525 prefixEnd_648525 222003360971453584436663 := by
  unfold tailWord_648525
  simp only [CollatzResearch.WordTrace]
  refine ⟨23653649975512159097115029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15769099983674772731410019 23653649975512159097115029)
  ·
    refine ⟨1108764842602132457677267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23653649975512159097115029 1108764842602132457677267)
    ·
      refine ⟨1663147263903198686515901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108764842602132457677267 1663147263903198686515901)
      ·
        refine ⟨623680223963699507443463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1663147263903198686515901 623680223963699507443463)
        ·
          refine ⟨935520335945549261165195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623680223963699507443463 935520335945549261165195)
          ·
            refine ⟨1403280503918323891747793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935520335945549261165195 1403280503918323891747793)
            ·
              refine ⟨1052460377938742918810845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403280503918323891747793 1052460377938742918810845)
              ·
                refine ⟨394672641727028594554067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1052460377938742918810845 394672641727028594554067)
                ·
                  refine ⟨592008962590542891831101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394672641727028594554067 592008962590542891831101)
                  ·
                    refine ⟨222003360971453584436663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592008962590542891831101 222003360971453584436663)
                    ·
                      rfl

theorem cell22_648525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_648525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648525 prefixEnd_648525 := by exact prefixLift 648525
  have htrace : WordTrace (prefixWord ++ tailWord_648525) baseStart_648525 baseEnd_648525 := by
    simpa [prefixWord, tailWord_648525, baseEnd_648525] using wordTrace_append hprefix tailTrace_648525
  have hstable : (prefixWord ++ tailWord_648525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648525).length < 2 ^ (prefixWord ++ tailWord_648525).sum := by decide
  have hdescent : baseEnd_648525 < baseStart_648525 := by decide
  rcases family_descends (prefixWord ++ tailWord_648525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648560 : List Nat := [2, 1, 1, 1, 4, 2, 2, 9]
def baseStart_648560 : Nat := 118140960795 + 648560 * 2 ^ 59
def prefixEnd_648560 : Nat := 4983230072969 + 3 ^ 40 * 648560 * 2
def baseEnd_648560 : Nat := 24668371354080573312395

theorem tailTrace_648560 : CollatzResearch.WordTrace tailWord_648560 prefixEnd_648560 24668371354080573312395 := by
  unfold tailWord_648560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827463265192680037319567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15769951020256906716426089 11827463265192680037319567)
  ·
    refine ⟨17741194897789020055979351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11827463265192680037319567 17741194897789020055979351)
    ·
      refine ⟨26611792346683530083969027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17741194897789020055979351 26611792346683530083969027)
      ·
        refine ⟨39917688520025295125953541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26611792346683530083969027 39917688520025295125953541)
        ·
          refine ⟨7484566597504742836116289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39917688520025295125953541 7484566597504742836116289)
          ·
            refine ⟨5613424948128557127087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7484566597504742836116289 5613424948128557127087217)
            ·
              refine ⟨4210068711096417845315413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613424948128557127087217 4210068711096417845315413)
              ·
                refine ⟨24668371354080573312395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4210068711096417845315413 24668371354080573312395)
                ·
                  rfl

theorem cell22_648560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_648560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648560 prefixEnd_648560 := by exact prefixLift 648560
  have htrace : WordTrace (prefixWord ++ tailWord_648560) baseStart_648560 baseEnd_648560 := by
    simpa [prefixWord, tailWord_648560, baseEnd_648560] using wordTrace_append hprefix tailTrace_648560
  have hstable : (prefixWord ++ tailWord_648560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648560).length < 2 ^ (prefixWord ++ tailWord_648560).sum := by decide
  have hdescent : baseEnd_648560 < baseStart_648560 := by decide
  rcases family_descends (prefixWord ++ tailWord_648560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648669 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_648669 : Nat := 118140960795 + 648669 * 2 ^ 59
def prefixEnd_648669 : Nat := 4983230072969 + 3 ^ 40 * 648669 * 2
def baseEnd_648669 : Nat := 222052655114285208836221

theorem tailTrace_648669 : CollatzResearch.WordTrace tailWord_648669 prefixEnd_648669 222052655114285208836221 := by
  unfold tailWord_648669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23658902086990471690357061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15772601391326981126904707 23658902086990471690357061)
  ·
    refine ⟨4436044141310713441941949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23658902086990471690357061 4436044141310713441941949)
    ·
      refine ⟨1663516552991517540728231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4436044141310713441941949 1663516552991517540728231)
      ·
        refine ⟨2495274829487276311092347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663516552991517540728231 2495274829487276311092347)
        ·
          refine ⟨3742912244230914466638521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495274829487276311092347 3742912244230914466638521)
          ·
            refine ⟨2807184183173185849978891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742912244230914466638521 2807184183173185849978891)
            ·
              refine ⟨4210776274759778774968337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807184183173185849978891 4210776274759778774968337)
              ·
                refine ⟨3158082206069834081226253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210776274759778774968337 3158082206069834081226253)
                ·
                  refine ⟨1184280827276187780459845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3158082206069834081226253 1184280827276187780459845)
                  ·
                    refine ⟨222052655114285208836221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184280827276187780459845 222052655114285208836221)
                    ·
                      rfl

theorem cell22_648669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_648669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648669 prefixEnd_648669 := by exact prefixLift 648669
  have htrace : WordTrace (prefixWord ++ tailWord_648669) baseStart_648669 baseEnd_648669 := by
    simpa [prefixWord, tailWord_648669, baseEnd_648669] using wordTrace_append hprefix tailTrace_648669
  have hstable : (prefixWord ++ tailWord_648669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648669).length < 2 ^ (prefixWord ++ tailWord_648669).sum := by decide
  have hdescent : baseEnd_648669 < baseStart_648669 := by decide
  rcases family_descends (prefixWord ++ tailWord_648669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648701 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 4]
def baseStart_648701 : Nat := 118140960795 + 648701 * 2 ^ 59
def prefixEnd_648701 : Nat := 4983230072969 + 3 ^ 40 * 648701 * 2
def baseEnd_648701 : Nat := 74021203122749264012041

theorem tailTrace_648701 : CollatzResearch.WordTrace tailWord_648701 prefixEnd_648701 74021203122749264012041 := by
  unfold tailWord_648701
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660069222874541155521957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15773379481916360770347971 23660069222874541155521957)
  ·
    refine ⟨4436262979288976466660367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23660069222874541155521957 4436262979288976466660367)
    ·
      refine ⟨6654394468933464699990551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436262979288976466660367 6654394468933464699990551)
      ·
        refine ⟨9981591703400197049985827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654394468933464699990551 9981591703400197049985827)
        ·
          refine ⟨14972387555100295574978741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981591703400197049985827 14972387555100295574978741)
          ·
            refine ⟨1403661333290652710154257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14972387555100295574978741 1403661333290652710154257)
            ·
              refine ⟨1052745999967989532615693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403661333290652710154257 1052745999967989532615693)
              ·
                refine ⟨394779749987996074730885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1052745999967989532615693 394779749987996074730885)
                ·
                  refine ⟨74021203122749264012041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 394779749987996074730885 74021203122749264012041)
                  ·
                    rfl

theorem cell22_648701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_648701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648701 prefixEnd_648701 := by exact prefixLift 648701
  have htrace : WordTrace (prefixWord ++ tailWord_648701) baseStart_648701 baseEnd_648701 := by
    simpa [prefixWord, tailWord_648701, baseEnd_648701] using wordTrace_append hprefix tailTrace_648701
  have hstable : (prefixWord ++ tailWord_648701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648701).length < 2 ^ (prefixWord ++ tailWord_648701).sum := by decide
  have hdescent : baseEnd_648701 < baseStart_648701 := by decide
  rcases family_descends (prefixWord ++ tailWord_648701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648716 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_648716 : Nat := 118140960795 + 648716 * 2 ^ 59
def prefixEnd_648716 : Nat := 4983230072969 + 3 ^ 40 * 648716 * 2
def baseEnd_648716 : Nat := 222068744174792752911077

theorem tailTrace_648716 : CollatzResearch.WordTrace tailWord_648716 prefixEnd_648716 222068744174792752911077 := by
  unfold tailWord_648716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830308158910099358659001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15773744211880132478212001 11830308158910099358659001)
  ·
    refine ⟨8872731119182574518994251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11830308158910099358659001 8872731119182574518994251)
    ·
      refine ⟨13309096678773861778491377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872731119182574518994251 13309096678773861778491377)
      ·
        refine ⟨9981822509080396333868533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309096678773861778491377 9981822509080396333868533)
        ·
          refine ⟨935795860226287156300175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9981822509080396333868533 935795860226287156300175)
          ·
            refine ⟨1403693790339430734450263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935795860226287156300175 1403693790339430734450263)
            ·
              refine ⟨2105540685509146101675395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403693790339430734450263 2105540685509146101675395)
              ·
                refine ⟨3158311028263719152513093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105540685509146101675395 3158311028263719152513093)
                ·
                  refine ⟨592183317799447341096205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3158311028263719152513093 592183317799447341096205)
                  ·
                    refine ⟨222068744174792752911077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592183317799447341096205 222068744174792752911077)
                    ·
                      rfl

theorem cell22_648716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_648716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648716 prefixEnd_648716 := by exact prefixLift 648716
  have htrace : WordTrace (prefixWord ++ tailWord_648716) baseStart_648716 baseEnd_648716 := by
    simpa [prefixWord, tailWord_648716, baseEnd_648716] using wordTrace_append hprefix tailTrace_648716
  have hstable : (prefixWord ++ tailWord_648716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648716).length < 2 ^ (prefixWord ++ tailWord_648716).sum := by decide
  have hdescent : baseEnd_648716 < baseStart_648716 := by decide
  rcases family_descends (prefixWord ++ tailWord_648716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648733 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_648733 : Nat := 118140960795 + 648733 * 2 ^ 59
def prefixEnd_648733 : Nat := 4983230072969 + 3 ^ 40 * 648733 * 2
def baseEnd_648733 : Nat := 222074563622210375236025

theorem tailTrace_648733 : CollatzResearch.WordTrace tailWord_648733 prefixEnd_648733 222074563622210375236025 := by
  unfold tailWord_648733
  simp only [CollatzResearch.WordTrace]
  refine ⟨23661236358758610620686853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15774157572505740413791235 23661236358758610620686853)
  ·
    refine ⟨4436481817267239491378785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23661236358758610620686853 4436481817267239491378785)
    ·
      refine ⟨3327361362950429618534089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4436481817267239491378785 3327361362950429618534089)
      ·
        refine ⟨2495521022212822213900567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3327361362950429618534089 2495521022212822213900567)
        ·
          refine ⟨3743281533319233320850851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495521022212822213900567 3743281533319233320850851)
          ·
            refine ⟨5614922299978849981276277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743281533319233320850851 5614922299978849981276277)
            ·
              refine ⟨526398965623017185744651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5614922299978849981276277 526398965623017185744651)
              ·
                refine ⟨789598448434525778616977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526398965623017185744651 789598448434525778616977)
                ·
                  refine ⟨592198836325894333962733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789598448434525778616977 592198836325894333962733)
                  ·
                    refine ⟨222074563622210375236025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592198836325894333962733 222074563622210375236025)
                    ·
                      rfl

theorem cell22_648733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_648733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648733 prefixEnd_648733 := by exact prefixLift 648733
  have htrace : WordTrace (prefixWord ++ tailWord_648733) baseStart_648733 baseEnd_648733 := by
    simpa [prefixWord, tailWord_648733, baseEnd_648733] using wordTrace_append hprefix tailTrace_648733
  have hstable : (prefixWord ++ tailWord_648733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648733).length < 2 ^ (prefixWord ++ tailWord_648733).sum := by decide
  have hdescent : baseEnd_648733 < baseStart_648733 := by decide
  rcases family_descends (prefixWord ++ tailWord_648733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648791 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 5]
def baseStart_648791 : Nat := 118140960795 + 648791 * 2 ^ 59
def prefixEnd_648791 : Nat := 4983230072969 + 3 ^ 40 * 648791 * 2
def baseEnd_648791 : Nat := 74031472735839185761949

theorem tailTrace_648791 : CollatzResearch.WordTrace tailWord_648791 prefixEnd_648791 74031472735839185761949 := by
  unfold tailWord_648791
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663351792548486526298227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15775567861698991017532151 23663351792548486526298227)
  ·
    refine ⟨35495027688822729789447341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23663351792548486526298227 35495027688822729789447341)
    ·
      refine ⟨13310635383308523671042753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35495027688822729789447341 13310635383308523671042753)
      ·
        refine ⟨9982976537481392753282065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13310635383308523671042753 9982976537481392753282065)
        ·
          refine ⟨7487232403111044564961549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9982976537481392753282065 7487232403111044564961549)
          ·
            refine ⟨2807712151166641711860581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7487232403111044564961549 2807712151166641711860581)
            ·
              refine ⟨526446028343745320973859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2807712151166641711860581 526446028343745320973859)
              ·
                refine ⟨789669042515617981460789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526446028343745320973859 789669042515617981460789)
                ·
                  refine ⟨74031472735839185761949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789669042515617981460789 74031472735839185761949)
                  ·
                    rfl

theorem cell22_648791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 5].length) (baseStart_648791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648791 prefixEnd_648791 := by exact prefixLift 648791
  have htrace : WordTrace (prefixWord ++ tailWord_648791) baseStart_648791 baseEnd_648791 := by
    simpa [prefixWord, tailWord_648791, baseEnd_648791] using wordTrace_append hprefix tailTrace_648791
  have hstable : (prefixWord ++ tailWord_648791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648791).length < 2 ^ (prefixWord ++ tailWord_648791).sum := by decide
  have hdescent : baseEnd_648791 < baseStart_648791 := by decide
  rcases family_descends (prefixWord ++ tailWord_648791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648872 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_648872 : Nat := 118140960795 + 648872 * 2 ^ 59
def prefixEnd_648872 : Nat := 4983230072969 + 3 ^ 40 * 648872 * 2
def baseEnd_648872 : Nat := 222122146162860346010599

theorem tailTrace_648872 : CollatzResearch.WordTrace tailWord_648872 prefixEnd_648872 222122146162860346010599 := by
  unfold tailWord_648872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833153052627518679998435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15777537403503358239997913 11833153052627518679998435)
  ·
    refine ⟨17749729578941278019997653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11833153052627518679998435 17749729578941278019997653)
    ·
      refine ⟨416009287006436203593695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17749729578941278019997653 416009287006436203593695)
      ·
        refine ⟨624013930509654305390543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416009287006436203593695 624013930509654305390543)
        ·
          refine ⟨936020895764481458085815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624013930509654305390543 936020895764481458085815)
          ·
            refine ⟨1404031343646722187128723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936020895764481458085815 1404031343646722187128723)
            ·
              refine ⟨2106047015470083280693085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404031343646722187128723 2106047015470083280693085)
              ·
                refine ⟨789767630801281230259907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2106047015470083280693085 789767630801281230259907)
                ·
                  refine ⟨1184651446201921845389861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789767630801281230259907 1184651446201921845389861)
                  ·
                    refine ⟨222122146162860346010599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184651446201921845389861 222122146162860346010599)
                    ·
                      rfl

theorem cell22_648872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_648872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648872 prefixEnd_648872 := by exact prefixLift 648872
  have htrace : WordTrace (prefixWord ++ tailWord_648872) baseStart_648872 baseEnd_648872 := by
    simpa [prefixWord, tailWord_648872, baseEnd_648872] using wordTrace_append hprefix tailTrace_648872
  have hstable : (prefixWord ++ tailWord_648872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648872).length < 2 ^ (prefixWord ++ tailWord_648872).sum := by decide
  have hdescent : baseEnd_648872 < baseStart_648872 := by decide
  rcases family_descends (prefixWord ++ tailWord_648872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648902 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_648902 : Nat := 118140960795 + 648902 * 2 ^ 59
def prefixEnd_648902 : Nat := 4983230072969 + 3 ^ 40 * 648902 * 2
def baseEnd_648902 : Nat := 222132415775950267760507

theorem tailTrace_648902 : CollatzResearch.WordTrace tailWord_648902 prefixEnd_648902 222132415775950267760507 := by
  unfold tailWord_648902
  simp only [CollatzResearch.WordTrace]
  refine ⟨739606259223323515112155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15778266863430901655725973 739606259223323515112155)
  ·
    refine ⟨1109409388834985272668233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739606259223323515112155 1109409388834985272668233)
    ·
      refine ⟨832057041626238954501175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109409388834985272668233 832057041626238954501175)
      ·
        refine ⟨1248085562439358431751763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832057041626238954501175 1248085562439358431751763)
        ·
          refine ⟨1872128343659037647627645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248085562439358431751763 1872128343659037647627645)
          ·
            refine ⟨702048128872139117860367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872128343659037647627645 702048128872139117860367)
            ·
              refine ⟨1053072193308208676790551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702048128872139117860367 1053072193308208676790551)
              ·
                refine ⟨1579608289962313015185827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053072193308208676790551 1579608289962313015185827)
                ·
                  refine ⟨2369412434943469522778741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579608289962313015185827 2369412434943469522778741)
                  ·
                    refine ⟨222132415775950267760507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2369412434943469522778741 222132415775950267760507)
                    ·
                      rfl

theorem cell22_648902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_648902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648902 prefixEnd_648902 := by exact prefixLift 648902
  have htrace : WordTrace (prefixWord ++ tailWord_648902) baseStart_648902 baseEnd_648902 := by
    simpa [prefixWord, tailWord_648902, baseEnd_648902] using wordTrace_append hprefix tailTrace_648902
  have hstable : (prefixWord ++ tailWord_648902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648902).length < 2 ^ (prefixWord ++ tailWord_648902).sum := by decide
  have hdescent : baseEnd_648902 < baseStart_648902 := by decide
  rcases family_descends (prefixWord ++ tailWord_648902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648956 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_648956 : Nat := 118140960795 + 648956 * 2 ^ 59
def prefixEnd_648956 : Nat := 4983230072969 + 3 ^ 40 * 648956 * 2
def baseEnd_648956 : Nat := 222150901079512126910341

theorem tailTrace_648956 : CollatzResearch.WordTrace tailWord_648956 prefixEnd_648956 222150901079512126910341 := by
  unfold tailWord_648956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834684918475359853027361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15779579891300479804036481 11834684918475359853027361)
  ·
    refine ⟨8876013688856519889770521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11834684918475359853027361 8876013688856519889770521)
    ·
      refine ⟨6657010266642389917327891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8876013688856519889770521 6657010266642389917327891)
      ·
        refine ⟨9985515399963584875991837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6657010266642389917327891 9985515399963584875991837)
        ·
          refine ⟨3744568274986344328496939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9985515399963584875991837 3744568274986344328496939)
          ·
            refine ⟨5616852412479516492745409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744568274986344328496939 5616852412479516492745409)
            ·
              refine ⟨4212639309359637369559057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616852412479516492745409 4212639309359637369559057)
              ·
                refine ⟨3159479482019728027169293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212639309359637369559057 3159479482019728027169293)
                ·
                  refine ⟨1184804805757398010188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3159479482019728027169293 1184804805757398010188485)
                  ·
                    refine ⟨222150901079512126910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184804805757398010188485 222150901079512126910341)
                    ·
                      rfl

theorem cell22_648956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_648956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648956 prefixEnd_648956 := by exact prefixLift 648956
  have htrace : WordTrace (prefixWord ++ tailWord_648956) baseStart_648956 baseEnd_648956 := by
    simpa [prefixWord, tailWord_648956, baseEnd_648956] using wordTrace_append hprefix tailTrace_648956
  have hstable : (prefixWord ++ tailWord_648956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648956).length < 2 ^ (prefixWord ++ tailWord_648956).sum := by decide
  have hdescent : baseEnd_648956 < baseStart_648956 := by decide
  rcases family_descends (prefixWord ++ tailWord_648956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648986 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_648986 : Nat := 118140960795 + 648986 * 2 ^ 59
def prefixEnd_648986 : Nat := 4983230072969 + 3 ^ 40 * 648986 * 2
def baseEnd_648986 : Nat := 222161170692602048660249

theorem tailTrace_648986 : CollatzResearch.WordTrace tailWord_648986 prefixEnd_648986 222161170692602048660249 := by
  unfold tailWord_648986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5917616006710508707411703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15780309351228023219764541 5917616006710508707411703)
  ·
    refine ⟨8876424010065763061117555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5917616006710508707411703 8876424010065763061117555)
    ·
      refine ⟨13314636015098644591676333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8876424010065763061117555 13314636015098644591676333)
      ·
        refine ⟨4992988505661991721878625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13314636015098644591676333 4992988505661991721878625)
        ·
          refine ⟨3744741379246493791408969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4992988505661991721878625 3744741379246493791408969)
          ·
            refine ⟨2808556034434870343556727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3744741379246493791408969 2808556034434870343556727)
            ·
              refine ⟨4212834051652305515335091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808556034434870343556727 4212834051652305515335091)
              ·
                refine ⟨6319251077478458273002637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212834051652305515335091 6319251077478458273002637)
                ·
                  refine ⟨2369719154054421852375989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6319251077478458273002637 2369719154054421852375989)
                  ·
                    refine ⟨222161170692602048660249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2369719154054421852375989 222161170692602048660249)
                    ·
                      rfl

theorem cell22_648986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_648986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648986 prefixEnd_648986 := by exact prefixLift 648986
  have htrace : WordTrace (prefixWord ++ tailWord_648986) baseStart_648986 baseEnd_648986 := by
    simpa [prefixWord, tailWord_648986, baseEnd_648986] using wordTrace_append hprefix tailTrace_648986
  have hstable : (prefixWord ++ tailWord_648986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648986).length < 2 ^ (prefixWord ++ tailWord_648986).sum := by decide
  have hdescent : baseEnd_648986 < baseStart_648986 := by decide
  rcases family_descends (prefixWord ++ tailWord_648986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648988 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_648988 : Nat := 118140960795 + 648988 * 2 ^ 59
def prefixEnd_648988 : Nat := 4983230072969 + 3 ^ 40 * 648988 * 2
def baseEnd_648988 : Nat := 74053951777824903370081

theorem tailTrace_648988 : CollatzResearch.WordTrace tailWord_648988 prefixEnd_648988 74053951777824903370081 := by
  unfold tailWord_648988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835268486417394585609809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15780357981889859447479745 11835268486417394585609809)
  ·
    refine ⟨8876451364813045939207357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11835268486417394585609809 8876451364813045939207357)
    ·
      refine ⟨3328669261804892227202759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8876451364813045939207357 3328669261804892227202759)
      ·
        refine ⟨4993003892707338340804139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328669261804892227202759 4993003892707338340804139)
        ·
          refine ⟨7489505839061007511206209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993003892707338340804139 7489505839061007511206209)
          ·
            refine ⟨5617129379295755633404657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489505839061007511206209 5617129379295755633404657)
            ·
              refine ⟨4212847034471816725053493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617129379295755633404657 4212847034471816725053493)
              ·
                refine ⟨394954409481732817973765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4212847034471816725053493 394954409481732817973765)
                ·
                  refine ⟨74053951777824903370081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 394954409481732817973765 74053951777824903370081)
                  ·
                    rfl

theorem cell22_648988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_648988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648988 prefixEnd_648988 := by exact prefixLift 648988
  have htrace : WordTrace (prefixWord ++ tailWord_648988) baseStart_648988 baseEnd_648988 := by
    simpa [prefixWord, tailWord_648988, baseEnd_648988] using wordTrace_append hprefix tailTrace_648988
  have hstable : (prefixWord ++ tailWord_648988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648988).length < 2 ^ (prefixWord ++ tailWord_648988).sum := by decide
  have hdescent : baseEnd_648988 < baseStart_648988 := by decide
  rcases family_descends (prefixWord ++ tailWord_648988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648999 : List Nat := [1, 1, 20]
def baseStart_648999 : Nat := 118140960795 + 648999 * 2 ^ 59
def prefixEnd_648999 : Nat := 4983230072969 + 3 ^ 40 * 648999 * 2
def baseEnd_648999 : Nat := 101584646025731297707

theorem tailTrace_648999 : CollatzResearch.WordTrace tailWord_648999 prefixEnd_648999 101584646025731297707 := by
  unfold tailWord_648999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670938175794938049870051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15780625450529958699913367 23670938175794938049870051)
  ·
    refine ⟨35506407263692407074805077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23670938175794938049870051 35506407263692407074805077)
    ·
      refine ⟨101584646025731297707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 20 35506407263692407074805077 101584646025731297707)
      ·
        rfl

theorem cell22_648999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 20].length) (baseStart_648999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_648999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_648999 prefixEnd_648999 := by exact prefixLift 648999
  have htrace : WordTrace (prefixWord ++ tailWord_648999) baseStart_648999 baseEnd_648999 := by
    simpa [prefixWord, tailWord_648999, baseEnd_648999] using wordTrace_append hprefix tailTrace_648999
  have hstable : (prefixWord ++ tailWord_648999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648999).length < 2 ^ (prefixWord ++ tailWord_648999).sum := by decide
  have hdescent : baseEnd_648999 < baseStart_648999 := by decide
  rcases family_descends (prefixWord ++ tailWord_648999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649016 : List Nat := [2, 1, 2, 1, 3, 3, 3, 7]
def baseStart_649016 : Nat := 118140960795 + 649016 * 2 ^ 59
def prefixEnd_649016 : Nat := 4983230072969 + 3 ^ 40 * 649016 * 2
def baseEnd_649016 : Nat := 24685715589521330045573

theorem tailTrace_649016 : CollatzResearch.WordTrace tailWord_649016 prefixEnd_649016 24685715589521330045573 := by
  unfold tailWord_649016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835779108366674976619451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15781038811155566635492601 11835779108366674976619451)
  ·
    refine ⟨17753668662550012464929177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11835779108366674976619451 17753668662550012464929177)
    ·
      refine ⟨13315251496912509348696883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17753668662550012464929177 13315251496912509348696883)
      ·
        refine ⟨19972877245368764023045325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13315251496912509348696883 19972877245368764023045325)
        ·
          refine ⟨7489828967013286508641997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19972877245368764023045325 7489828967013286508641997)
          ·
            refine ⟨2808685862629982440740749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7489828967013286508641997 2808685862629982440740749)
            ·
              refine ⟨1053257198486243415277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2808685862629982440740749 1053257198486243415277781)
              ·
                refine ⟨24685715589521330045573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1053257198486243415277781 24685715589521330045573)
                ·
                  rfl

theorem cell22_649016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_649016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649016 prefixEnd_649016 := by exact prefixLift 649016
  have htrace : WordTrace (prefixWord ++ tailWord_649016) baseStart_649016 baseEnd_649016 := by
    simpa [prefixWord, tailWord_649016, baseEnd_649016] using wordTrace_append hprefix tailTrace_649016
  have hstable : (prefixWord ++ tailWord_649016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649016).length < 2 ^ (prefixWord ++ tailWord_649016).sum := by decide
  have hdescent : baseEnd_649016 < baseStart_649016 := by decide
  rcases family_descends (prefixWord ++ tailWord_649016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649151 : List Nat := [1, 1, 2, 2, 2, 1, 3, 10]
def baseStart_649151 : Nat := 118140960795 + 649151 * 2 ^ 59
def prefixEnd_649151 : Nat := 4983230072969 + 3 ^ 40 * 649151 * 2
def baseEnd_649151 : Nat := 24690850396066290920527

theorem tailTrace_649151 : CollatzResearch.WordTrace tailWord_649151 prefixEnd_649151 24690850396066290920527 := by
  unfold tailWord_649151
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676482071244268009403307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15784321380829512006268871 23676482071244268009403307)
  ·
    refine ⟨35514723106866402014104961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23676482071244268009403307 35514723106866402014104961)
    ·
      refine ⟨26636042330149801510578721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35514723106866402014104961 26636042330149801510578721)
      ·
        refine ⟨19977031747612351132934041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26636042330149801510578721 19977031747612351132934041)
        ·
          refine ⟨14982773810709263349700531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19977031747612351132934041 14982773810709263349700531)
          ·
            refine ⟨22474160716063895024550797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982773810709263349700531 22474160716063895024550797)
            ·
              refine ⟨8427810268523960634206549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22474160716063895024550797 8427810268523960634206549)
              ·
                refine ⟨24690850396066290920527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8427810268523960634206549 24690850396066290920527)
                ·
                  rfl

theorem cell22_649151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 10].length) (baseStart_649151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649151 prefixEnd_649151 := by exact prefixLift 649151
  have htrace : WordTrace (prefixWord ++ tailWord_649151) baseStart_649151 baseEnd_649151 := by
    simpa [prefixWord, tailWord_649151, baseEnd_649151] using wordTrace_append hprefix tailTrace_649151
  have hstable : (prefixWord ++ tailWord_649151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649151).length < 2 ^ (prefixWord ++ tailWord_649151).sum := by decide
  have hdescent : baseEnd_649151 < baseStart_649151 := by decide
  rcases family_descends (prefixWord ++ tailWord_649151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649172 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_649172 : Nat := 118140960795 + 649172 * 2 ^ 59
def prefixEnd_649172 : Nat := 4983230072969 + 3 ^ 40 * 649172 * 2
def baseEnd_649172 : Nat := 222224842293759563509679

theorem tailTrace_649172 : CollatzResearch.WordTrace tailWord_649172 prefixEnd_649172 222224842293759563509679 := by
  unfold tailWord_649172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11838624002084094297958885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15784832002778792397278513 11838624002084094297958885)
  ·
    refine ⟨2219742000390767680867291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11838624002084094297958885 2219742000390767680867291)
    ·
      refine ⟨3329613000586151521300937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219742000390767680867291 3329613000586151521300937)
      ·
        refine ⟨2497209750439613640975703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329613000586151521300937 2497209750439613640975703)
        ·
          refine ⟨3745814625659420461463555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497209750439613640975703 3745814625659420461463555)
          ·
            refine ⟨5618721938489130692195333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745814625659420461463555 5618721938489130692195333)
            ·
              refine ⟨1053510363466712004786625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5618721938489130692195333 1053510363466712004786625)
              ·
                refine ⟨790132772600034003589969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053510363466712004786625 790132772600034003589969)
                ·
                  refine ⟨592599579450025502692477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 790132772600034003589969 592599579450025502692477)
                  ·
                    refine ⟨222224842293759563509679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592599579450025502692477 222224842293759563509679)
                    ·
                      rfl

theorem cell22_649172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_649172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649172 prefixEnd_649172 := by exact prefixLift 649172
  have htrace : WordTrace (prefixWord ++ tailWord_649172) baseStart_649172 baseEnd_649172 := by
    simpa [prefixWord, tailWord_649172, baseEnd_649172] using wordTrace_append hprefix tailTrace_649172
  have hstable : (prefixWord ++ tailWord_649172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649172).length < 2 ^ (prefixWord ++ tailWord_649172).sum := by decide
  have hdescent : baseEnd_649172 < baseStart_649172 := by decide
  rcases family_descends (prefixWord ++ tailWord_649172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649174 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_649174 : Nat := 118140960795 + 649174 * 2 ^ 59
def prefixEnd_649174 : Nat := 4983230072969 + 3 ^ 40 * 649174 * 2
def baseEnd_649174 : Nat := 74075175644877408319891

theorem tailTrace_649174 : CollatzResearch.WordTrace tailWord_649174 prefixEnd_649174 74075175644877408319891 := by
  unfold tailWord_649174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479832559385058933593161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15784880633440628624993717 1479832559385058933593161)
  ·
    refine ⟨1109874419538794200194871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1479832559385058933593161 1109874419538794200194871)
    ·
      refine ⟨1664811629308191300292307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109874419538794200194871 1664811629308191300292307)
      ·
        refine ⟨2497217443962286950438461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664811629308191300292307 2497217443962286950438461)
        ·
          refine ⟨936456541485857606414423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497217443962286950438461 936456541485857606414423)
          ·
            refine ⟨1404684812228786409621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936456541485857606414423 1404684812228786409621635)
            ·
              refine ⟨2107027218343179614432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404684812228786409621635 2107027218343179614432453)
              ·
                refine ⟨395067603439346177706085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2107027218343179614432453 395067603439346177706085)
                ·
                  refine ⟨74075175644877408319891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395067603439346177706085 74075175644877408319891)
                  ·
                    rfl

theorem cell22_649174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_649174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649174 prefixEnd_649174 := by exact prefixLift 649174
  have htrace : WordTrace (prefixWord ++ tailWord_649174) baseStart_649174 baseEnd_649174 := by
    simpa [prefixWord, tailWord_649174, baseEnd_649174] using wordTrace_append hprefix tailTrace_649174
  have hstable : (prefixWord ++ tailWord_649174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649174).length < 2 ^ (prefixWord ++ tailWord_649174).sum := by decide
  have hdescent : baseEnd_649174 < baseStart_649174 := by decide
  rcases family_descends (prefixWord ++ tailWord_649174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649228 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_649228 : Nat := 118140960795 + 649228 * 2 ^ 59
def prefixEnd_649228 : Nat := 4983230072969 + 3 ^ 40 * 649228 * 2
def baseEnd_649228 : Nat := 222244012238194084109507

theorem tailTrace_649228 : CollatzResearch.WordTrace tailWord_649228 prefixEnd_649228 222244012238194084109507 := by
  unfold tailWord_649228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11839645245982655079978169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15786193661310206773304225 11839645245982655079978169)
  ·
    refine ⟨8879733934486991309983627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11839645245982655079978169 8879733934486991309983627)
    ·
      refine ⟨13319600901730486964975441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8879733934486991309983627 13319600901730486964975441)
      ·
        refine ⟨9989700676297865223731581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13319600901730486964975441 9989700676297865223731581)
        ·
          refine ⟨3746137753611699458899343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9989700676297865223731581 3746137753611699458899343)
          ·
            refine ⟨5619206630417549188349015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746137753611699458899343 5619206630417549188349015)
            ·
              refine ⟨8428809945626323782523523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619206630417549188349015 8428809945626323782523523)
              ·
                refine ⟨12643214918439485673785285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8428809945626323782523523 12643214918439485673785285)
                ·
                  refine ⟨2370602797207403563834741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12643214918439485673785285 2370602797207403563834741)
                  ·
                    refine ⟨222244012238194084109507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2370602797207403563834741 222244012238194084109507)
                    ·
                      rfl

theorem cell22_649228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_649228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649228 prefixEnd_649228 := by exact prefixLift 649228
  have htrace : WordTrace (prefixWord ++ tailWord_649228) baseStart_649228 baseEnd_649228 := by
    simpa [prefixWord, tailWord_649228, baseEnd_649228] using wordTrace_append hprefix tailTrace_649228
  have hstable : (prefixWord ++ tailWord_649228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649228).length < 2 ^ (prefixWord ++ tailWord_649228).sum := by decide
  have hdescent : baseEnd_649228 < baseStart_649228 := by decide
  rcases family_descends (prefixWord ++ tailWord_649228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649243 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_649243 : Nat := 118140960795 + 649243 * 2 ^ 59
def prefixEnd_649243 : Nat := 4983230072969 + 3 ^ 40 * 649243 * 2
def baseEnd_649243 : Nat := 222249147044739044984461

theorem tailTrace_649243 : CollatzResearch.WordTrace tailWord_649243 prefixEnd_649243 222249147044739044984461 := by
  unfold tailWord_649243
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679837586910967721752383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786558391273978481168255 23679837586910967721752383)
  ·
    refine ⟨35519756380366451582628575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679837586910967721752383 35519756380366451582628575)
    ·
      refine ⟨53279634570549677373942863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35519756380366451582628575 53279634570549677373942863)
      ·
        refine ⟨79919451855824516060914295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53279634570549677373942863 79919451855824516060914295)
        ·
          refine ⟨119879177783736774091371443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79919451855824516060914295 119879177783736774091371443)
          ·
            refine ⟨179818766675605161137057165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119879177783736774091371443 179818766675605161137057165)
            ·
              refine ⟨67432037503351935426396437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179818766675605161137057165 67432037503351935426396437)
              ·
                refine ⟨3160876757969621973112333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67432037503351935426396437 3160876757969621973112333)
                ·
                  refine ⟨1185328784238608239917125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3160876757969621973112333 1185328784238608239917125)
                  ·
                    refine ⟨222249147044739044984461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1185328784238608239917125 222249147044739044984461)
                    ·
                      rfl

theorem cell22_649243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_649243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649243 prefixEnd_649243 := by exact prefixLift 649243
  have htrace : WordTrace (prefixWord ++ tailWord_649243) baseStart_649243 baseEnd_649243 := by
    simpa [prefixWord, tailWord_649243, baseEnd_649243] using wordTrace_append hprefix tailTrace_649243
  have hstable : (prefixWord ++ tailWord_649243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649243).length < 2 ^ (prefixWord ++ tailWord_649243).sum := by decide
  have hdescent : baseEnd_649243 < baseStart_649243 := by decide
  rcases family_descends (prefixWord ++ tailWord_649243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649245 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_649245 : Nat := 118140960795 + 649245 * 2 ^ 59
def prefixEnd_649245 : Nat := 4983230072969 + 3 ^ 40 * 649245 * 2
def baseEnd_649245 : Nat := 222249831685611706434455

theorem tailTrace_649245 : CollatzResearch.WordTrace tailWord_649245 prefixEnd_649245 222249831685611706434455 := by
  unfold tailWord_649245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679910532903722063325189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15786607021935814708883459 23679910532903722063325189)
  ·
    refine ⟨4439983224919447886873473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23679910532903722063325189 4439983224919447886873473)
    ·
      refine ⟨3329987418689585915155105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4439983224919447886873473 3329987418689585915155105)
      ·
        refine ⟨2497490564017189436366329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329987418689585915155105 2497490564017189436366329)
        ·
          refine ⟨1873117923012892077274747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2497490564017189436366329 1873117923012892077274747)
          ·
            refine ⟨2809676884519338115912121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873117923012892077274747 2809676884519338115912121)
            ·
              refine ⟨2107257663389503586934091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809676884519338115912121 2107257663389503586934091)
              ·
                refine ⟨3160886495084255380401137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107257663389503586934091 3160886495084255380401137)
                ·
                  refine ⟨2370664871313191535300853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3160886495084255380401137 2370664871313191535300853)
                  ·
                    refine ⟨222249831685611706434455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2370664871313191535300853 222249831685611706434455)
                    ·
                      rfl

theorem cell22_649245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_649245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649245 prefixEnd_649245 := by exact prefixLift 649245
  have htrace : WordTrace (prefixWord ++ tailWord_649245) baseStart_649245 baseEnd_649245 := by
    simpa [prefixWord, tailWord_649245, baseEnd_649245] using wordTrace_append hprefix tailTrace_649245
  have hstable : (prefixWord ++ tailWord_649245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649245).length < 2 ^ (prefixWord ++ tailWord_649245).sum := by decide
  have hdescent : baseEnd_649245 < baseStart_649245 := by decide
  rcases family_descends (prefixWord ++ tailWord_649245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649268 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_649268 : Nat := 118140960795 + 649268 * 2 ^ 59
def prefixEnd_649268 : Nat := 4983230072969 + 3 ^ 40 * 649268 * 2
def baseEnd_649268 : Nat := 222257705055647313109385

theorem tailTrace_649268 : CollatzResearch.WordTrace tailWord_649268 prefixEnd_649268 222257705055647313109385 := by
  unfold tailWord_649268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11840374705910198495706229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15787166274546931327608305 11840374705910198495706229)
  ·
    refine ⟨1110035128679081108972459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11840374705910198495706229 1110035128679081108972459)
    ·
      refine ⟨1665052693018621663458689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110035128679081108972459 1665052693018621663458689)
      ·
        refine ⟨1248789519763966247594017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665052693018621663458689 1248789519763966247594017)
        ·
          refine ⟨936592139822974685695513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248789519763966247594017 936592139822974685695513)
          ·
            refine ⟨702444104867231014271635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936592139822974685695513 702444104867231014271635)
            ·
              refine ⟨1053666157300846521407453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702444104867231014271635 1053666157300846521407453)
              ·
                refine ⟨395124808987817445527795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053666157300846521407453 395124808987817445527795)
                ·
                  refine ⟨592687213481726168291693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395124808987817445527795 592687213481726168291693)
                  ·
                    refine ⟨222257705055647313109385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592687213481726168291693 222257705055647313109385)
                    ·
                      rfl

theorem cell22_649268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_649268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649268 prefixEnd_649268 := by exact prefixLift 649268
  have htrace : WordTrace (prefixWord ++ tailWord_649268) baseStart_649268 baseEnd_649268 := by
    simpa [prefixWord, tailWord_649268, baseEnd_649268] using wordTrace_append hprefix tailTrace_649268
  have hstable : (prefixWord ++ tailWord_649268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649268).length < 2 ^ (prefixWord ++ tailWord_649268).sum := by decide
  have hdescent : baseEnd_649268 < baseStart_649268 := by decide
  rcases family_descends (prefixWord ++ tailWord_649268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649288 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_649288 : Nat := 118140960795 + 649288 * 2 ^ 59
def prefixEnd_649288 : Nat := 4983230072969 + 3 ^ 40 * 649288 * 2
def baseEnd_649288 : Nat := 222264551464373927609323

theorem tailTrace_649288 : CollatzResearch.WordTrace tailWord_649288 prefixEnd_649288 222264551464373927609323 := by
  unfold tailWord_649288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11840739435873970203570259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15787652581165293604760345 11840739435873970203570259)
  ·
    refine ⟨17761109153810955305355389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11840739435873970203570259 17761109153810955305355389)
    ·
      refine ⟨6660415932679108239508271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17761109153810955305355389 6660415932679108239508271)
      ·
        refine ⟨9990623899018662359262407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660415932679108239508271 9990623899018662359262407)
        ·
          refine ⟨14985935848527993538893611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990623899018662359262407 14985935848527993538893611)
          ·
            refine ⟨22478903772791990308340417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14985935848527993538893611 22478903772791990308340417)
            ·
              refine ⟨16859177829593992731255313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22478903772791990308340417 16859177829593992731255313)
              ·
                refine ⟨12644383372195494548441485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16859177829593992731255313 12644383372195494548441485)
                ·
                  refine ⟨4741643764573310455665557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12644383372195494548441485 4741643764573310455665557)
                  ·
                    refine ⟨222264551464373927609323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4741643764573310455665557 222264551464373927609323)
                    ·
                      rfl

theorem cell22_649288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_649288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649288 prefixEnd_649288 := by exact prefixLift 649288
  have htrace : WordTrace (prefixWord ++ tailWord_649288) baseStart_649288 baseEnd_649288 := by
    simpa [prefixWord, tailWord_649288, baseEnd_649288] using wordTrace_append hprefix tailTrace_649288
  have hstable : (prefixWord ++ tailWord_649288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649288).length < 2 ^ (prefixWord ++ tailWord_649288).sum := by decide
  have hdescent : baseEnd_649288 < baseStart_649288 := by decide
  rcases family_descends (prefixWord ++ tailWord_649288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649303 : List Nat := [1, 1, 3, 2, 2, 1, 3, 9]
def baseStart_649303 : Nat := 118140960795 + 649303 * 2 ^ 59
def prefixEnd_649303 : Nat := 4983230072969 + 3 ^ 40 * 649303 * 2
def baseEnd_649303 : Nat := 24696631807879876498253

theorem tailTrace_649303 : CollatzResearch.WordTrace tailWord_649303 prefixEnd_649303 24696631807879876498253 := by
  unfold tailWord_649303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23682025966693597968936563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15788017311129065312624375 23682025966693597968936563)
  ·
    refine ⟨35523038950040396953404845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23682025966693597968936563 35523038950040396953404845)
    ·
      refine ⟨13321139606265148857526817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35523038950040396953404845 13321139606265148857526817)
      ·
        refine ⟨9990854704698861643145113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13321139606265148857526817 9990854704698861643145113)
        ·
          refine ⟨7493141028524146232358835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9990854704698861643145113 7493141028524146232358835)
          ·
            refine ⟨11239711542786219348538253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493141028524146232358835 11239711542786219348538253)
            ·
              refine ⟨4214891828544832255701845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11239711542786219348538253 4214891828544832255701845)
              ·
                refine ⟨24696631807879876498253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4214891828544832255701845 24696631807879876498253)
                ·
                  rfl

theorem cell22_649303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 9].length) (baseStart_649303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649303 prefixEnd_649303 := by exact prefixLift 649303
  have htrace : WordTrace (prefixWord ++ tailWord_649303) baseStart_649303 baseEnd_649303 := by
    simpa [prefixWord, tailWord_649303, baseEnd_649303] using wordTrace_append hprefix tailTrace_649303
  have hstable : (prefixWord ++ tailWord_649303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649303).length < 2 ^ (prefixWord ++ tailWord_649303).sum := by decide
  have hdescent : baseEnd_649303 < baseStart_649303 := by decide
  rcases family_descends (prefixWord ++ tailWord_649303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649365 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 5]
def baseStart_649365 : Nat := 118140960795 + 649365 * 2 ^ 59
def prefixEnd_649365 : Nat := 4983230072969 + 3 ^ 40 * 649365 * 2
def baseEnd_649365 : Nat := 74096970045990464478029

theorem tailTrace_649365 : CollatzResearch.WordTrace tailWord_649365 prefixEnd_649365 74096970045990464478029 := by
  unfold tailWord_649365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684287292468982557693549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789524861645988371795699 23684287292468982557693549)
  ·
    refine ⟨8881607734675868459135081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23684287292468982557693549 8881607734675868459135081)
    ·
      refine ⟨6661205801006901344351311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8881607734675868459135081 6661205801006901344351311)
      ·
        refine ⟨9991808701510352016526967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661205801006901344351311 9991808701510352016526967)
        ·
          refine ⟨14987713052265528024790451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991808701510352016526967 14987713052265528024790451)
          ·
            refine ⟨22481569578398292037185677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14987713052265528024790451 22481569578398292037185677)
            ·
              refine ⟨8430588591899359513944629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22481569578398292037185677 8430588591899359513944629)
              ·
                refine ⟨790367680490564954432309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8430588591899359513944629 790367680490564954432309)
                ·
                  refine ⟨74096970045990464478029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790367680490564954432309 74096970045990464478029)
                  ·
                    rfl

theorem cell22_649365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_649365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649365 prefixEnd_649365 := by exact prefixLift 649365
  have htrace : WordTrace (prefixWord ++ tailWord_649365) baseStart_649365 baseEnd_649365 := by
    simpa [prefixWord, tailWord_649365, baseEnd_649365] using wordTrace_append hprefix tailTrace_649365
  have hstable : (prefixWord ++ tailWord_649365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649365).length < 2 ^ (prefixWord ++ tailWord_649365).sum := by decide
  have hdescent : baseEnd_649365 < baseStart_649365 := by decide
  rcases family_descends (prefixWord ++ tailWord_649365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649440 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_649440 : Nat := 118140960795 + 649440 * 2 ^ 59
def prefixEnd_649440 : Nat := 4983230072969 + 3 ^ 40 * 649440 * 2
def baseEnd_649440 : Nat := 222316584170696197808857

theorem tailTrace_649440 : CollatzResearch.WordTrace tailWord_649440 prefixEnd_649440 222316584170696197808857 := by
  unfold tailWord_649440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843511383598635183336887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15791348511464846911115849 11843511383598635183336887)
  ·
    refine ⟨17765267075397952775005331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11843511383598635183336887 17765267075397952775005331)
    ·
      refine ⟨26647900613096929162507997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17765267075397952775005331 26647900613096929162507997)
      ·
        refine ⟨9992962729911348435940499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26647900613096929162507997 9992962729911348435940499)
        ·
          refine ⟨14989444094867022653910749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9992962729911348435940499 14989444094867022653910749)
          ·
            refine ⟨5621041535575133495216531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14989444094867022653910749 5621041535575133495216531)
            ·
              refine ⟨8431562303362700242824797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621041535575133495216531 8431562303362700242824797)
              ·
                refine ⟨3161835863761012591059299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8431562303362700242824797 3161835863761012591059299)
                ·
                  refine ⟨4742753795641518886588949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161835863761012591059299 4742753795641518886588949)
                  ·
                    refine ⟨222316584170696197808857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4742753795641518886588949 222316584170696197808857)
                    ·
                      rfl

theorem cell22_649440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_649440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649440 prefixEnd_649440 := by exact prefixLift 649440
  have htrace : WordTrace (prefixWord ++ tailWord_649440) baseStart_649440 baseEnd_649440 := by
    simpa [prefixWord, tailWord_649440, baseEnd_649440] using wordTrace_append hprefix tailTrace_649440
  have hstable : (prefixWord ++ tailWord_649440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649440).length < 2 ^ (prefixWord ++ tailWord_649440).sum := by decide
  have hdescent : baseEnd_649440 < baseStart_649440 := by decide
  rcases family_descends (prefixWord ++ tailWord_649440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649455 : List Nat := [1, 1, 2, 1, 6, 1, 10]
def baseStart_649455 : Nat := 118140960795 + 649455 * 2 ^ 59
def prefixEnd_649455 : Nat := 4983230072969 + 3 ^ 40 * 649455 * 2
def baseEnd_649455 : Nat := 8234137739897820691993

theorem tailTrace_649455 : CollatzResearch.WordTrace tailWord_649455 prefixEnd_649455 8234137739897820691993 := by
  unfold tailWord_649455
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687569862142927928469819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15791713241428618618979879 23687569862142927928469819)
  ·
    refine ⟨35531354793214391892704729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23687569862142927928469819 35531354793214391892704729)
    ·
      refine ⟨26648516094910793919528547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35531354793214391892704729 26648516094910793919528547)
      ·
        refine ⟨39972774142366190879292821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26648516094910793919528547 39972774142366190879292821)
        ·
          refine ⟨1873723787923415197466851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39972774142366190879292821 1873723787923415197466851)
          ·
            refine ⟨2810585681885122796200277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873723787923415197466851 2810585681885122796200277)
            ·
              refine ⟨8234137739897820691993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2810585681885122796200277 8234137739897820691993)
              ·
                rfl

theorem cell22_649455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 10].length) (baseStart_649455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649455 prefixEnd_649455 := by exact prefixLift 649455
  have htrace : WordTrace (prefixWord ++ tailWord_649455) baseStart_649455 baseEnd_649455 := by
    simpa [prefixWord, tailWord_649455, baseEnd_649455] using wordTrace_append hprefix tailTrace_649455
  have hstable : (prefixWord ++ tailWord_649455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649455).length < 2 ^ (prefixWord ++ tailWord_649455).sum := by decide
  have hdescent : baseEnd_649455 < baseStart_649455 := by decide
  rcases family_descends (prefixWord ++ tailWord_649455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649476 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_649476 : Nat := 118140960795 + 649476 * 2 ^ 59
def prefixEnd_649476 : Nat := 4983230072969 + 3 ^ 40 * 649476 * 2
def baseEnd_649476 : Nat := 222328907706404103908747

theorem tailTrace_649476 : CollatzResearch.WordTrace tailWord_649476 prefixEnd_649476 222328907706404103908747 := by
  unfold tailWord_649476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844167897533424257492141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15792223863377899009989521 11844167897533424257492141)
  ·
    refine ⟨4441562961575034096559553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11844167897533424257492141 4441562961575034096559553)
    ·
      refine ⟨3331172221181275572419665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4441562961575034096559553 3331172221181275572419665)
      ·
        refine ⟨2498379165885956679314749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3331172221181275572419665 2498379165885956679314749)
        ·
          refine ⟨936892187207233754743031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2498379165885956679314749 936892187207233754743031)
          ·
            refine ⟨1405338280810850632114547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936892187207233754743031 1405338280810850632114547)
            ·
              refine ⟨2108007421216275948171821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405338280810850632114547 2108007421216275948171821)
              ·
                refine ⟨790502782956103480564433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108007421216275948171821 790502782956103480564433)
                ·
                  refine ⟨592877087217077610423325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 790502782956103480564433 592877087217077610423325)
                  ·
                    refine ⟨222328907706404103908747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592877087217077610423325 222328907706404103908747)
                    ·
                      rfl

theorem cell22_649476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_649476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649476 prefixEnd_649476 := by exact prefixLift 649476
  have htrace : WordTrace (prefixWord ++ tailWord_649476) baseStart_649476 baseEnd_649476 := by
    simpa [prefixWord, tailWord_649476, baseEnd_649476] using wordTrace_append hprefix tailTrace_649476
  have hstable : (prefixWord ++ tailWord_649476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649476).length < 2 ^ (prefixWord ++ tailWord_649476).sum := by decide
  have hdescent : baseEnd_649476 < baseStart_649476 := by decide
  rcases family_descends (prefixWord ++ tailWord_649476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649487 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 3, 3]
def baseStart_649487 : Nat := 118140960795 + 649487 * 2 ^ 59
def prefixEnd_649487 : Nat := 4983230072969 + 3 ^ 40 * 649487 * 2
def baseEnd_649487 : Nat := 222332673231203741883713

theorem tailTrace_649487 : CollatzResearch.WordTrace tailWord_649487 prefixEnd_649487 222332673231203741883713 := by
  unfold tailWord_649487
  simp only [CollatzResearch.WordTrace]
  refine ⟨23688736998026997393634715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15792491332017998262423143 23688736998026997393634715)
  ·
    refine ⟨35533105497040496090452073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23688736998026997393634715 35533105497040496090452073)
    ·
      refine ⟨26649829122780372067839055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35533105497040496090452073 26649829122780372067839055)
      ·
        refine ⟨39974743684170558101758583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26649829122780372067839055 39974743684170558101758583)
        ·
          refine ⟨59962115526255837152637875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39974743684170558101758583 59962115526255837152637875)
          ·
            refine ⟨89943173289383755728956813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59962115526255837152637875 89943173289383755728956813)
            ·
              refine ⟨33728689983518908398358805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89943173289383755728956813 33728689983518908398358805)
              ·
                refine ⟨1581032342977448831173069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33728689983518908398358805 1581032342977448831173069)
                ·
                  refine ⟨592887128616543311689901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1581032342977448831173069 592887128616543311689901)
                  ·
                    refine ⟨222332673231203741883713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592887128616543311689901 222332673231203741883713)
                    ·
                      rfl

theorem cell22_649487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_649487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649487 prefixEnd_649487 := by exact prefixLift 649487
  have htrace : WordTrace (prefixWord ++ tailWord_649487) baseStart_649487 baseEnd_649487 := by
    simpa [prefixWord, tailWord_649487, baseEnd_649487] using wordTrace_append hprefix tailTrace_649487
  have hstable : (prefixWord ++ tailWord_649487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649487).length < 2 ^ (prefixWord ++ tailWord_649487).sum := by decide
  have hdescent : baseEnd_649487 < baseStart_649487 := by decide
  rcases family_descends (prefixWord ++ tailWord_649487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649532 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_649532 : Nat := 118140960795 + 649532 * 2 ^ 59
def prefixEnd_649532 : Nat := 4983230072969 + 3 ^ 40 * 649532 * 2
def baseEnd_649532 : Nat := 222348077650838624508575

theorem tailTrace_649532 : CollatzResearch.WordTrace tailWord_649532 prefixEnd_649532 222348077650838624508575 := by
  unfold tailWord_649532
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845189141431985039511425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15793585521909313386015233 11845189141431985039511425)
  ·
    refine ⟨8883891856073988779633569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11845189141431985039511425 8883891856073988779633569)
    ·
      refine ⟨6662918892055491584725177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8883891856073988779633569 6662918892055491584725177)
      ·
        refine ⟨4997189169041618688543883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6662918892055491584725177 4997189169041618688543883)
        ·
          refine ⟨7495783753562428032815825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997189169041618688543883 7495783753562428032815825)
          ·
            refine ⟨5621837815171821024611869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7495783753562428032815825 5621837815171821024611869)
            ·
              refine ⟨2108189180689432884229451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5621837815171821024611869 2108189180689432884229451)
              ·
                refine ⟨3162283771034149326344177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108189180689432884229451 3162283771034149326344177)
                ·
                  refine ⟨2371712828275611994758133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162283771034149326344177 2371712828275611994758133)
                  ·
                    refine ⟨222348077650838624508575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2371712828275611994758133 222348077650838624508575)
                    ·
                      rfl

theorem cell22_649532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_649532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649532 prefixEnd_649532 := by exact prefixLift 649532
  have htrace : WordTrace (prefixWord ++ tailWord_649532) baseStart_649532 baseEnd_649532 := by
    simpa [prefixWord, tailWord_649532, baseEnd_649532] using wordTrace_append hprefix tailTrace_649532
  have hstable : (prefixWord ++ tailWord_649532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649532).length < 2 ^ (prefixWord ++ tailWord_649532).sum := by decide
  have hdescent : baseEnd_649532 < baseStart_649532 := by decide
  rcases family_descends (prefixWord ++ tailWord_649532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649534 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_649534 : Nat := 118140960795 + 649534 * 2 ^ 59
def prefixEnd_649534 : Nat := 4983230072969 + 3 ^ 40 * 649534 * 2
def baseEnd_649534 : Nat := 74116254097237095319523

theorem tailTrace_649534 : CollatzResearch.WordTrace tailWord_649534 prefixEnd_649534 74116254097237095319523 := by
  unfold tailWord_649534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961306403607090552574457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15793634152571149613730437 2961306403607090552574457)
  ·
    refine ⟨2220979802705317914430843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2961306403607090552574457 2220979802705317914430843)
    ·
      refine ⟨3331469704057976871646265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220979802705317914430843 3331469704057976871646265)
      ·
        refine ⟨2498602278043482653734699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3331469704057976871646265 2498602278043482653734699)
        ·
          refine ⟨3747903417065223980602049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498602278043482653734699 3747903417065223980602049)
          ·
            refine ⟨2810927562798917985451537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747903417065223980602049 2810927562798917985451537)
            ·
              refine ⟨2108195672099188489088653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810927562798917985451537 2108195672099188489088653)
              ·
                refine ⟨790573377037195683408245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108195672099188489088653 790573377037195683408245)
                ·
                  refine ⟨74116254097237095319523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790573377037195683408245 74116254097237095319523)
                  ·
                    rfl

theorem cell22_649534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_649534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649534 prefixEnd_649534 := by exact prefixLift 649534
  have htrace : WordTrace (prefixWord ++ tailWord_649534) baseStart_649534 baseEnd_649534 := by
    simpa [prefixWord, tailWord_649534, baseEnd_649534] using wordTrace_append hprefix tailTrace_649534
  have hstable : (prefixWord ++ tailWord_649534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649534).length < 2 ^ (prefixWord ++ tailWord_649534).sum := by decide
  have hdescent : baseEnd_649534 < baseStart_649534 := by decide
  rcases family_descends (prefixWord ++ tailWord_649534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649607 : List Nat := [1, 1, 4, 2, 2, 1, 3, 8]
def baseStart_649607 : Nat := 118140960795 + 649607 * 2 ^ 59
def prefixEnd_649607 : Nat := 4983230072969 + 3 ^ 40 * 649607 * 2
def baseEnd_649607 : Nat := 24708194631507047653705

theorem tailTrace_649607 : CollatzResearch.WordTrace tailWord_649607 prefixEnd_649607 24708194631507047653705 := by
  unfold tailWord_649607
  simp only [CollatzResearch.WordTrace]
  refine ⟨23693113757592257888003075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15795409171728171925335383 23693113757592257888003075)
  ·
    refine ⟨35539670636388386832004613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23693113757592257888003075 35539670636388386832004613)
    ·
      refine ⟨6663688244322822531000865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35539670636388386832004613 6663688244322822531000865)
      ·
        refine ⟨4997766183242116898250649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6663688244322822531000865 4997766183242116898250649)
        ·
          refine ⟨3748324637431587673687987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997766183242116898250649 3748324637431587673687987)
          ·
            refine ⟨5622486956147381510531981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748324637431587673687987 5622486956147381510531981)
            ·
              refine ⟨2108432608555268066449493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5622486956147381510531981 2108432608555268066449493)
              ·
                refine ⟨24708194631507047653705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2108432608555268066449493 24708194631507047653705)
                ·
                  rfl

theorem cell22_649607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 8].length) (baseStart_649607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649607 prefixEnd_649607 := by exact prefixLift 649607
  have htrace : WordTrace (prefixWord ++ tailWord_649607) baseStart_649607 baseEnd_649607 := by
    simpa [prefixWord, tailWord_649607, baseEnd_649607] using wordTrace_append hprefix tailTrace_649607
  have hstable : (prefixWord ++ tailWord_649607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649607).length < 2 ^ (prefixWord ++ tailWord_649607).sum := by decide
  have hdescent : baseEnd_649607 < baseStart_649607 := by decide
  rcases family_descends (prefixWord ++ tailWord_649607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649624 : List Nat := [2, 1, 2, 5, 1, 3, 8]
def baseStart_649624 : Nat := 118140960795 + 649624 * 2 ^ 59
def prefixEnd_649624 : Nat := 4983230072969 + 3 ^ 40 * 649624 * 2
def baseEnd_649624 : Nat := 8236280412258557452159

theorem tailTrace_649624 : CollatzResearch.WordTrace tailWord_649624 prefixEnd_649624 8236280412258557452159 := by
  unfold tailWord_649624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11846866899265334895685963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15795822532353779860914617 11846866899265334895685963)
  ·
    refine ⟨17770300348898002343528945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11846866899265334895685963 17770300348898002343528945)
    ·
      refine ⟨13327725261673501757646709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17770300348898002343528945 13327725261673501757646709)
      ·
        refine ⟨1249474243281890789779379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13327725261673501757646709 1249474243281890789779379)
        ·
          refine ⟨1874211364922836184669069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249474243281890789779379 1874211364922836184669069)
          ·
            refine ⟨702829261846063569250901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1874211364922836184669069 702829261846063569250901)
            ·
              refine ⟨8236280412258557452159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 702829261846063569250901 8236280412258557452159)
              ·
                rfl

theorem cell22_649624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 8].length) (baseStart_649624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649624 prefixEnd_649624 := by exact prefixLift 649624
  have htrace : WordTrace (prefixWord ++ tailWord_649624) baseStart_649624 baseEnd_649624 := by
    simpa [prefixWord, tailWord_649624, baseEnd_649624] using wordTrace_append hprefix tailTrace_649624
  have hstable : (prefixWord ++ tailWord_649624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649624).length < 2 ^ (prefixWord ++ tailWord_649624).sum := by decide
  have hdescent : baseEnd_649624 < baseStart_649624 := by decide
  rcases family_descends (prefixWord ++ tailWord_649624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649630 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_649630 : Nat := 118140960795 + 649630 * 2 ^ 59
def prefixEnd_649630 : Nat := 4983230072969 + 3 ^ 40 * 649630 * 2
def baseEnd_649630 : Nat := 74127208351199678519425

theorem tailTrace_649630 : CollatzResearch.WordTrace tailWord_649630 prefixEnd_649630 74127208351199678519425 := by
  unfold tailWord_649630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961744079563616602011293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15795968424339288544060229 2961744079563616602011293)
  ·
    refine ⟨1110654029836356225754235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2961744079563616602011293 1110654029836356225754235)
    ·
      refine ⟨1665981044754534338631353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110654029836356225754235 1665981044754534338631353)
      ·
        refine ⟨1249485783565900753973515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665981044754534338631353 1249485783565900753973515)
        ·
          refine ⟨1874228675348851130960273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249485783565900753973515 1874228675348851130960273)
          ·
            refine ⟨1405671506511638348220205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874228675348851130960273 1405671506511638348220205)
            ·
              refine ⟨527126814941864380582577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405671506511638348220205 527126814941864380582577)
              ·
                refine ⟨395345111206398285436933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527126814941864380582577 395345111206398285436933)
                ·
                  refine ⟨74127208351199678519425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395345111206398285436933 74127208351199678519425)
                  ·
                    rfl

theorem cell22_649630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_649630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649630 prefixEnd_649630 := by exact prefixLift 649630
  have htrace : WordTrace (prefixWord ++ tailWord_649630) baseStart_649630 baseEnd_649630 := by
    simpa [prefixWord, tailWord_649630, baseEnd_649630] using wordTrace_append hprefix tailTrace_649630
  have hstable : (prefixWord ++ tailWord_649630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649630).length < 2 ^ (prefixWord ++ tailWord_649630).sum := by decide
  have hdescent : baseEnd_649630 < baseStart_649630 := by decide
  rcases family_descends (prefixWord ++ tailWord_649630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649637 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_649637 : Nat := 118140960795 + 649637 * 2 ^ 59
def prefixEnd_649637 : Nat := 4983230072969 + 3 ^ 40 * 649637 * 2
def baseEnd_649637 : Nat := 222384021296653350633253

theorem tailTrace_649637 : CollatzResearch.WordTrace tailWord_649637 prefixEnd_649637 222384021296653350633253 := by
  unfold tailWord_649637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694207947483573011595165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15796138631655715341063443 23694207947483573011595165)
  ·
    refine ⟨8885327980306339879348187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23694207947483573011595165 8885327980306339879348187)
    ·
      refine ⟨13327991970459509819022281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8885327980306339879348187 13327991970459509819022281)
      ·
        refine ⟨9995993977844632364266711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13327991970459509819022281 9995993977844632364266711)
        ·
          refine ⟨14993990966766948546400067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9995993977844632364266711 14993990966766948546400067)
          ·
            refine ⟨22490986450150422819600101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14993990966766948546400067 22490986450150422819600101)
            ·
              refine ⟨4217059959403204278675019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22490986450150422819600101 4217059959403204278675019)
              ·
                refine ⟨6325589939104806418012529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217059959403204278675019 6325589939104806418012529)
                ·
                  refine ⟨4744192454328604813509397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325589939104806418012529 4744192454328604813509397)
                  ·
                    refine ⟨222384021296653350633253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4744192454328604813509397 222384021296653350633253)
                    ·
                      rfl

theorem cell22_649637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_649637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649637 prefixEnd_649637 := by exact prefixLift 649637
  have htrace : WordTrace (prefixWord ++ tailWord_649637) baseStart_649637 baseEnd_649637 := by
    simpa [prefixWord, tailWord_649637, baseEnd_649637] using wordTrace_append hprefix tailTrace_649637
  have hstable : (prefixWord ++ tailWord_649637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649637).length < 2 ^ (prefixWord ++ tailWord_649637).sum := by decide
  have hdescent : baseEnd_649637 < baseStart_649637 := by decide
  rcases family_descends (prefixWord ++ tailWord_649637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649667 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_649667 : Nat := 118140960795 + 649667 * 2 ^ 59
def prefixEnd_649667 : Nat := 4983230072969 + 3 ^ 40 * 649667 * 2
def baseEnd_649667 : Nat := 222394290909743272383161

theorem tailTrace_649667 : CollatzResearch.WordTrace tailWord_649667 prefixEnd_649667 222394290909743272383161 := by
  unfold tailWord_649667
  simp only [CollatzResearch.WordTrace]
  refine ⟨23695302137374888135187255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15796868091583258756791503 23695302137374888135187255)
  ·
    refine ⟨35542953206062332202780883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23695302137374888135187255 35542953206062332202780883)
    ·
      refine ⟨53314429809093498304171325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35542953206062332202780883 53314429809093498304171325)
      ·
        refine ⟨19992911178410061864064247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53314429809093498304171325 19992911178410061864064247)
        ·
          refine ⟨29989366767615092796096371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19992911178410061864064247 29989366767615092796096371)
          ·
            refine ⟨44984050151422639194144557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29989366767615092796096371 44984050151422639194144557)
            ·
              refine ⟨16869018806783489697804209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44984050151422639194144557 16869018806783489697804209)
              ·
                refine ⟨12651764105087617273353157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16869018806783489697804209 12651764105087617273353157)
                ·
                  refine ⟨2372205769703928238753717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12651764105087617273353157 2372205769703928238753717)
                  ·
                    refine ⟨222394290909743272383161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2372205769703928238753717 222394290909743272383161)
                    ·
                      rfl

theorem cell22_649667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_649667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649667 prefixEnd_649667 := by exact prefixLift 649667
  have htrace : WordTrace (prefixWord ++ tailWord_649667) baseStart_649667 baseEnd_649667 := by
    simpa [prefixWord, tailWord_649667, baseEnd_649667] using wordTrace_append hprefix tailTrace_649667
  have hstable : (prefixWord ++ tailWord_649667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649667).length < 2 ^ (prefixWord ++ tailWord_649667).sum := by decide
  have hdescent : baseEnd_649667 < baseStart_649667 := by decide
  rcases family_descends (prefixWord ++ tailWord_649667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649701 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_649701 : Nat := 118140960795 + 649701 * 2 ^ 59
def prefixEnd_649701 : Nat := 4983230072969 + 3 ^ 40 * 649701 * 2
def baseEnd_649701 : Nat := 222405929804578517033057

theorem tailTrace_649701 : CollatzResearch.WordTrace tailWord_649701 prefixEnd_649701 222405929804578517033057 := by
  unfold tailWord_649701
  simp only [CollatzResearch.WordTrace]
  refine ⟨23696542219251711941924957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15797694812834474627949971 23696542219251711941924957)
  ·
    refine ⟨8886203332219391978221859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23696542219251711941924957 8886203332219391978221859)
    ·
      refine ⟨13329304998329087967332789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886203332219391978221859 13329304998329087967332789)
      ·
        refine ⟨1249622343593351996937449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13329304998329087967332789 1249622343593351996937449)
        ·
          refine ⟨937216757695013997703087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249622343593351996937449 937216757695013997703087)
          ·
            refine ⟨1405825136542520996554631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937216757695013997703087 1405825136542520996554631)
            ·
              refine ⟨2108737704813781494831947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405825136542520996554631 2108737704813781494831947)
              ·
                refine ⟨3163106557220672242247921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108737704813781494831947 3163106557220672242247921)
                ·
                  refine ⟨2372329917915504181685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163106557220672242247921 2372329917915504181685941)
                  ·
                    refine ⟨222405929804578517033057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2372329917915504181685941 222405929804578517033057)
                    ·
                      rfl

theorem cell22_649701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_649701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649701 prefixEnd_649701 := by exact prefixLift 649701
  have htrace : WordTrace (prefixWord ++ tailWord_649701) baseStart_649701 baseEnd_649701 := by
    simpa [prefixWord, tailWord_649701, baseEnd_649701] using wordTrace_append hprefix tailTrace_649701
  have hstable : (prefixWord ++ tailWord_649701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649701).length < 2 ^ (prefixWord ++ tailWord_649701).sum := by decide
  have hdescent : baseEnd_649701 < baseStart_649701 := by decide
  rcases family_descends (prefixWord ++ tailWord_649701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649731 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 4]
def baseStart_649731 : Nat := 118140960795 + 649731 * 2 ^ 59
def prefixEnd_649731 : Nat := 4983230072969 + 3 ^ 40 * 649731 * 2
def baseEnd_649731 : Nat := 74138733139222812927655

theorem tailTrace_649731 : CollatzResearch.WordTrace tailWord_649731 prefixEnd_649731 74138733139222812927655 := by
  unfold tailWord_649731
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697636409143027065517047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798424272762018043678031 23697636409143027065517047)
  ·
    refine ⟨35546454613714540598275571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23697636409143027065517047 35546454613714540598275571)
    ·
      refine ⟨53319681920571810897413357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35546454613714540598275571 53319681920571810897413357)
      ·
        refine ⟨19994880720214429086530009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53319681920571810897413357 19994880720214429086530009)
        ·
          refine ⟨14996160540160821814897507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19994880720214429086530009 14996160540160821814897507)
          ·
            refine ⟨22494240810241232722346261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14996160540160821814897507 22494240810241232722346261)
            ·
              refine ⟨1054417537980057783859981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22494240810241232722346261 1054417537980057783859981)
              ·
                refine ⟨395406576742521668947493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054417537980057783859981 395406576742521668947493)
                ·
                  refine ⟨74138733139222812927655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395406576742521668947493 74138733139222812927655)
                  ·
                    rfl

theorem cell22_649731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 4].length) (baseStart_649731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649731 prefixEnd_649731 := by exact prefixLift 649731
  have htrace : WordTrace (prefixWord ++ tailWord_649731) baseStart_649731 baseEnd_649731 := by
    simpa [prefixWord, tailWord_649731, baseEnd_649731] using wordTrace_append hprefix tailTrace_649731
  have hstable : (prefixWord ++ tailWord_649731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649731).length < 2 ^ (prefixWord ++ tailWord_649731).sum := by decide
  have hdescent : baseEnd_649731 < baseStart_649731 := by decide
  rcases family_descends (prefixWord ++ tailWord_649731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649748 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_649748 : Nat := 118140960795 + 649748 * 2 ^ 59
def prefixEnd_649748 : Nat := 4983230072969 + 3 ^ 40 * 649748 * 2
def baseEnd_649748 : Nat := 74140672955028687035971

theorem tailTrace_649748 : CollatzResearch.WordTrace tailWord_649748 prefixEnd_649748 74140672955028687035971 := by
  unfold tailWord_649748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849128225040719484442949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15798837633387625979257265 11849128225040719484442949)
  ·
    refine ⟨2221711542195134903333053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11849128225040719484442949 2221711542195134903333053)
    ·
      refine ⟨833141828323175588749895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2221711542195134903333053 833141828323175588749895)
      ·
        refine ⟨1249712742484763383124843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833141828323175588749895 1249712742484763383124843)
        ·
          refine ⟨1874569113727145074687265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249712742484763383124843 1874569113727145074687265)
          ·
            refine ⟨1405926835295358806015449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874569113727145074687265 1405926835295358806015449)
            ·
              refine ⟨1054445126471519104511587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405926835295358806015449 1054445126471519104511587)
              ·
                refine ⟨1581667689707278656767381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054445126471519104511587 1581667689707278656767381)
                ·
                  refine ⟨74140672955028687035971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1581667689707278656767381 74140672955028687035971)
                  ·
                    rfl

theorem cell22_649748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_649748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649748 prefixEnd_649748 := by exact prefixLift 649748
  have htrace : WordTrace (prefixWord ++ tailWord_649748) baseStart_649748 baseEnd_649748 := by
    simpa [prefixWord, tailWord_649748, baseEnd_649748] using wordTrace_append hprefix tailTrace_649748
  have hstable : (prefixWord ++ tailWord_649748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649748).length < 2 ^ (prefixWord ++ tailWord_649748).sum := by decide
  have hdescent : baseEnd_649748 < baseStart_649748 := by decide
  rcases family_descends (prefixWord ++ tailWord_649748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649804 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_649804 : Nat := 118140960795 + 649804 * 2 ^ 59
def prefixEnd_649804 : Nat := 4983230072969 + 3 ^ 40 * 649804 * 2
def baseEnd_649804 : Nat := 74147062936506860569247

theorem tailTrace_649804 : CollatzResearch.WordTrace tailWord_649804 prefixEnd_649804 74147062936506860569247 := by
  unfold tailWord_649804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850149468939280266462233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15800199291919040355282977 11850149468939280266462233)
  ·
    refine ⟨8887612101704460199846675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11850149468939280266462233 8887612101704460199846675)
    ·
      refine ⟨13331418152556690299770013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8887612101704460199846675 13331418152556690299770013)
      ·
        refine ⟨4999281807208758862413755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13331418152556690299770013 4999281807208758862413755)
        ·
          refine ⟨7498922710813138293620633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999281807208758862413755 7498922710813138293620633)
          ·
            refine ⟨5624192033109853720215475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7498922710813138293620633 5624192033109853720215475)
            ·
              refine ⟨8436288049664780580323213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624192033109853720215475 8436288049664780580323213)
              ·
                refine ⟨3163608018624292717621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8436288049664780580323213 3163608018624292717621205)
                ·
                  refine ⟨74147062936506860569247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3163608018624292717621205 74147062936506860569247)
                  ·
                    rfl

theorem cell22_649804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_649804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649804 prefixEnd_649804 := by exact prefixLift 649804
  have htrace : WordTrace (prefixWord ++ tailWord_649804) baseStart_649804 baseEnd_649804 := by
    simpa [prefixWord, tailWord_649804, baseEnd_649804] using wordTrace_append hprefix tailTrace_649804
  have hstable : (prefixWord ++ tailWord_649804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649804).length < 2 ^ (prefixWord ++ tailWord_649804).sum := by decide
  have hdescent : baseEnd_649804 < baseStart_649804 := by decide
  rcases family_descends (prefixWord ++ tailWord_649804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649881 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_649881 : Nat := 118140960795 + 649881 * 2 ^ 59
def prefixEnd_649881 : Nat := 4983230072969 + 3 ^ 40 * 649881 * 2
def baseEnd_649881 : Nat := 222467547483118047532505

theorem tailTrace_649881 : CollatzResearch.WordTrace tailWord_649881 prefixEnd_649881 222467547483118047532505 := by
  unfold tailWord_649881
  simp only [CollatzResearch.WordTrace]
  refine ⟨23703107358599602683477497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15802071572399735122318331 23703107358599602683477497)
  ·
    refine ⟨17777330518949702012608123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23703107358599602683477497 17777330518949702012608123)
    ·
      refine ⟨26665995778424553018912185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17777330518949702012608123 26665995778424553018912185)
      ·
        refine ⟨19999496833818414764184139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26665995778424553018912185 19999496833818414764184139)
        ·
          refine ⟨29999245250727622146276209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19999496833818414764184139 29999245250727622146276209)
          ·
            refine ⟨22499433938045716609707157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29999245250727622146276209 22499433938045716609707157)
            ·
              refine ⟨1054660965845892966080023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22499433938045716609707157 1054660965845892966080023)
              ·
                refine ⟨1581991448768839449120035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054660965845892966080023 1581991448768839449120035)
                ·
                  refine ⟨2372987173153259173680053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581991448768839449120035 2372987173153259173680053)
                  ·
                    refine ⟨222467547483118047532505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2372987173153259173680053 222467547483118047532505)
                    ·
                      rfl

theorem cell22_649881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_649881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649881 prefixEnd_649881 := by exact prefixLift 649881
  have htrace : WordTrace (prefixWord ++ tailWord_649881) baseStart_649881 baseEnd_649881 := by
    simpa [prefixWord, tailWord_649881, baseEnd_649881] using wordTrace_append hprefix tailTrace_649881
  have hstable : (prefixWord ++ tailWord_649881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649881).length < 2 ^ (prefixWord ++ tailWord_649881).sum := by decide
  have hdescent : baseEnd_649881 < baseStart_649881 := by decide
  rcases family_descends (prefixWord ++ tailWord_649881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649902 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_649902 : Nat := 118140960795 + 649902 * 2 ^ 59
def prefixEnd_649902 : Nat := 4983230072969 + 3 ^ 40 * 649902 * 2
def baseEnd_649902 : Nat := 222474736212280992757441

theorem tailTrace_649902 : CollatzResearch.WordTrace tailWord_649902 prefixEnd_649902 222474736212280992757441 := by
  unfold tailWord_649902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962984161440440408748995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15802582194349015513327973 2962984161440440408748995)
  ·
    refine ⟨4444476242160660613123493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962984161440440408748995 4444476242160660613123493)
    ·
      refine ⟨833339295405123864960655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4444476242160660613123493 833339295405123864960655)
      ·
        refine ⟨1250008943107685797440983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833339295405123864960655 1250008943107685797440983)
        ·
          refine ⟨1875013414661528696161475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250008943107685797440983 1875013414661528696161475)
          ·
            refine ⟨2812520121992293044242213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875013414661528696161475 2812520121992293044242213)
            ·
              refine ⟨527347522873554945795415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2812520121992293044242213 527347522873554945795415)
              ·
                refine ⟨791021284310332418693123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527347522873554945795415 791021284310332418693123)
                ·
                  refine ⟨1186531926465498628039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791021284310332418693123 1186531926465498628039685)
                  ·
                    refine ⟨222474736212280992757441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186531926465498628039685 222474736212280992757441)
                    ·
                      rfl

theorem cell22_649902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_649902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649902 prefixEnd_649902 := by exact prefixLift 649902
  have htrace : WordTrace (prefixWord ++ tailWord_649902) baseStart_649902 baseEnd_649902 := by
    simpa [prefixWord, tailWord_649902, baseEnd_649902] using wordTrace_append hprefix tailTrace_649902
  have hstable : (prefixWord ++ tailWord_649902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649902).length < 2 ^ (prefixWord ++ tailWord_649902).sum := by decide
  have hdescent : baseEnd_649902 < baseStart_649902 := by decide
  rcases family_descends (prefixWord ++ tailWord_649902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649911 : List Nat := [1, 1, 3, 1, 6, 1, 9]
def baseStart_649911 : Nat := 118140960795 + 649911 * 2 ^ 59
def prefixEnd_649911 : Nat := 4983230072969 + 3 ^ 40 * 649911 * 2
def baseEnd_649911 : Nat := 8239919151711406269719

theorem tailTrace_649911 : CollatzResearch.WordTrace tailWord_649911 prefixEnd_649911 8239919151711406269719 := by
  unfold tailWord_649911
  simp only [CollatzResearch.WordTrace]
  refine ⟨23704201548490917807069587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15802801032327278538046391 23704201548490917807069587)
  ·
    refine ⟨35556302322736376710604381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23704201548490917807069587 35556302322736376710604381)
    ·
      refine ⟨13333613371026141266476643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35556302322736376710604381 13333613371026141266476643)
      ·
        refine ⟨20000420056539211899714965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13333613371026141266476643 20000420056539211899714965)
        ·
          refine ⟨937519690150275557799139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20000420056539211899714965 937519690150275557799139)
          ·
            refine ⟨1406279535225413336698709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937519690150275557799139 1406279535225413336698709)
            ·
              refine ⟨8239919151711406269719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1406279535225413336698709 8239919151711406269719)
              ·
                rfl

theorem cell22_649911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 9].length) (baseStart_649911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649911 prefixEnd_649911 := by exact prefixLift 649911
  have htrace : WordTrace (prefixWord ++ tailWord_649911) baseStart_649911 baseEnd_649911 := by
    simpa [prefixWord, tailWord_649911, baseEnd_649911] using wordTrace_append hprefix tailTrace_649911
  have hstable : (prefixWord ++ tailWord_649911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649911).length < 2 ^ (prefixWord ++ tailWord_649911).sum := by decide
  have hdescent : baseEnd_649911 < baseStart_649911 := by decide
  rcases family_descends (prefixWord ++ tailWord_649911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649932 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_649932 : Nat := 118140960795 + 649932 * 2 ^ 59
def prefixEnd_649932 : Nat := 4983230072969 + 3 ^ 40 * 649932 * 2
def baseEnd_649932 : Nat := 222485005825370914507349

theorem tailTrace_649932 : CollatzResearch.WordTrace tailWord_649932 prefixEnd_649932 222485005825370914507349 := by
  unfold tailWord_649932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852483740707419196792025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15803311654276558929056033 11852483740707419196792025)
  ·
    refine ⟨8889362805530564397594019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11852483740707419196792025 8889362805530564397594019)
    ·
      refine ⟨13334044208295846596391029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889362805530564397594019 13334044208295846596391029)
      ·
        refine ⟨1250066644527735618411659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13334044208295846596391029 1250066644527735618411659)
        ·
          refine ⟨1875099966791603427617489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250066644527735618411659 1875099966791603427617489)
          ·
            refine ⟨1406324975093702570713117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875099966791603427617489 1406324975093702570713117)
            ·
              refine ⟨527371865660138464017419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406324975093702570713117 527371865660138464017419)
              ·
                refine ⟨791057798490207696026129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527371865660138464017419 791057798490207696026129)
                ·
                  refine ⟨593293348867655772019597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791057798490207696026129 593293348867655772019597)
                  ·
                    refine ⟨222485005825370914507349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593293348867655772019597 222485005825370914507349)
                    ·
                      rfl

theorem cell22_649932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_649932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649932 prefixEnd_649932 := by exact prefixLift 649932
  have htrace : WordTrace (prefixWord ++ tailWord_649932) baseStart_649932 baseEnd_649932 := by
    simpa [prefixWord, tailWord_649932, baseEnd_649932] using wordTrace_append hprefix tailTrace_649932
  have hstable : (prefixWord ++ tailWord_649932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649932).length < 2 ^ (prefixWord ++ tailWord_649932).sum := by decide
  have hdescent : baseEnd_649932 < baseStart_649932 := by decide
  rcases family_descends (prefixWord ++ tailWord_649932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649943 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 3, 3]
def baseStart_649943 : Nat := 118140960795 + 649943 * 2 ^ 59
def prefixEnd_649943 : Nat := 4983230072969 + 3 ^ 40 * 649943 * 2
def baseEnd_649943 : Nat := 222488771350170552482315

theorem tailTrace_649943 : CollatzResearch.WordTrace tailWord_649943 prefixEnd_649943 222488771350170552482315 := by
  unfold tailWord_649943
  simp only [CollatzResearch.WordTrace]
  refine ⟨23705368684374987272234483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15803579122916658181489655 23705368684374987272234483)
  ·
    refine ⟨35558053026562480908351725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23705368684374987272234483 35558053026562480908351725)
    ·
      refine ⟨13334269884960930340631897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35558053026562480908351725 13334269884960930340631897)
      ·
        refine ⟨10000702413720697755473923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13334269884960930340631897 10000702413720697755473923)
        ·
          refine ⟨15001053620581046633210885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000702413720697755473923 15001053620581046633210885)
          ·
            refine ⟨2812697553858946243727041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15001053620581046633210885 2812697553858946243727041)
            ·
              refine ⟨2109523165394209682795281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812697553858946243727041 2109523165394209682795281)
              ·
                refine ⟨1582142374045657262096461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109523165394209682795281 1582142374045657262096461)
                ·
                  refine ⟨593303390267121473286173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1582142374045657262096461 593303390267121473286173)
                  ·
                    refine ⟨222488771350170552482315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593303390267121473286173 222488771350170552482315)
                    ·
                      rfl

theorem cell22_649943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_649943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649943 prefixEnd_649943 := by exact prefixLift 649943
  have htrace : WordTrace (prefixWord ++ tailWord_649943) baseStart_649943 baseEnd_649943 := by
    simpa [prefixWord, tailWord_649943, baseEnd_649943] using wordTrace_append hprefix tailTrace_649943
  have hstable : (prefixWord ++ tailWord_649943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649943).length < 2 ^ (prefixWord ++ tailWord_649943).sum := by decide
  have hdescent : baseEnd_649943 < baseStart_649943 := by decide
  rcases family_descends (prefixWord ++ tailWord_649943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649956 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_649956 : Nat := 118140960795 + 649956 * 2 ^ 59
def prefixEnd_649956 : Nat := 4983230072969 + 3 ^ 40 * 649956 * 2
def baseEnd_649956 : Nat := 74164407171947617302425

theorem tailTrace_649956 : CollatzResearch.WordTrace tailWord_649956 prefixEnd_649956 74164407171947617302425 := by
  unfold tailWord_649956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852921416663945246228861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15803895222218593661638481 11852921416663945246228861)
  ·
    refine ⟨4444845531248979467335823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11852921416663945246228861 4444845531248979467335823)
    ·
      refine ⟨6667268296873469201003735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444845531248979467335823 6667268296873469201003735)
      ·
        refine ⟨10000902445310203801505603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667268296873469201003735 10000902445310203801505603)
        ·
          refine ⟨15001353667965305702258405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000902445310203801505603 15001353667965305702258405)
          ·
            refine ⟨2812753812743494819173451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15001353667965305702258405 2812753812743494819173451)
            ·
              refine ⟨4219130719115242228760177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812753812743494819173451 4219130719115242228760177)
              ·
                refine ⟨3164348039336431671570133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219130719115242228760177 3164348039336431671570133)
                ·
                  refine ⟨74164407171947617302425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3164348039336431671570133 74164407171947617302425)
                  ·
                    rfl

theorem cell22_649956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_649956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_649956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_649956 prefixEnd_649956 := by exact prefixLift 649956
  have htrace : WordTrace (prefixWord ++ tailWord_649956) baseStart_649956 baseEnd_649956 := by
    simpa [prefixWord, tailWord_649956, baseEnd_649956] using wordTrace_append hprefix tailTrace_649956
  have hstable : (prefixWord ++ tailWord_649956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649956).length < 2 ^ (prefixWord ++ tailWord_649956).sum := by decide
  have hdescent : baseEnd_649956 < baseStart_649956 := by decide
  rcases family_descends (prefixWord ++ tailWord_649956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650001 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 6]
def baseStart_650001 : Nat := 118140960795 + 650001 * 2 ^ 59
def prefixEnd_650001 : Nat := 4983230072969 + 3 ^ 40 * 650001 * 2
def baseEnd_650001 : Nat := 74169541978492578177379

theorem tailTrace_650001 : CollatzResearch.WordTrace tailWord_650001 prefixEnd_650001 74169541978492578177379 := by
  unfold tailWord_650001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707484118164863177845857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15804989412109908785230571 23707484118164863177845857)
  ·
    refine ⟨17780613088623647383384393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23707484118164863177845857 17780613088623647383384393)
    ·
      refine ⟨13335459816467735537538295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17780613088623647383384393 13335459816467735537538295)
      ·
        refine ⟨20003189724701603306307443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13335459816467735537538295 20003189724701603306307443)
        ·
          refine ⟨30004784587052404959461165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20003189724701603306307443 30004784587052404959461165)
          ·
            refine ⟨11251794220144651859797937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30004784587052404959461165 11251794220144651859797937)
            ·
              refine ⟨8438845665108488894848453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251794220144651859797937 8438845665108488894848453)
              ·
                refine ⟨1582283562207841667784085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8438845665108488894848453 1582283562207841667784085)
                ·
                  refine ⟨74169541978492578177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1582283562207841667784085 74169541978492578177379)
                  ·
                    rfl

theorem cell22_650001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_650001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650001 prefixEnd_650001 := by exact prefixLift 650001
  have htrace : WordTrace (prefixWord ++ tailWord_650001) baseStart_650001 baseEnd_650001 := by
    simpa [prefixWord, tailWord_650001, baseEnd_650001] using wordTrace_append hprefix tailTrace_650001
  have hstable : (prefixWord ++ tailWord_650001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650001).length < 2 ^ (prefixWord ++ tailWord_650001).sum := by decide
  have hdescent : baseEnd_650001 < baseStart_650001 := by decide
  rcases family_descends (prefixWord ++ tailWord_650001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650035 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 4]
def baseStart_650035 : Nat := 118140960795 + 650035 * 2 ^ 59
def prefixEnd_650035 : Nat := 4983230072969 + 3 ^ 40 * 650035 * 2
def baseEnd_650035 : Nat := 74173421610104326394011

theorem tailTrace_650035 : CollatzResearch.WordTrace tailWord_650035 prefixEnd_650035 74173421610104326394011 := by
  unfold tailWord_650035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708724200041686984583559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15805816133361124656389039 23708724200041686984583559)
  ·
    refine ⟨35563086300062530476875339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23708724200041686984583559 35563086300062530476875339)
    ·
      refine ⟨53344629450093795715313009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35563086300062530476875339 53344629450093795715313009)
      ·
        refine ⟨40008472087570346786484757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53344629450093795715313009 40008472087570346786484757)
        ·
          refine ⟨1875397129104860005616473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40008472087570346786484757 1875397129104860005616473)
          ·
            refine ⟨1406547846828645004212355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875397129104860005616473 1406547846828645004212355)
            ·
              refine ⟨2109821770242967506318533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406547846828645004212355 2109821770242967506318533)
              ·
                refine ⟨395591581920556407434725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2109821770242967506318533 395591581920556407434725)
                ·
                  refine ⟨74173421610104326394011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395591581920556407434725 74173421610104326394011)
                  ·
                    rfl

theorem cell22_650035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 4].length) (baseStart_650035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650035 prefixEnd_650035 := by exact prefixLift 650035
  have htrace : WordTrace (prefixWord ++ tailWord_650035) baseStart_650035 baseEnd_650035 := by
    simpa [prefixWord, tailWord_650035, baseEnd_650035] using wordTrace_append hprefix tailTrace_650035
  have hstable : (prefixWord ++ tailWord_650035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650035).length < 2 ^ (prefixWord ++ tailWord_650035).sum := by decide
  have hdescent : baseEnd_650035 < baseStart_650035 := by decide
  rcases family_descends (prefixWord ++ tailWord_650035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650052 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_650052 : Nat := 118140960795 + 650052 * 2 ^ 59
def prefixEnd_650052 : Nat := 4983230072969 + 3 ^ 40 * 650052 * 2
def baseEnd_650052 : Nat := 74175361425910200502327

theorem tailTrace_650052 : CollatzResearch.WordTrace tailWord_650052 prefixEnd_650052 74175361425910200502327 := by
  unfold tailWord_650052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854672120490049443976205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15806229493986732591968273 11854672120490049443976205)
  ·
    refine ⟨4445502045183768541491077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11854672120490049443976205 4445502045183768541491077)
    ·
      refine ⟨833531633471956601529577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4445502045183768541491077 833531633471956601529577)
      ·
        refine ⟨625148725103967451147183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 833531633471956601529577 625148725103967451147183)
        ·
          refine ⟨937723087655951176720775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625148725103967451147183 937723087655951176720775)
          ·
            refine ⟨1406584631483926765081163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937723087655951176720775 1406584631483926765081163)
            ·
              refine ⟨2109876947225890147621745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406584631483926765081163 2109876947225890147621745)
              ·
                refine ⟨1582407710419417610716309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109876947225890147621745 1582407710419417610716309)
                ·
                  refine ⟨74175361425910200502327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1582407710419417610716309 74175361425910200502327)
                  ·
                    rfl

theorem cell22_650052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_650052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650052 prefixEnd_650052 := by exact prefixLift 650052
  have htrace : WordTrace (prefixWord ++ tailWord_650052) baseStart_650052 baseEnd_650052 := by
    simpa [prefixWord, tailWord_650052, baseEnd_650052] using wordTrace_append hprefix tailTrace_650052
  have hstable : (prefixWord ++ tailWord_650052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650052).length < 2 ^ (prefixWord ++ tailWord_650052).sum := by decide
  have hdescent : baseEnd_650052 < baseStart_650052 := by decide
  rcases family_descends (prefixWord ++ tailWord_650052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650108 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_650108 : Nat := 118140960795 + 650108 * 2 ^ 59
def prefixEnd_650108 : Nat := 4983230072969 + 3 ^ 40 * 650108 * 2
def baseEnd_650108 : Nat := 74181751407388374035603

theorem tailTrace_650108 : CollatzResearch.WordTrace tailWord_650108 prefixEnd_650108 74181751407388374035603 := by
  unfold tailWord_650108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855693364388610225995489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15807591152518146967993985 11855693364388610225995489)
  ·
    refine ⟨8891770023291457669496617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11855693364388610225995489 8891770023291457669496617)
    ·
      refine ⟨6668827517468593252122463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8891770023291457669496617 6668827517468593252122463)
      ·
        refine ⟨10003241276202889878183695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6668827517468593252122463 10003241276202889878183695)
        ·
          refine ⟨15004861914304334817275543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10003241276202889878183695 15004861914304334817275543)
          ·
            refine ⟨22507292871456502225913315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15004861914304334817275543 22507292871456502225913315)
            ·
              refine ⟨33760939307184753338869973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22507292871456502225913315 33760939307184753338869973)
              ·
                refine ⟨791272015012142656379765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33760939307184753338869973 791272015012142656379765)
                ·
                  refine ⟨74181751407388374035603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791272015012142656379765 74181751407388374035603)
                  ·
                    rfl

theorem cell22_650108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_650108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650108 prefixEnd_650108 := by exact prefixLift 650108
  have htrace : WordTrace (prefixWord ++ tailWord_650108) baseStart_650108 baseEnd_650108 := by
    simpa [prefixWord, tailWord_650108, baseEnd_650108] using wordTrace_append hprefix tailTrace_650108
  have hstable : (prefixWord ++ tailWord_650108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650108).length < 2 ^ (prefixWord ++ tailWord_650108).sum := by decide
  have hdescent : baseEnd_650108 < baseStart_650108 := by decide
  rcases family_descends (prefixWord ++ tailWord_650108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650146 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_650146 : Nat := 118140960795 + 650146 * 2 ^ 59
def prefixEnd_650146 : Nat := 4983230072969 + 3 ^ 40 * 650146 * 2
def baseEnd_650146 : Nat := 222558262398745689656693

theorem tailTrace_650146 : CollatzResearch.WordTrace tailWord_650146 prefixEnd_650146 222558262398745689656693 := by
  unfold tailWord_650146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928193175659888235468573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15808515135093035294582861 5928193175659888235468573)
  ·
    refine ⟨2223072440872458088300715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5928193175659888235468573 2223072440872458088300715)
    ·
      refine ⟨3334608661308687132451073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2223072440872458088300715 3334608661308687132451073)
      ·
        refine ⟨2500956495981515349338305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334608661308687132451073 2500956495981515349338305)
        ·
          refine ⟨1875717371986136512003729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2500956495981515349338305 1875717371986136512003729)
          ·
            refine ⟨1406788028989602384002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875717371986136512003729 1406788028989602384002797)
            ·
              refine ⟨527545510871100894001049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406788028989602384002797 527545510871100894001049)
              ·
                refine ⟨395659133153325670500787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527545510871100894001049 395659133153325670500787)
                ·
                  refine ⟨593488699729988505751181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395659133153325670500787 593488699729988505751181)
                  ·
                    refine ⟨222558262398745689656693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593488699729988505751181 222558262398745689656693)
                    ·
                      rfl

theorem cell22_650146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_650146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650146 prefixEnd_650146 := by exact prefixLift 650146
  have htrace : WordTrace (prefixWord ++ tailWord_650146) baseStart_650146 baseEnd_650146 := by
    simpa [prefixWord, tailWord_650146, baseEnd_650146] using wordTrace_append hprefix tailTrace_650146
  have hstable : (prefixWord ++ tailWord_650146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650146).length < 2 ^ (prefixWord ++ tailWord_650146).sum := by decide
  have hdescent : baseEnd_650146 < baseStart_650146 := by decide
  rcases family_descends (prefixWord ++ tailWord_650146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650183 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_650183 : Nat := 118140960795 + 650183 * 2 ^ 59
def prefixEnd_650183 : Nat := 4983230072969 + 3 ^ 40 * 650183 * 2
def baseEnd_650183 : Nat := 222570928254889926481579

theorem tailTrace_650183 : CollatzResearch.WordTrace tailWord_650183 prefixEnd_650183 222570928254889926481579 := by
  unfold tailWord_650183
  simp only [CollatzResearch.WordTrace]
  refine ⟨23714122203505508260971203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15809414802337005507314135 23714122203505508260971203)
  ·
    refine ⟨35571183305258262391456805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23714122203505508260971203 35571183305258262391456805)
    ·
      refine ⟨6669596869735924198398151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35571183305258262391456805 6669596869735924198398151)
      ·
        refine ⟨10004395304603886297597227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669596869735924198398151 10004395304603886297597227)
        ·
          refine ⟨15006592956905829446395841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004395304603886297597227 15006592956905829446395841)
          ·
            refine ⟨11254944717679372084796881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15006592956905829446395841 11254944717679372084796881)
            ·
              refine ⟨8441208538259529063597661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11254944717679372084796881 8441208538259529063597661)
              ·
                refine ⟨3165453201847323398849123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8441208538259529063597661 3165453201847323398849123)
                ·
                  refine ⟨4748179802770985098273685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165453201847323398849123 4748179802770985098273685)
                  ·
                    refine ⟨222570928254889926481579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4748179802770985098273685 222570928254889926481579)
                    ·
                      rfl

theorem cell22_650183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_650183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650183 prefixEnd_650183 := by exact prefixLift 650183
  have htrace : WordTrace (prefixWord ++ tailWord_650183) baseStart_650183 baseEnd_650183 := by
    simpa [prefixWord, tailWord_650183, baseEnd_650183] using wordTrace_append hprefix tailTrace_650183
  have hstable : (prefixWord ++ tailWord_650183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650183).length < 2 ^ (prefixWord ++ tailWord_650183).sum := by decide
  have hdescent : baseEnd_650183 < baseStart_650183 := by decide
  rcases family_descends (prefixWord ++ tailWord_650183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650200 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_650200 : Nat := 118140960795 + 650200 * 2 ^ 59
def prefixEnd_650200 : Nat := 4983230072969 + 3 ^ 40 * 650200 * 2
def baseEnd_650200 : Nat := 222576747702307548806527

theorem tailTrace_650200 : CollatzResearch.WordTrace tailWord_650200 prefixEnd_650200 222576747702307548806527 := by
  unfold tailWord_650200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857371122221960082170027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15809828162962613442893369 11857371122221960082170027)
  ·
    refine ⟨17786056683332940123255041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11857371122221960082170027 17786056683332940123255041)
    ·
      refine ⟨13339542512499705092441281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17786056683332940123255041 13339542512499705092441281)
      ·
        refine ⟨10004656884374778819330961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13339542512499705092441281 10004656884374778819330961)
        ·
          refine ⟨7503492663281084114498221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10004656884374778819330961 7503492663281084114498221)
          ·
            refine ⟨2813809748730406542936833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7503492663281084114498221 2813809748730406542936833)
            ·
              refine ⟨2110357311547804907202625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813809748730406542936833 2110357311547804907202625)
              ·
                refine ⟨1582767983660853680401969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110357311547804907202625 1582767983660853680401969)
                ·
                  refine ⟨1187075987745640260301477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582767983660853680401969 1187075987745640260301477)
                  ·
                    refine ⟨222576747702307548806527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1187075987745640260301477 222576747702307548806527)
                    ·
                      rfl

theorem cell22_650200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_650200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650200 prefixEnd_650200 := by exact prefixLift 650200
  have htrace : WordTrace (prefixWord ++ tailWord_650200) baseStart_650200 baseEnd_650200 := by
    simpa [prefixWord, tailWord_650200, baseEnd_650200] using wordTrace_append hprefix tailTrace_650200
  have hstable : (prefixWord ++ tailWord_650200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650200).length < 2 ^ (prefixWord ++ tailWord_650200).sum := by decide
  have hdescent : baseEnd_650200 < baseStart_650200 := by decide
  rcases family_descends (prefixWord ++ tailWord_650200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650202 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_650202 : Nat := 118140960795 + 650202 * 2 ^ 59
def prefixEnd_650202 : Nat := 4983230072969 + 3 ^ 40 * 650202 * 2
def baseEnd_650202 : Nat := 222577432343180210256521

theorem tailTrace_650202 : CollatzResearch.WordTrace tailWord_650202 prefixEnd_650202 222577432343180210256521 := by
  unfold tailWord_650202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928703797609168626478215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15809876793624449670608573 5928703797609168626478215)
  ·
    refine ⟨8893055696413752939717323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5928703797609168626478215 8893055696413752939717323)
    ·
      refine ⟨13339583544620629409575985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893055696413752939717323 13339583544620629409575985)
      ·
        refine ⟨10004687658465472057181989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13339583544620629409575985 10004687658465472057181989)
        ·
          refine ⟨1875878935962276010721623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10004687658465472057181989 1875878935962276010721623)
          ·
            refine ⟨2813818403943414016082435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875878935962276010721623 2813818403943414016082435)
            ·
              refine ⟨4220727605915121024123653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813818403943414016082435 4220727605915121024123653)
              ·
                refine ⟨791386426109085192023185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4220727605915121024123653 791386426109085192023185)
                ·
                  refine ⟨593539819581813894017389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791386426109085192023185 593539819581813894017389)
                  ·
                    refine ⟨222577432343180210256521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593539819581813894017389 222577432343180210256521)
                    ·
                      rfl

theorem cell22_650202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_650202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650202 prefixEnd_650202 := by exact prefixLift 650202
  have htrace : WordTrace (prefixWord ++ tailWord_650202) baseStart_650202 baseEnd_650202 := by
    simpa [prefixWord, tailWord_650202, baseEnd_650202] using wordTrace_append hprefix tailTrace_650202
  have hstable : (prefixWord ++ tailWord_650202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650202).length < 2 ^ (prefixWord ++ tailWord_650202).sum := by decide
  have hdescent : baseEnd_650202 < baseStart_650202 := by decide
  rcases family_descends (prefixWord ++ tailWord_650202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650215 : List Nat := [1, 1, 5, 2, 2, 1, 3, 7]
def baseStart_650215 : Nat := 118140960795 + 650215 * 2 ^ 59
def prefixEnd_650215 : Nat := 4983230072969 + 3 ^ 40 * 650215 * 2
def baseEnd_650215 : Nat := 24731320278761389964609

theorem tailTrace_650215 : CollatzResearch.WordTrace tailWord_650215 prefixEnd_650215 24731320278761389964609 := by
  unfold tailWord_650215
  simp only [CollatzResearch.WordTrace]
  refine ⟨23715289339389577726136099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15810192892926385150757399 23715289339389577726136099)
  ·
    refine ⟨35572934009084366589204149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23715289339389577726136099 35572934009084366589204149)
    ·
      refine ⟨3334962563351659367737889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35572934009084366589204149 3334962563351659367737889)
      ·
        refine ⟨2501221922513744525803417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334962563351659367737889 2501221922513744525803417)
        ·
          refine ⟨1875916441885308394352563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2501221922513744525803417 1875916441885308394352563)
          ·
            refine ⟨2813874662827962591528845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875916441885308394352563 2813874662827962591528845)
            ·
              refine ⟨1055202998560485971823317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2813874662827962591528845 1055202998560485971823317)
              ·
                refine ⟨24731320278761389964609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1055202998560485971823317 24731320278761389964609)
                ·
                  rfl

theorem cell22_650215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 7].length) (baseStart_650215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650215 prefixEnd_650215 := by exact prefixLift 650215
  have htrace : WordTrace (prefixWord ++ tailWord_650215) baseStart_650215 baseEnd_650215 := by
    simpa [prefixWord, tailWord_650215, baseEnd_650215] using wordTrace_append hprefix tailTrace_650215
  have hstable : (prefixWord ++ tailWord_650215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650215).length < 2 ^ (prefixWord ++ tailWord_650215).sum := by decide
  have hdescent : baseEnd_650215 < baseStart_650215 := by decide
  rcases family_descends (prefixWord ++ tailWord_650215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650264 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_650264 : Nat := 118140960795 + 650264 * 2 ^ 59
def prefixEnd_650264 : Nat := 4983230072969 + 3 ^ 40 * 650264 * 2
def baseEnd_650264 : Nat := 222598656210232715206331

theorem tailTrace_650264 : CollatzResearch.WordTrace tailWord_650264 prefixEnd_650264 222598656210232715206331 := by
  unfold tailWord_650264
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858538258106029547334923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15811384344141372729779897 11858538258106029547334923)
  ·
    refine ⟨17787807387159044321002385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11858538258106029547334923 17787807387159044321002385)
    ·
      refine ⟨13340855540369283240751789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17787807387159044321002385 13340855540369283240751789)
      ·
        refine ⟨5002820827638481215281921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13340855540369283240751789 5002820827638481215281921)
        ·
          refine ⟨3752115620728860911461441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5002820827638481215281921 3752115620728860911461441)
          ·
            refine ⟨2814086715546645683596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752115620728860911461441 2814086715546645683596081)
            ·
              refine ⟨2110565036659984262697061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814086715546645683596081 2110565036659984262697061)
              ·
                refine ⟨395730944373747049255699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2110565036659984262697061 395730944373747049255699)
                ·
                  refine ⟨593596416560620573883549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395730944373747049255699 593596416560620573883549)
                  ·
                    refine ⟨222598656210232715206331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593596416560620573883549 222598656210232715206331)
                    ·
                      rfl

theorem cell22_650264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_650264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650264 prefixEnd_650264 := by exact prefixLift 650264
  have htrace : WordTrace (prefixWord ++ tailWord_650264) baseStart_650264 baseEnd_650264 := by
    simpa [prefixWord, tailWord_650264, baseEnd_650264] using wordTrace_append hprefix tailTrace_650264
  have hstable : (prefixWord ++ tailWord_650264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650264).length < 2 ^ (prefixWord ++ tailWord_650264).sum := by decide
  have hdescent : baseEnd_650264 < baseStart_650264 := by decide
  rcases family_descends (prefixWord ++ tailWord_650264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650275 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_650275 : Nat := 118140960795 + 650275 * 2 ^ 59
def prefixEnd_650275 : Nat := 4983230072969 + 3 ^ 40 * 650275 * 2
def baseEnd_650275 : Nat := 222602421735032353181297

theorem tailTrace_650275 : CollatzResearch.WordTrace tailWord_650275 prefixEnd_650275 222602421735032353181297 := by
  unfold tailWord_650275
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717477719172207973320279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811651812781471982213519 23717477719172207973320279)
  ·
    refine ⟨35576216578758311959980419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23717477719172207973320279 35576216578758311959980419)
    ·
      refine ⟨53364324868137467939970629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35576216578758311959980419 53364324868137467939970629)
      ·
        refine ⟨10005810912775775238744493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53364324868137467939970629 10005810912775775238744493)
        ·
          refine ⟨3752179092290915714529185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10005810912775775238744493 3752179092290915714529185)
          ·
            refine ⟨2814134319218186785896889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752179092290915714529185 2814134319218186785896889)
            ·
              refine ⟨2110600739413640089422667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814134319218186785896889 2110600739413640089422667)
              ·
                refine ⟨3165901109120460134134001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110600739413640089422667 3165901109120460134134001)
                ·
                  refine ⟨2374425831840345100600501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165901109120460134134001 2374425831840345100600501)
                  ·
                    refine ⟨222602421735032353181297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2374425831840345100600501 222602421735032353181297)
                    ·
                      rfl

theorem cell22_650275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_650275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650275 prefixEnd_650275 := by exact prefixLift 650275
  have htrace : WordTrace (prefixWord ++ tailWord_650275) baseStart_650275 baseEnd_650275 := by
    simpa [prefixWord, tailWord_650275, baseEnd_650275] using wordTrace_append hprefix tailTrace_650275
  have hstable : (prefixWord ++ tailWord_650275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650275).length < 2 ^ (prefixWord ++ tailWord_650275).sum := by decide
  have hdescent : baseEnd_650275 < baseStart_650275 := by decide
  rcases family_descends (prefixWord ++ tailWord_650275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650277 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 5]
def baseStart_650277 : Nat := 118140960795 + 650277 * 2 ^ 59
def prefixEnd_650277 : Nat := 4983230072969 + 3 ^ 40 * 650277 * 2
def baseEnd_650277 : Nat := 74201035458635004877097

theorem tailTrace_650277 : CollatzResearch.WordTrace tailWord_650277 prefixEnd_650277 74201035458635004877097 := by
  unfold tailWord_650277
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717550665164962314893085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15811700443443308209928723 23717550665164962314893085)
  ·
    refine ⟨8894081499436860868084907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23717550665164962314893085 8894081499436860868084907)
    ·
      refine ⟨13341122249155291302127361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8894081499436860868084907 13341122249155291302127361)
      ·
        refine ⟨10005841686866468476595521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13341122249155291302127361 10005841686866468476595521)
        ·
          refine ⟨7504381265149851357446641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10005841686866468476595521 7504381265149851357446641)
          ·
            refine ⟨5628285948862388518084981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7504381265149851357446641 5628285948862388518084981)
            ·
              refine ⟨527651807705848923570467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5628285948862388518084981 527651807705848923570467)
              ·
                refine ⟨791477711558773385355701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527651807705848923570467 791477711558773385355701)
                ·
                  refine ⟨74201035458635004877097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791477711558773385355701 74201035458635004877097)
                  ·
                    rfl

theorem cell22_650277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_650277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650277 prefixEnd_650277 := by exact prefixLift 650277
  have htrace : WordTrace (prefixWord ++ tailWord_650277) baseStart_650277 baseEnd_650277 := by
    simpa [prefixWord, tailWord_650277, baseEnd_650277] using wordTrace_append hprefix tailTrace_650277
  have hstable : (prefixWord ++ tailWord_650277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650277).length < 2 ^ (prefixWord ++ tailWord_650277).sum := by decide
  have hdescent : baseEnd_650277 < baseStart_650277 := by decide
  rcases family_descends (prefixWord ++ tailWord_650277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650322 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_650322 : Nat := 118140960795 + 650322 * 2 ^ 59
def prefixEnd_650322 : Nat := 4983230072969 + 3 ^ 40 * 650322 * 2
def baseEnd_650322 : Nat := 74206170265179965752051

theorem tailTrace_650322 : CollatzResearch.WordTrace tailWord_650322 prefixEnd_650322 74206170265179965752051 := by
  unfold tailWord_650322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929797987500483750070305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15812794633334623333520813 5929797987500483750070305)
  ·
    refine ⟨4447348490625362812552729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5929797987500483750070305 4447348490625362812552729)
    ·
      refine ⟨3335511367969022109414547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4447348490625362812552729 3335511367969022109414547)
      ·
        refine ⟨5003267051953533164121821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3335511367969022109414547 5003267051953533164121821)
        ·
          refine ⟨1876225144482574936545683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5003267051953533164121821 1876225144482574936545683)
          ·
            refine ⟨2814337716723862404818525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876225144482574936545683 2814337716723862404818525)
            ·
              refine ⟨1055376643771448401806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814337716723862404818525 1055376643771448401806947)
              ·
                refine ⟨1583064965657172602710421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055376643771448401806947 1583064965657172602710421)
                ·
                  refine ⟨74206170265179965752051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1583064965657172602710421 74206170265179965752051)
                  ·
                    rfl

theorem cell22_650322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_650322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650322 prefixEnd_650322 := by exact prefixLift 650322
  have htrace : WordTrace (prefixWord ++ tailWord_650322) baseStart_650322 baseEnd_650322 := by
    simpa [prefixWord, tailWord_650322, baseEnd_650322] using wordTrace_append hprefix tailTrace_650322
  have hstable : (prefixWord ++ tailWord_650322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650322).length < 2 ^ (prefixWord ++ tailWord_650322).sum := by decide
  have hdescent : baseEnd_650322 < baseStart_650322 := by decide
  rcases family_descends (prefixWord ++ tailWord_650322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650335 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_650335 : Nat := 118140960795 + 650335 * 2 ^ 59
def prefixEnd_650335 : Nat := 4983230072969 + 3 ^ 40 * 650335 * 2
def baseEnd_650335 : Nat := 222622960961212196681113

theorem tailTrace_650335 : CollatzResearch.WordTrace tailWord_650335 prefixEnd_650335 222622960961212196681113 := by
  unfold tailWord_650335
  simp only [CollatzResearch.WordTrace]
  refine ⟨23719666098954838220504459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15813110732636558813669639 23719666098954838220504459)
  ·
    refine ⟨35579499148432257330756689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23719666098954838220504459 35579499148432257330756689)
    ·
      refine ⟨26684624361324192998067517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35579499148432257330756689 26684624361324192998067517)
      ·
        refine ⟨10006734135496572374275319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26684624361324192998067517 10006734135496572374275319)
        ·
          refine ⟨15010101203244858561412979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006734135496572374275319 15010101203244858561412979)
          ·
            refine ⟨22515151804867287842119469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15010101203244858561412979 22515151804867287842119469)
            ·
              refine ⟨8443181926825232940794801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22515151804867287842119469 8443181926825232940794801)
              ·
                refine ⟨6332386445118924705596101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443181926825232940794801 6332386445118924705596101)
                ·
                  refine ⟨1187322458459798382299269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6332386445118924705596101 1187322458459798382299269)
                  ·
                    refine ⟨222622960961212196681113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1187322458459798382299269 222622960961212196681113)
                    ·
                      rfl

theorem cell22_650335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_650335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650335 prefixEnd_650335 := by exact prefixLift 650335
  have htrace : WordTrace (prefixWord ++ tailWord_650335) baseStart_650335 baseEnd_650335 := by
    simpa [prefixWord, tailWord_650335, baseEnd_650335] using wordTrace_append hprefix tailTrace_650335
  have hstable : (prefixWord ++ tailWord_650335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650335).length < 2 ^ (prefixWord ++ tailWord_650335).sum := by decide
  have hdescent : baseEnd_650335 < baseStart_650335 := by decide
  rcases family_descends (prefixWord ++ tailWord_650335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650352 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_650352 : Nat := 118140960795 + 650352 * 2 ^ 59
def prefixEnd_650352 : Nat := 4983230072969 + 3 ^ 40 * 650352 * 2
def baseEnd_650352 : Nat := 222628780408629819006061

theorem tailTrace_650352 : CollatzResearch.WordTrace tailWord_650352 prefixEnd_650352 222628780408629819006061 := by
  unfold tailWord_650352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860143069946625061936655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15813524093262166749248873 11860143069946625061936655)
  ·
    refine ⟨17790214604919937592904983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11860143069946625061936655 17790214604919937592904983)
    ·
      refine ⟨26685321907379906389357475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17790214604919937592904983 26685321907379906389357475)
      ·
        refine ⟨40027982861069859584036213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26685321907379906389357475 40027982861069859584036213)
        ·
          refine ⟨3752623393225299336003395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40027982861069859584036213 3752623393225299336003395)
          ·
            refine ⟨5628935089837949004005093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752623393225299336003395 5628935089837949004005093)
            ·
              refine ⟨1055425329344615438250955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5628935089837949004005093 1055425329344615438250955)
              ·
                refine ⟨1583137994016923157376433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055425329344615438250955 1583137994016923157376433)
                ·
                  refine ⟨1187353495512692368032325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583137994016923157376433 1187353495512692368032325)
                  ·
                    refine ⟨222628780408629819006061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1187353495512692368032325 222628780408629819006061)
                    ·
                      rfl

theorem cell22_650352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_650352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650352 prefixEnd_650352 := by exact prefixLift 650352
  have htrace : WordTrace (prefixWord ++ tailWord_650352) baseStart_650352 baseEnd_650352 := by
    simpa [prefixWord, tailWord_650352, baseEnd_650352] using wordTrace_append hprefix tailTrace_650352
  have hstable : (prefixWord ++ tailWord_650352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650352).length < 2 ^ (prefixWord ++ tailWord_650352).sum := by decide
  have hdescent : baseEnd_650352 < baseStart_650352 := by decide
  rcases family_descends (prefixWord ++ tailWord_650352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650373 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 4]
def baseStart_650373 : Nat := 118140960795 + 650373 * 2 ^ 59
def prefixEnd_650373 : Nat := 4983230072969 + 3 ^ 40 * 650373 * 2
def baseEnd_650373 : Nat := 74211989712597588076999

theorem tailTrace_650373 : CollatzResearch.WordTrace tailWord_650373 prefixEnd_650373 74211989712597588076999 := by
  unfold tailWord_650373
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721052072817170710387773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15814034715211447140258515 23721052072817170710387773)
  ·
    refine ⟨8895394527306439016395415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23721052072817170710387773 8895394527306439016395415)
    ·
      refine ⟨13343091790959658524593123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895394527306439016395415 13343091790959658524593123)
      ·
        refine ⟨20014637686439487786889685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13343091790959658524593123 20014637686439487786889685)
        ·
          refine ⟨469093070775925495005227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20014637686439487786889685 469093070775925495005227)
          ·
            refine ⟨703639606163888242507841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469093070775925495005227 703639606163888242507841)
            ·
              refine ⟨527729704622916181880881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703639606163888242507841 527729704622916181880881)
              ·
                refine ⟨395797278467187136410661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527729704622916181880881 395797278467187136410661)
                ·
                  refine ⟨74211989712597588076999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395797278467187136410661 74211989712597588076999)
                  ·
                    rfl

theorem cell22_650373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_650373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650373 prefixEnd_650373 := by exact prefixLift 650373
  have htrace : WordTrace (prefixWord ++ tailWord_650373) baseStart_650373 baseEnd_650373 := by
    simpa [prefixWord, tailWord_650373, baseEnd_650373] using wordTrace_append hprefix tailTrace_650373
  have hstable : (prefixWord ++ tailWord_650373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650373).length < 2 ^ (prefixWord ++ tailWord_650373).sum := by decide
  have hdescent : baseEnd_650373 < baseStart_650373 := by decide
  rcases family_descends (prefixWord ++ tailWord_650373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650422 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_650422 : Nat := 118140960795 + 650422 * 2 ^ 59
def prefixEnd_650422 : Nat := 4983230072969 + 3 ^ 40 * 650422 * 2
def baseEnd_650422 : Nat := 222652742839172969755847

theorem tailTrace_650422 : CollatzResearch.WordTrace tailWord_650422 prefixEnd_650422 222652742839172969755847 := by
  unfold tailWord_650422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482677453102478254932595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15815226166426434719281013 1482677453102478254932595)
  ·
    refine ⟨2224016179653717382398893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482677453102478254932595 2224016179653717382398893)
    ·
      refine ⟨834006067370144018399585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2224016179653717382398893 834006067370144018399585)
      ·
        refine ⟨625504550527608013799689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834006067370144018399585 625504550527608013799689)
        ·
          refine ⟨469128412895706010349767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625504550527608013799689 469128412895706010349767)
          ·
            refine ⟨703692619343559015524651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469128412895706010349767 703692619343559015524651)
            ·
              refine ⟨1055538929015338523286977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703692619343559015524651 1055538929015338523286977)
              ·
                refine ⟨791654196761503892465233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055538929015338523286977 791654196761503892465233)
                ·
                  refine ⟨593740647571127919348925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791654196761503892465233 593740647571127919348925)
                  ·
                    refine ⟨222652742839172969755847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593740647571127919348925 222652742839172969755847)
                    ·
                      rfl

theorem cell22_650422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_650422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650422 prefixEnd_650422 := by exact prefixLift 650422
  have htrace : WordTrace (prefixWord ++ tailWord_650422) baseStart_650422 baseEnd_650422 := by
    simpa [prefixWord, tailWord_650422, baseEnd_650422] using wordTrace_append hprefix tailTrace_650422
  have hstable : (prefixWord ++ tailWord_650422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650422).length < 2 ^ (prefixWord ++ tailWord_650422).sum := by decide
  have hdescent : baseEnd_650422 < baseStart_650422 := by decide
  rcases family_descends (prefixWord ++ tailWord_650422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650433 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_650433 : Nat := 118140960795 + 650433 * 2 ^ 59
def prefixEnd_650433 : Nat := 4983230072969 + 3 ^ 40 * 650433 * 2
def baseEnd_650433 : Nat := 222656508363972607730813

theorem tailTrace_650433 : CollatzResearch.WordTrace tailWord_650433 prefixEnd_650433 222656508363972607730813 := by
  unfold tailWord_650433
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723240452599800957571953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15815493635066533971714635 23723240452599800957571953)
  ·
    refine ⟨17792430339449850718178965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23723240452599800957571953 17792430339449850718178965)
    ·
      refine ⟨834020172161711752414639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17792430339449850718178965 834020172161711752414639)
      ·
        refine ⟨1251030258242567628621959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834020172161711752414639 1251030258242567628621959)
        ·
          refine ⟨1876545387363851442932939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251030258242567628621959 1876545387363851442932939)
          ·
            refine ⟨2814818081045777164399409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876545387363851442932939 2814818081045777164399409)
            ·
              refine ⟨2111113560784332873299557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814818081045777164399409 2111113560784332873299557)
              ·
                refine ⟨395833792647062413743667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2111113560784332873299557 395833792647062413743667)
                ·
                  refine ⟨593750688970593620615501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395833792647062413743667 593750688970593620615501)
                  ·
                    refine ⟨222656508363972607730813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593750688970593620615501 222656508363972607730813)
                    ·
                      rfl

theorem cell22_650433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_650433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650433 prefixEnd_650433 := by exact prefixLift 650433
  have htrace : WordTrace (prefixWord ++ tailWord_650433) baseStart_650433 baseEnd_650433 := by
    simpa [prefixWord, tailWord_650433, baseEnd_650433] using wordTrace_append hprefix tailTrace_650433
  have hstable : (prefixWord ++ tailWord_650433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650433).length < 2 ^ (prefixWord ++ tailWord_650433).sum := by decide
  have hdescent : baseEnd_650433 < baseStart_650433 := by decide
  rcases family_descends (prefixWord ++ tailWord_650433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650446 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_650446 : Nat := 118140960795 + 650446 * 2 ^ 59
def prefixEnd_650446 : Nat := 4983230072969 + 3 ^ 40 * 650446 * 2
def baseEnd_650446 : Nat := 74220319509881635718591

theorem tailTrace_650446 : CollatzResearch.WordTrace tailWord_650446 prefixEnd_650446 74220319509881635718591 := by
  unfold tailWord_650446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965464325194088022224399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15815809734368469451863461 2965464325194088022224399)
  ·
    refine ⟨4448196487791132033336599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965464325194088022224399 4448196487791132033336599)
    ·
      refine ⟨6672294731686698050004899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448196487791132033336599 6672294731686698050004899)
      ·
        refine ⟨10008442097530047075007349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672294731686698050004899 10008442097530047075007349)
        ·
          refine ⟨938291446643441913281939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10008442097530047075007349 938291446643441913281939)
          ·
            refine ⟨1407437169965162869922909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938291446643441913281939 1407437169965162869922909)
            ·
              refine ⟨527788938736936076221091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1407437169965162869922909 527788938736936076221091)
              ·
                refine ⟨791683408105404114331637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527788938736936076221091 791683408105404114331637)
                ·
                  refine ⟨74220319509881635718591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791683408105404114331637 74220319509881635718591)
                  ·
                    rfl

theorem cell22_650446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_650446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650446 prefixEnd_650446 := by exact prefixLift 650446
  have htrace : WordTrace (prefixWord ++ tailWord_650446) baseStart_650446 baseEnd_650446 := by
    simpa [prefixWord, tailWord_650446, baseEnd_650446] using wordTrace_append hprefix tailTrace_650446
  have hstable : (prefixWord ++ tailWord_650446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650446).length < 2 ^ (prefixWord ++ tailWord_650446).sum := by decide
  have hdescent : baseEnd_650446 < baseStart_650446 := by decide
  rcases family_descends (prefixWord ++ tailWord_650446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650472 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_650472 : Nat := 118140960795 + 650472 * 2 ^ 59
def prefixEnd_650472 : Nat := 4983230072969 + 3 ^ 40 * 650472 * 2
def baseEnd_650472 : Nat := 222669858860989506005693

theorem tailTrace_650472 : CollatzResearch.WordTrace tailWord_650472 prefixEnd_650472 222669858860989506005693 := by
  unfold tailWord_650472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862331449729255309120835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15816441932972340412161113 11862331449729255309120835)
  ·
    refine ⟨17793497174593882963681253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11862331449729255309120835 17793497174593882963681253)
    ·
      refine ⟨3336280720236353055690235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17793497174593882963681253 3336280720236353055690235)
      ·
        refine ⟨5004421080354529583535353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336280720236353055690235 5004421080354529583535353)
        ·
          refine ⟨3753315810265897187651515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5004421080354529583535353 3753315810265897187651515)
          ·
            refine ⟨5629973715398845781477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753315810265897187651515 5629973715398845781477273)
            ·
              refine ⟨4222480286549134336107955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5629973715398845781477273 4222480286549134336107955)
              ·
                refine ⟨6333720429823701504161933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222480286549134336107955 6333720429823701504161933)
                ·
                  refine ⟨2375145161183888064060725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6333720429823701504161933 2375145161183888064060725)
                  ·
                    refine ⟨222669858860989506005693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2375145161183888064060725 222669858860989506005693)
                    ·
                      rfl

theorem cell22_650472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_650472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650472 prefixEnd_650472 := by exact prefixLift 650472
  have htrace : WordTrace (prefixWord ++ tailWord_650472) baseStart_650472 baseEnd_650472 := by
    simpa [prefixWord, tailWord_650472, baseEnd_650472] using wordTrace_append hprefix tailTrace_650472
  have hstable : (prefixWord ++ tailWord_650472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650472).length < 2 ^ (prefixWord ++ tailWord_650472).sum := by decide
  have hdescent : baseEnd_650472 < baseStart_650472 := by decide
  rcases family_descends (prefixWord ++ tailWord_650472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650484 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_650484 : Nat := 118140960795 + 650484 * 2 ^ 59
def prefixEnd_650484 : Nat := 4983230072969 + 3 ^ 40 * 650484 * 2
def baseEnd_650484 : Nat := 222673966706225474705657

theorem tailTrace_650484 : CollatzResearch.WordTrace tailWord_650484 prefixEnd_650484 222673966706225474705657 := by
  unfold tailWord_650484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862550287707518333839253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15816733716943357778452337 11862550287707518333839253)
  ·
    refine ⟨556057044736289921898715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11862550287707518333839253 556057044736289921898715)
    ·
      refine ⟨834085567104434882848073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556057044736289921898715 834085567104434882848073)
      ·
        refine ⟨625564175328326162136055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834085567104434882848073 625564175328326162136055)
        ·
          refine ⟨938346262992489243204083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625564175328326162136055 938346262992489243204083)
          ·
            refine ⟨1407519394488733864806125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938346262992489243204083 1407519394488733864806125)
            ·
              refine ⟨527819772933275199302297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1407519394488733864806125 527819772933275199302297)
              ·
                refine ⟨395864829699956399476723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527819772933275199302297 395864829699956399476723)
                ·
                  refine ⟨593797244549934599215085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395864829699956399476723 593797244549934599215085)
                  ·
                    refine ⟨222673966706225474705657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593797244549934599215085 222673966706225474705657)
                    ·
                      rfl

theorem cell22_650484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_650484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650484 prefixEnd_650484 := by exact prefixLift 650484
  have htrace : WordTrace (prefixWord ++ tailWord_650484) baseStart_650484 baseEnd_650484 := by
    simpa [prefixWord, tailWord_650484, baseEnd_650484] using wordTrace_append hprefix tailTrace_650484
  have hstable : (prefixWord ++ tailWord_650484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650484).length < 2 ^ (prefixWord ++ tailWord_650484).sum := by decide
  have hdescent : baseEnd_650484 < baseStart_650484 := by decide
  rcases family_descends (prefixWord ++ tailWord_650484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650487 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_650487 : Nat := 118140960795 + 650487 * 2 ^ 59
def prefixEnd_650487 : Nat := 4983230072969 + 3 ^ 40 * 650487 * 2
def baseEnd_650487 : Nat := 222674993667534466880647

theorem tailTrace_650487 : CollatzResearch.WordTrace tailWord_650487 prefixEnd_650487 222674993667534466880647 := by
  unfold tailWord_650487
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725209994404168180037715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15816806662936112120025143 23725209994404168180037715)
  ·
    refine ⟨35587814991606252270056573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725209994404168180037715 35587814991606252270056573)
    ·
      refine ⟨13345430621852344601271215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35587814991606252270056573 13345430621852344601271215)
      ·
        refine ⟨20018145932778516901906823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13345430621852344601271215 20018145932778516901906823)
        ·
          refine ⟨30027218899167775352860235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20018145932778516901906823 30027218899167775352860235)
          ·
            refine ⟨45040828348751663029290353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30027218899167775352860235 45040828348751663029290353)
            ·
              refine ⟨33780621261563747271967765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45040828348751663029290353 33780621261563747271967765)
              ·
                refine ⟨1583466621635800653373489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33780621261563747271967765 1583466621635800653373489)
                ·
                  refine ⟨1187599966226850490030117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583466621635800653373489 1187599966226850490030117)
                  ·
                    refine ⟨222674993667534466880647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1187599966226850490030117 222674993667534466880647)
                    ·
                      rfl

theorem cell22_650487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_650487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650487 prefixEnd_650487 := by exact prefixLift 650487
  have htrace : WordTrace (prefixWord ++ tailWord_650487) baseStart_650487 baseEnd_650487 := by
    simpa [prefixWord, tailWord_650487, baseEnd_650487] using wordTrace_append hprefix tailTrace_650487
  have hstable : (prefixWord ++ tailWord_650487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650487).length < 2 ^ (prefixWord ++ tailWord_650487).sum := by decide
  have hdescent : baseEnd_650487 < baseStart_650487 := by decide
  rcases family_descends (prefixWord ++ tailWord_650487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650489 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_650489 : Nat := 118140960795 + 650489 * 2 ^ 59
def prefixEnd_650489 : Nat := 4983230072969 + 3 ^ 40 * 650489 * 2
def baseEnd_650489 : Nat := 222675678308407128330641

theorem tailTrace_650489 : CollatzResearch.WordTrace tailWord_650489 prefixEnd_650489 222675678308407128330641 := by
  unfold tailWord_650489
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725282940396922521610521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15816855293597948347740347 23725282940396922521610521)
  ·
    refine ⟨17793962205297691891207891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23725282940396922521610521 17793962205297691891207891)
    ·
      refine ⟨26690943307946537836811837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17793962205297691891207891 26690943307946537836811837)
      ·
        refine ⟨10009103740479951688804439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26690943307946537836811837 10009103740479951688804439)
        ·
          refine ⟨15013655610719927533206659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009103740479951688804439 15013655610719927533206659)
          ·
            refine ⟨22520483416079891299809989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15013655610719927533206659 22520483416079891299809989)
            ·
              refine ⟨4222590640514979618714373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22520483416079891299809989 4222590640514979618714373)
              ·
                refine ⟨791735745096558678508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4222590640514979618714373 791735745096558678508945)
                ·
                  refine ⟨593801808822419008881709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791735745096558678508945 593801808822419008881709)
                  ·
                    refine ⟨222675678308407128330641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593801808822419008881709 222675678308407128330641)
                    ·
                      rfl

theorem cell22_650489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_650489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650489 prefixEnd_650489 := by exact prefixLift 650489
  have htrace : WordTrace (prefixWord ++ tailWord_650489) baseStart_650489 baseEnd_650489 := by
    simpa [prefixWord, tailWord_650489, baseEnd_650489] using wordTrace_append hprefix tailTrace_650489
  have hstable : (prefixWord ++ tailWord_650489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650489).length < 2 ^ (prefixWord ++ tailWord_650489).sum := by decide
  have hdescent : baseEnd_650489 < baseStart_650489 := by decide
  rcases family_descends (prefixWord ++ tailWord_650489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650686 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_650686 : Nat := 118140960795 + 650686 * 2 ^ 59
def prefixEnd_650686 : Nat := 4983230072969 + 3 ^ 40 * 650686 * 2
def baseEnd_650686 : Nat := 222743115434364281155037

theorem tailTrace_650686 : CollatzResearch.WordTrace tailWord_650686 prefixEnd_650686 222743115434364281155037 := by
  unfold tailWord_650686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966558515085403145816489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15821645413788816777687941 2966558515085403145816489)
  ·
    refine ⟨2224918886314052359362367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2966558515085403145816489 2224918886314052359362367)
    ·
      refine ⟨3337378329471078539043551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224918886314052359362367 3337378329471078539043551)
      ·
        refine ⟨5006067494206617808565327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337378329471078539043551 5006067494206617808565327)
        ·
          refine ⟨7509101241309926712847991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5006067494206617808565327 7509101241309926712847991)
          ·
            refine ⟨11263651861964890069271987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509101241309926712847991 11263651861964890069271987)
            ·
              refine ⟨16895477792947335103907981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11263651861964890069271987 16895477792947335103907981)
              ·
                refine ⟨6335804172355250663965493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16895477792947335103907981 6335804172355250663965493)
                ·
                  refine ⟨593981641158304749746765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6335804172355250663965493 593981641158304749746765)
                  ·
                    refine ⟨222743115434364281155037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593981641158304749746765 222743115434364281155037)
                    ·
                      rfl

theorem cell22_650686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_650686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650686 prefixEnd_650686 := by exact prefixLift 650686
  have htrace : WordTrace (prefixWord ++ tailWord_650686) baseStart_650686 baseEnd_650686 := by
    simpa [prefixWord, tailWord_650686, baseEnd_650686] using wordTrace_append hprefix tailTrace_650686
  have hstable : (prefixWord ++ tailWord_650686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650686).length < 2 ^ (prefixWord ++ tailWord_650686).sum := by decide
  have hdescent : baseEnd_650686 < baseStart_650686 := by decide
  rcases family_descends (prefixWord ++ tailWord_650686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650744 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_650744 : Nat := 118140960795 + 650744 * 2 ^ 59
def prefixEnd_650744 : Nat := 4983230072969 + 3 ^ 40 * 650744 * 2
def baseEnd_650744 : Nat := 74254323339890487734953

theorem tailTrace_650744 : CollatzResearch.WordTrace tailWord_650744 prefixEnd_650744 74254323339890487734953 := by
  unfold tailWord_650744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867291777236550536071643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15823055702982067381428857 11867291777236550536071643)
  ·
    refine ⟨17800937665854825804107465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11867291777236550536071643 17800937665854825804107465)
    ·
      refine ⟨13350703249391119353080599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17800937665854825804107465 13350703249391119353080599)
      ·
        refine ⟨20026054874086679029620899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350703249391119353080599 20026054874086679029620899)
        ·
          refine ⟨30039082311130018544431349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20026054874086679029620899 30039082311130018544431349)
          ·
            refine ⟨2816163966668439238540439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30039082311130018544431349 2816163966668439238540439)
            ·
              refine ⟨4224245950002658857810659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816163966668439238540439 4224245950002658857810659)
              ·
                refine ⟨6336368925003988286715989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224245950002658857810659 6336368925003988286715989)
                ·
                  refine ⟨74254323339890487734953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6336368925003988286715989 74254323339890487734953)
                  ·
                    rfl

theorem cell22_650744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_650744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650744 prefixEnd_650744 := by exact prefixLift 650744
  have htrace : WordTrace (prefixWord ++ tailWord_650744) baseStart_650744 baseEnd_650744 := by
    simpa [prefixWord, tailWord_650744, baseEnd_650744] using wordTrace_append hprefix tailTrace_650744
  have hstable : (prefixWord ++ tailWord_650744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650744).length < 2 ^ (prefixWord ++ tailWord_650744).sum := by decide
  have hdescent : baseEnd_650744 < baseStart_650744 := by decide
  rcases family_descends (prefixWord ++ tailWord_650744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650746 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_650746 : Nat := 118140960795 + 650746 * 2 ^ 59
def prefixEnd_650746 : Nat := 4983230072969 + 3 ^ 40 * 650746 * 2
def baseEnd_650746 : Nat := 222763654660544124654853

theorem tailTrace_650746 : CollatzResearch.WordTrace tailWord_650746 prefixEnd_650746 222763654660544124654853 := by
  unfold tailWord_650746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933664125116463853429023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15823104333643903609144061 5933664125116463853429023)
  ·
    refine ⟨8900496187674695780143535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5933664125116463853429023 8900496187674695780143535)
    ·
      refine ⟨13350744281512043670215303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8900496187674695780143535 13350744281512043670215303)
      ·
        refine ⟨20026116422268065505322955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350744281512043670215303 20026116422268065505322955)
        ·
          refine ⟨30039174633402098257984433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20026116422268065505322955 30039174633402098257984433)
          ·
            refine ⟨22529380975051573693488325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30039174633402098257984433 22529380975051573693488325)
            ·
              refine ⟨4224258932822170067529061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22529380975051573693488325 4224258932822170067529061)
              ·
                refine ⟨792048549904156887661699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4224258932822170067529061 792048549904156887661699)
                ·
                  refine ⟨1188072824856235331492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792048549904156887661699 1188072824856235331492549)
                  ·
                    refine ⟨222763654660544124654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1188072824856235331492549 222763654660544124654853)
                    ·
                      rfl

theorem cell22_650746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_650746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650746 prefixEnd_650746 := by exact prefixLift 650746
  have htrace : WordTrace (prefixWord ++ tailWord_650746) baseStart_650746 baseEnd_650746 := by
    simpa [prefixWord, tailWord_650746, baseEnd_650746] using wordTrace_append hprefix tailTrace_650746
  have hstable : (prefixWord ++ tailWord_650746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650746).length < 2 ^ (prefixWord ++ tailWord_650746).sum := by decide
  have hdescent : baseEnd_650746 < baseStart_650746 := by decide
  rcases family_descends (prefixWord ++ tailWord_650746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650763 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 1, 4]
def baseStart_650763 : Nat := 118140960795 + 650763 * 2 ^ 59
def prefixEnd_650763 : Nat := 4983230072969 + 3 ^ 40 * 650763 * 2
def baseEnd_650763 : Nat := 222769474107961746979801

theorem tailTrace_650763 : CollatzResearch.WordTrace tailWord_650763 prefixEnd_650763 222769474107961746979801 := by
  unfold tailWord_650763
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735276541404267317084943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15823517694269511544723295 23735276541404267317084943)
  ·
    refine ⟨35602914812106400975627415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735276541404267317084943 35602914812106400975627415)
    ·
      refine ⟨53404372218159601463441123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35602914812106400975627415 53404372218159601463441123)
      ·
        refine ⟨80106558327239402195161685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53404372218159601463441123 80106558327239402195161685)
        ·
          refine ⟨938748730397336744474551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 80106558327239402195161685 938748730397336744474551)
          ·
            refine ⟨1408123095596005116711827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938748730397336744474551 1408123095596005116711827)
            ·
              refine ⟨2112184643394007675067741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408123095596005116711827 2112184643394007675067741)
              ·
                refine ⟨792069241272752878150403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2112184643394007675067741 792069241272752878150403)
                ·
                  refine ⟨1188103861909129317225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792069241272752878150403 1188103861909129317225605)
                  ·
                    refine ⟨222769474107961746979801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1188103861909129317225605 222769474107961746979801)
                    ·
                      rfl

theorem cell22_650763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_650763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650763 prefixEnd_650763 := by exact prefixLift 650763
  have htrace : WordTrace (prefixWord ++ tailWord_650763) baseStart_650763 baseEnd_650763 := by
    simpa [prefixWord, tailWord_650763, baseEnd_650763] using wordTrace_append hprefix tailTrace_650763
  have hstable : (prefixWord ++ tailWord_650763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650763).length < 2 ^ (prefixWord ++ tailWord_650763).sum := by decide
  have hdescent : baseEnd_650763 < baseStart_650763 := by decide
  rcases family_descends (prefixWord ++ tailWord_650763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650789 : List Nat := [1, 3, 1, 2, 2, 1, 1, 11]
def baseStart_650789 : Nat := 118140960795 + 650789 * 2 ^ 59
def prefixEnd_650789 : Nat := 4983230072969 + 3 ^ 40 * 650789 * 2
def baseEnd_650789 : Nat := 24753152715478482869969

theorem tailTrace_650789 : CollatzResearch.WordTrace tailWord_650789 prefixEnd_650789 24753152715478482869969 := by
  unfold tailWord_650789
  simp only [CollatzResearch.WordTrace]
  refine ⟨23736224839310073757531421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15824149892873382505020947 23736224839310073757531421)
  ·
    refine ⟨8901084314741277659074283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23736224839310073757531421 8901084314741277659074283)
    ·
      refine ⟨13351626472111916488611425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8901084314741277659074283 13351626472111916488611425)
      ·
        refine ⟨10013719854083937366458569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13351626472111916488611425 10013719854083937366458569)
        ·
          refine ⟨7510289890562953024843927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013719854083937366458569 7510289890562953024843927)
          ·
            refine ⟨11265434835844429537265891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510289890562953024843927 11265434835844429537265891)
            ·
              refine ⟨16898152253766644305898837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265434835844429537265891 16898152253766644305898837)
              ·
                refine ⟨24753152715478482869969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16898152253766644305898837 24753152715478482869969)
                ·
                  rfl

theorem cell22_650789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 11].length) (baseStart_650789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650789 prefixEnd_650789 := by exact prefixLift 650789
  have htrace : WordTrace (prefixWord ++ tailWord_650789) baseStart_650789 baseEnd_650789 := by
    simpa [prefixWord, tailWord_650789, baseEnd_650789] using wordTrace_append hprefix tailTrace_650789
  have hstable : (prefixWord ++ tailWord_650789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650789).length < 2 ^ (prefixWord ++ tailWord_650789).sum := by decide
  have hdescent : baseEnd_650789 < baseStart_650789 := by decide
  rcases family_descends (prefixWord ++ tailWord_650789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650812 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_650812 : Nat := 118140960795 + 650812 * 2 ^ 59
def prefixEnd_650812 : Nat := 4983230072969 + 3 ^ 40 * 650812 * 2
def baseEnd_650812 : Nat := 74262082603113984168217

theorem tailTrace_650812 : CollatzResearch.WordTrace tailWord_650812 prefixEnd_650812 74262082603113984168217 := by
  unfold tailWord_650812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868531859113374342809345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15824709145484499123745793 11868531859113374342809345)
  ·
    refine ⟨8901398894335030757107009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11868531859113374342809345 8901398894335030757107009)
    ·
      refine ⟨6676049170751273067830257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8901398894335030757107009 6676049170751273067830257)
      ·
        refine ⟨5007036878063454800872693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6676049170751273067830257 5007036878063454800872693)
        ·
          refine ⟨469409707318448887581815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5007036878063454800872693 469409707318448887581815)
          ·
            refine ⟨704114560977673331372723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469409707318448887581815 704114560977673331372723)
            ·
              refine ⟨1056171841466509997059085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704114560977673331372723 1056171841466509997059085)
              ·
                refine ⟨396064440549941248897157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056171841466509997059085 396064440549941248897157)
                ·
                  refine ⟨74262082603113984168217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396064440549941248897157 74262082603113984168217)
                  ·
                    rfl

theorem cell22_650812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_650812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650812 prefixEnd_650812 := by exact prefixLift 650812
  have htrace : WordTrace (prefixWord ++ tailWord_650812) baseStart_650812 baseEnd_650812 := by
    simpa [prefixWord, tailWord_650812, baseEnd_650812] using wordTrace_append hprefix tailTrace_650812
  have hstable : (prefixWord ++ tailWord_650812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650812).length < 2 ^ (prefixWord ++ tailWord_650812).sum := by decide
  have hdescent : baseEnd_650812 < baseStart_650812 := by decide
  rcases family_descends (prefixWord ++ tailWord_650812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650819 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_650819 : Nat := 118140960795 + 650819 * 2 ^ 59
def prefixEnd_650819 : Nat := 4983230072969 + 3 ^ 40 * 650819 * 2
def baseEnd_650819 : Nat := 222788644052396267579629

theorem tailTrace_650819 : CollatzResearch.WordTrace tailWord_650819 prefixEnd_650819 222788644052396267579629 := by
  unfold tailWord_650819
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737319029201388881123511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15824879352800925920749007 23737319029201388881123511)
  ·
    refine ⟨35605978543802083321685267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23737319029201388881123511 35605978543802083321685267)
    ·
      refine ⟨53408967815703124982527901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35605978543802083321685267 53408967815703124982527901)
      ·
        refine ⟨20028362930888671868447963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53408967815703124982527901 20028362930888671868447963)
        ·
          refine ⟨30042544396333007802671945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028362930888671868447963 30042544396333007802671945)
          ·
            refine ⟨22531908297249755852003959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30042544396333007802671945 22531908297249755852003959)
            ·
              refine ⟨33797862445874633778005939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22531908297249755852003959 33797862445874633778005939)
              ·
                refine ⟨50696793668811950667008909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33797862445874633778005939 50696793668811950667008909)
                ·
                  refine ⟨19011297625804481500128341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50696793668811950667008909 19011297625804481500128341)
                  ·
                    refine ⟨222788644052396267579629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19011297625804481500128341 222788644052396267579629)
                    ·
                      rfl

theorem cell22_650819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_650819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650819 prefixEnd_650819 := by exact prefixLift 650819
  have htrace : WordTrace (prefixWord ++ tailWord_650819) baseStart_650819 baseEnd_650819 := by
    simpa [prefixWord, tailWord_650819, baseEnd_650819] using wordTrace_append hprefix tailTrace_650819
  have hstable : (prefixWord ++ tailWord_650819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650819).length < 2 ^ (prefixWord ++ tailWord_650819).sum := by decide
  have hdescent : baseEnd_650819 < baseStart_650819 := by decide
  rcases family_descends (prefixWord ++ tailWord_650819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650823 : List Nat := [1, 1, 4, 1, 6, 1, 8]
def baseStart_650823 : Nat := 118140960795 + 650823 * 2 ^ 59
def prefixEnd_650823 : Nat := 4983230072969 + 3 ^ 40 * 650823 * 2
def baseEnd_650823 : Nat := 8251481975338577425171

theorem tailTrace_650823 : CollatzResearch.WordTrace tailWord_650823 prefixEnd_650823 8251481975338577425171 := by
  unfold tailWord_650823
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737464921186897564269123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15824976614124598376179415 23737464921186897564269123)
  ·
    refine ⟨35606197381780346346403685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23737464921186897564269123 35606197381780346346403685)
    ·
      refine ⟨6676162009083814939950691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35606197381780346346403685 6676162009083814939950691)
      ·
        refine ⟨10014243013625722409926037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676162009083814939950691 10014243013625722409926037)
        ·
          refine ⟨469417641263705737965283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10014243013625722409926037 469417641263705737965283)
          ·
            refine ⟨704126461895558606947925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469417641263705737965283 704126461895558606947925)
            ·
              refine ⟨8251481975338577425171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 704126461895558606947925 8251481975338577425171)
              ·
                rfl

theorem cell22_650823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 8].length) (baseStart_650823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650823 prefixEnd_650823 := by exact prefixLift 650823
  have htrace : WordTrace (prefixWord ++ tailWord_650823) baseStart_650823 baseEnd_650823 := by
    simpa [prefixWord, tailWord_650823, baseEnd_650823] using wordTrace_append hprefix tailTrace_650823
  have hstable : (prefixWord ++ tailWord_650823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650823).length < 2 ^ (prefixWord ++ tailWord_650823).sum := by decide
  have hdescent : baseEnd_650823 < baseStart_650823 := by decide
  rcases family_descends (prefixWord ++ tailWord_650823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650836 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_650836 : Nat := 118140960795 + 650836 * 2 ^ 59
def prefixEnd_650836 : Nat := 4983230072969 + 3 ^ 40 * 650836 * 2
def baseEnd_650836 : Nat := 222794463499813889904577

theorem tailTrace_650836 : CollatzResearch.WordTrace tailWord_650836 prefixEnd_650836 222794463499813889904577 := by
  unfold tailWord_650836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11868969535069900392246181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15825292713426533856328241 11868969535069900392246181)
  ·
    refine ⟨2225431787825606323546159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11868969535069900392246181 2225431787825606323546159)
    ·
      refine ⟨3338147681738409485319239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225431787825606323546159 3338147681738409485319239)
      ·
        refine ⟨5007221522607614227978859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338147681738409485319239 5007221522607614227978859)
        ·
          refine ⟨7510832283911421341968289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007221522607614227978859 7510832283911421341968289)
          ·
            refine ⟨5633124212933566006476217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7510832283911421341968289 5633124212933566006476217)
            ·
              refine ⟨4224843159700174504857163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633124212933566006476217 4224843159700174504857163)
              ·
                refine ⟨6337264739550261757285745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224843159700174504857163 6337264739550261757285745)
                ·
                  refine ⟨4752948554662696317964309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337264739550261757285745 4752948554662696317964309)
                  ·
                    refine ⟨222794463499813889904577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4752948554662696317964309 222794463499813889904577)
                    ·
                      rfl

theorem cell22_650836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_650836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650836 prefixEnd_650836 := by exact prefixLift 650836
  have htrace : WordTrace (prefixWord ++ tailWord_650836) baseStart_650836 baseEnd_650836 := by
    simpa [prefixWord, tailWord_650836, baseEnd_650836] using wordTrace_append hprefix tailTrace_650836
  have hstable : (prefixWord ++ tailWord_650836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650836).length < 2 ^ (prefixWord ++ tailWord_650836).sum := by decide
  have hdescent : baseEnd_650836 < baseStart_650836 := by decide
  rcases family_descends (prefixWord ++ tailWord_650836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650900 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_650900 : Nat := 118140960795 + 650900 * 2 ^ 59
def prefixEnd_650900 : Nat := 4983230072969 + 3 ^ 40 * 650900 * 2
def baseEnd_650900 : Nat := 222816372007739056304381

theorem tailTrace_650900 : CollatzResearch.WordTrace tailWord_650900 prefixEnd_650900 222816372007739056304381 := by
  unfold tailWord_650900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870136670953969857411077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15826848894605293143214769 11870136670953969857411077)
  ·
    refine ⟨2225650625803869348264577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11870136670953969857411077 2225650625803869348264577)
    ·
      refine ⟨1669237969352902011198433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2225650625803869348264577 1669237969352902011198433)
      ·
        refine ⟨1251928477014676508398825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1669237969352902011198433 1251928477014676508398825)
        ·
          refine ⟨938946357761007381299119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251928477014676508398825 938946357761007381299119)
          ·
            refine ⟨1408419536641511071948679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938946357761007381299119 1408419536641511071948679)
            ·
              refine ⟨2112629304962266607923019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408419536641511071948679 2112629304962266607923019)
              ·
                refine ⟨3168943957443399911884529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112629304962266607923019 3168943957443399911884529)
                ·
                  refine ⟨2376707968082549933913397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168943957443399911884529 2376707968082549933913397)
                  ·
                    refine ⟨222816372007739056304381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2376707968082549933913397 222816372007739056304381)
                    ·
                      rfl

theorem cell22_650900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_650900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650900 prefixEnd_650900 := by exact prefixLift 650900
  have htrace : WordTrace (prefixWord ++ tailWord_650900) baseStart_650900 baseEnd_650900 := by
    simpa [prefixWord, tailWord_650900, baseEnd_650900] using wordTrace_append hprefix tailTrace_650900
  have hstable : (prefixWord ++ tailWord_650900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650900).length < 2 ^ (prefixWord ++ tailWord_650900).sum := by decide
  have hdescent : baseEnd_650900 < baseStart_650900 := by decide
  rcases family_descends (prefixWord ++ tailWord_650900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650913 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 6]
def baseStart_650913 : Nat := 118140960795 + 650913 * 2 ^ 59
def prefixEnd_650913 : Nat := 4983230072969 + 3 ^ 40 * 650913 * 2
def baseEnd_650913 : Nat := 74273607391137118576447

theorem tailTrace_650913 : CollatzResearch.WordTrace tailWord_650913 prefixEnd_650913 74273607391137118576447 := by
  unfold tailWord_650913
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740747490860842935045393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15827164993907228623363595 23740747490860842935045393)
  ·
    refine ⟨17805560618145632201284045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23740747490860842935045393 17805560618145632201284045)
    ·
      refine ⟨6677085231804612075481517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17805560618145632201284045 6677085231804612075481517)
      ·
        refine ⟨2503906961926729528305569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6677085231804612075481517 2503906961926729528305569)
        ·
          refine ⟨1877930221445047146229177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503906961926729528305569 1877930221445047146229177)
          ·
            refine ⟨1408447666083785359671883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1877930221445047146229177 1408447666083785359671883)
            ·
              refine ⟨2112671499125678039507825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408447666083785359671883 2112671499125678039507825)
              ·
                refine ⟨1584503624344258529630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112671499125678039507825 1584503624344258529630869)
                ·
                  refine ⟨74273607391137118576447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1584503624344258529630869 74273607391137118576447)
                  ·
                    rfl

theorem cell22_650913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_650913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650913 prefixEnd_650913 := by exact prefixLift 650913
  have htrace : WordTrace (prefixWord ++ tailWord_650913) baseStart_650913 baseEnd_650913 := by
    simpa [prefixWord, tailWord_650913, baseEnd_650913] using wordTrace_append hprefix tailTrace_650913
  have hstable : (prefixWord ++ tailWord_650913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650913).length < 2 ^ (prefixWord ++ tailWord_650913).sum := by decide
  have hdescent : baseEnd_650913 < baseStart_650913 := by decide
  rcases family_descends (prefixWord ++ tailWord_650913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650941 : List Nat := [1, 4, 1, 2, 1, 2, 11]
def baseStart_650941 : Nat := 118140960795 + 650941 * 2 ^ 59
def prefixEnd_650941 : Nat := 4983230072969 + 3 ^ 40 * 650941 * 2
def baseEnd_650941 : Nat := 8252978042430689482565

theorem tailTrace_650941 : CollatzResearch.WordTrace tailWord_650941 prefixEnd_650941 8252978042430689482565 := by
  unfold tailWord_650941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23741768734759403717064677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15827845823172935811376451 23741768734759403717064677)
  ·
    refine ⟨4451581637767388196949627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23741768734759403717064677 4451581637767388196949627)
    ·
      refine ⟨6677372456651082295424441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451581637767388196949627 6677372456651082295424441)
      ·
        refine ⟨5008029342488311721568331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6677372456651082295424441 5008029342488311721568331)
        ·
          refine ⟨7512044013732467582352497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008029342488311721568331 7512044013732467582352497)
          ·
            refine ⟨5634033010299350686764373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512044013732467582352497 5634033010299350686764373)
            ·
              refine ⟨8252978042430689482565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5634033010299350686764373 8252978042430689482565)
              ·
                rfl

theorem cell22_650941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 11].length) (baseStart_650941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_650941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_650941 prefixEnd_650941 := by exact prefixLift 650941
  have htrace : WordTrace (prefixWord ++ tailWord_650941) baseStart_650941 baseEnd_650941 := by
    simpa [prefixWord, tailWord_650941, baseEnd_650941] using wordTrace_append hprefix tailTrace_650941
  have hstable : (prefixWord ++ tailWord_650941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650941).length < 2 ^ (prefixWord ++ tailWord_650941).sum := by decide
  have hdescent : baseEnd_650941 < baseStart_650941 := by decide
  rcases family_descends (prefixWord ++ tailWord_650941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651020 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_651020 : Nat := 118140960795 + 651020 * 2 ^ 59
def prefixEnd_651020 : Nat := 4983230072969 + 3 ^ 40 * 651020 * 2
def baseEnd_651020 : Nat := 74285816820032914434671

theorem tailTrace_651020 : CollatzResearch.WordTrace tailWord_651020 prefixEnd_651020 74285816820032914434671 := by
  unfold tailWord_651020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872325050736600104595257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15829766734315466806127009 11872325050736600104595257)
  ·
    refine ⟨8904243788052450078446443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11872325050736600104595257 8904243788052450078446443)
    ·
      refine ⟨13356365682078675117669665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904243788052450078446443 13356365682078675117669665)
      ·
        refine ⟨10017274261559006338252249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13356365682078675117669665 10017274261559006338252249)
        ·
          refine ⟨7512955696169254753689187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10017274261559006338252249 7512955696169254753689187)
          ·
            refine ⟨11269433544253882130533781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512955696169254753689187 11269433544253882130533781)
            ·
              refine ⟨528254697386900724868771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11269433544253882130533781 528254697386900724868771)
              ·
                refine ⟨792382046080351087303157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528254697386900724868771 792382046080351087303157)
                ·
                  refine ⟨74285816820032914434671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792382046080351087303157 74285816820032914434671)
                  ·
                    rfl

theorem cell22_651020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_651020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651020 prefixEnd_651020 := by exact prefixLift 651020
  have htrace : WordTrace (prefixWord ++ tailWord_651020) baseStart_651020 baseEnd_651020 := by
    simpa [prefixWord, tailWord_651020, baseEnd_651020] using wordTrace_append hprefix tailTrace_651020
  have hstable : (prefixWord ++ tailWord_651020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651020).length < 2 ^ (prefixWord ++ tailWord_651020).sum := by decide
  have hdescent : baseEnd_651020 < baseStart_651020 := by decide
  rcases family_descends (prefixWord ++ tailWord_651020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651080 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_651080 : Nat := 118140960795 + 651080 * 2 ^ 59
def prefixEnd_651080 : Nat := 4983230072969 + 3 ^ 40 * 651080 * 2
def baseEnd_651080 : Nat := 222877989686278586803829

theorem tailTrace_651080 : CollatzResearch.WordTrace tailWord_651080 prefixEnd_651080 222877989686278586803829 := by
  unfold tailWord_651080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873419240627915228187347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15831225654170553637583129 11873419240627915228187347)
  ·
    refine ⟨17810128860941872842281021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873419240627915228187347 17810128860941872842281021)
    ·
      refine ⟨6678798322853202315855383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17810128860941872842281021 6678798322853202315855383)
      ·
        refine ⟨10018197484279803473783075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678798322853202315855383 10018197484279803473783075)
        ·
          refine ⟨15027296226419705210674613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10018197484279803473783075 15027296226419705210674613)
          ·
            refine ⟨1408809021226847363500745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15027296226419705210674613 1408809021226847363500745)
            ·
              refine ⟨1056606765920135522625559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408809021226847363500745 1056606765920135522625559)
              ·
                refine ⟨1584910148880203283938339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056606765920135522625559 1584910148880203283938339)
                ·
                  refine ⟨2377365223320304925907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584910148880203283938339 2377365223320304925907509)
                  ·
                    refine ⟨222877989686278586803829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2377365223320304925907509 222877989686278586803829)
                    ·
                      rfl

theorem cell22_651080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_651080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651080 prefixEnd_651080 := by exact prefixLift 651080
  have htrace : WordTrace (prefixWord ++ tailWord_651080) baseStart_651080 baseEnd_651080 := by
    simpa [prefixWord, tailWord_651080, baseEnd_651080] using wordTrace_append hprefix tailTrace_651080
  have hstable : (prefixWord ++ tailWord_651080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651080).length < 2 ^ (prefixWord ++ tailWord_651080).sum := by decide
  have hdescent : baseEnd_651080 < baseStart_651080 := by decide
  rcases family_descends (prefixWord ++ tailWord_651080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651095 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_651095 : Nat := 118140960795 + 651095 * 2 ^ 59
def prefixEnd_651095 : Nat := 4983230072969 + 3 ^ 40 * 651095 * 2
def baseEnd_651095 : Nat := 222883124492823547678783

theorem tailTrace_651095 : CollatzResearch.WordTrace tailWord_651095 prefixEnd_651095 222883124492823547678783 := by
  unfold tailWord_651095
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747385576201488018170739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15831590384134325345447159 23747385576201488018170739)
  ·
    refine ⟨35621078364302232027256109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23747385576201488018170739 35621078364302232027256109)
    ·
      refine ⟨13357904386613337010221041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35621078364302232027256109 13357904386613337010221041)
      ·
        refine ⟨10018428289960002757665781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13357904386613337010221041 10018428289960002757665781)
        ·
          refine ⟨939227652183750258531167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10018428289960002757665781 939227652183750258531167)
          ·
            refine ⟨1408841478275625387796751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939227652183750258531167 1408841478275625387796751)
            ·
              refine ⟨2113262217413438081695127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408841478275625387796751 2113262217413438081695127)
              ·
                refine ⟨3169893326120157122542691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113262217413438081695127 3169893326120157122542691)
                ·
                  refine ⟨4754839989180235683814037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169893326120157122542691 4754839989180235683814037)
                  ·
                    refine ⟨222883124492823547678783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4754839989180235683814037 222883124492823547678783)
                    ·
                      rfl

theorem cell22_651095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_651095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651095 prefixEnd_651095 := by exact prefixLift 651095
  have htrace : WordTrace (prefixWord ++ tailWord_651095) baseStart_651095 baseEnd_651095 := by
    simpa [prefixWord, tailWord_651095, baseEnd_651095] using wordTrace_append hprefix tailTrace_651095
  have hstable : (prefixWord ++ tailWord_651095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651095).length < 2 ^ (prefixWord ++ tailWord_651095).sum := by decide
  have hdescent : baseEnd_651095 < baseStart_651095 := by decide
  rcases family_descends (prefixWord ++ tailWord_651095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651114 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_651114 : Nat := 118140960795 + 651114 * 2 ^ 59
def prefixEnd_651114 : Nat := 4983230072969 + 3 ^ 40 * 651114 * 2
def baseEnd_651114 : Nat := 222889628581113831453725

theorem tailTrace_651114 : CollatzResearch.WordTrace tailWord_651114 prefixEnd_651114 222889628581113831453725 := by
  unfold tailWord_651114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937019640783163565778099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15832052375421769508741597 5937019640783163565778099)
  ·
    refine ⟨8905529461174745348667149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937019640783163565778099 8905529461174745348667149)
    ·
      refine ⟨3339573547940529505750181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8905529461174745348667149 3339573547940529505750181)
      ·
        refine ⟨626170040238849282328159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3339573547940529505750181 626170040238849282328159)
        ·
          refine ⟨939255060358273923492239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626170040238849282328159 939255060358273923492239)
          ·
            refine ⟨1408882590537410885238359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939255060358273923492239 1408882590537410885238359)
            ·
              refine ⟨2113323885806116327857539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408882590537410885238359 2113323885806116327857539)
              ·
                refine ⟨3169985828709174491786309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113323885806116327857539 3169985828709174491786309)
                ·
                  refine ⟨594372342882970217209933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3169985828709174491786309 594372342882970217209933)
                  ·
                    refine ⟨222889628581113831453725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594372342882970217209933 222889628581113831453725)
                    ·
                      rfl

theorem cell22_651114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_651114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651114 prefixEnd_651114 := by exact prefixLift 651114
  have htrace : WordTrace (prefixWord ++ tailWord_651114) baseStart_651114 baseEnd_651114 := by
    simpa [prefixWord, tailWord_651114, baseEnd_651114] using wordTrace_append hprefix tailTrace_651114
  have hstable : (prefixWord ++ tailWord_651114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651114).length < 2 ^ (prefixWord ++ tailWord_651114).sum := by decide
  have hdescent : baseEnd_651114 < baseStart_651114 := by decide
  rcases family_descends (prefixWord ++ tailWord_651114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651144 : List Nat := [2, 1, 3, 3, 4, 1, 2, 6]
def baseStart_651144 : Nat := 118140960795 + 651144 * 2 ^ 59
def prefixEnd_651144 : Nat := 4983230072969 + 3 ^ 40 * 651144 * 2
def baseEnd_651144 : Nat := 24766655354911528133737

theorem tailTrace_651144 : CollatzResearch.WordTrace tailWord_651144 prefixEnd_651144 24766655354911528133737 := by
  unfold tailWord_651144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874586376511984693352243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15832781835349312924469657 11874586376511984693352243)
  ·
    refine ⟨17811879564767977040028365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11874586376511984693352243 17811879564767977040028365)
    ·
      refine ⟨6679454836787991390010637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17811879564767977040028365 6679454836787991390010637)
      ·
        refine ⟨2504795563795496771253989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6679454836787991390010637 2504795563795496771253989)
        ·
          refine ⟨469649168211655644610123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2504795563795496771253989 469649168211655644610123)
          ·
            refine ⟨704473752317483466915185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469649168211655644610123 704473752317483466915185)
            ·
              refine ⟨528355314238112600186389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704473752317483466915185 528355314238112600186389)
              ·
                refine ⟨24766655354911528133737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 528355314238112600186389 24766655354911528133737)
                ·
                  rfl

theorem cell22_651144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_651144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651144 prefixEnd_651144 := by exact prefixLift 651144
  have htrace : WordTrace (prefixWord ++ tailWord_651144) baseStart_651144 baseEnd_651144 := by
    simpa [prefixWord, tailWord_651144, baseEnd_651144] using wordTrace_append hprefix tailTrace_651144
  have hstable : (prefixWord ++ tailWord_651144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651144).length < 2 ^ (prefixWord ++ tailWord_651144).sum := by decide
  have hdescent : baseEnd_651144 < baseStart_651144 := by decide
  rcases family_descends (prefixWord ++ tailWord_651144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651153 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_651153 : Nat := 118140960795 + 651153 * 2 ^ 59
def prefixEnd_651153 : Nat := 4983230072969 + 3 ^ 40 * 651153 * 2
def baseEnd_651153 : Nat := 222902979078130729728605

theorem tailTrace_651153 : CollatzResearch.WordTrace tailWord_651153 prefixEnd_651153 222902979078130729728605 := by
  unfold tailWord_651153
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749501009991363923782113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833000673327575949188075 23749501009991363923782113)
  ·
    refine ⟨17812125757493522942836585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23749501009991363923782113 17812125757493522942836585)
    ·
      refine ⟨13359094318120142207127439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17812125757493522942836585 13359094318120142207127439)
      ·
        refine ⟨20038641477180213310691159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359094318120142207127439 20038641477180213310691159)
        ·
          refine ⟨30057962215770319966036739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20038641477180213310691159 30057962215770319966036739)
          ·
            refine ⟨45086943323655479949055109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30057962215770319966036739 45086943323655479949055109)
            ·
              refine ⟨8453801873185402490447833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45086943323655479949055109 8453801873185402490447833)
              ·
                refine ⟨6340351404889051867835875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8453801873185402490447833 6340351404889051867835875)
                ·
                  refine ⟨9510527107333577801753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6340351404889051867835875 9510527107333577801753813)
                  ·
                    refine ⟨222902979078130729728605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9510527107333577801753813 222902979078130729728605)
                    ·
                      rfl

theorem cell22_651153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_651153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651153 prefixEnd_651153 := by exact prefixLift 651153
  have htrace : WordTrace (prefixWord ++ tailWord_651153) baseStart_651153 baseEnd_651153 := by
    simpa [prefixWord, tailWord_651153, baseEnd_651153] using wordTrace_append hprefix tailTrace_651153
  have hstable : (prefixWord ++ tailWord_651153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651153).length < 2 ^ (prefixWord ++ tailWord_651153).sum := by decide
  have hdescent : baseEnd_651153 < baseStart_651153 := by decide
  rcases family_descends (prefixWord ++ tailWord_651153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651159 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 1, 3]
def baseStart_651159 : Nat := 118140960795 + 651159 * 2 ^ 59
def prefixEnd_651159 : Nat := 4983230072969 + 3 ^ 40 * 651159 * 2
def baseEnd_651159 : Nat := 222905033000748714078587

theorem tailTrace_651159 : CollatzResearch.WordTrace tailWord_651159 prefixEnd_651159 222905033000748714078587 := by
  unfold tailWord_651159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749719847969626948500531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833146565313084632333687 23749719847969626948500531)
  ·
    refine ⟨35624579771954440422750797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23749719847969626948500531 35624579771954440422750797)
    ·
      refine ⟨13359217414482915158531549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35624579771954440422750797 13359217414482915158531549)
      ·
        refine ⟨5009706530431093184449331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13359217414482915158531549 5009706530431093184449331)
        ·
          refine ⟨7514559795646639776673997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009706530431093184449331 7514559795646639776673997)
          ·
            refine ⟨2817959923367489916252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7514559795646639776673997 2817959923367489916252749)
            ·
              refine ⟨1056734971262808718594781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2817959923367489916252749 1056734971262808718594781)
              ·
                refine ⟨396275614223553269473043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056734971262808718594781 396275614223553269473043)
                ·
                  refine ⟨594413421335329904209565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396275614223553269473043 594413421335329904209565)
                  ·
                    refine ⟨222905033000748714078587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594413421335329904209565 222905033000748714078587)
                    ·
                      rfl

theorem cell22_651159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_651159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651159 prefixEnd_651159 := by exact prefixLift 651159
  have htrace : WordTrace (prefixWord ++ tailWord_651159) baseStart_651159 baseEnd_651159 := by
    simpa [prefixWord, tailWord_651159, baseEnd_651159] using wordTrace_append hprefix tailTrace_651159
  have hstable : (prefixWord ++ tailWord_651159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651159).length < 2 ^ (prefixWord ++ tailWord_651159).sum := by decide
  have hdescent : baseEnd_651159 < baseStart_651159 := by decide
  rcases family_descends (prefixWord ++ tailWord_651159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651182 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_651182 : Nat := 118140960795 + 651182 * 2 ^ 59
def prefixEnd_651182 : Nat := 4983230072969 + 3 ^ 40 * 651182 * 2
def baseEnd_651182 : Nat := 222912906370784320753517

theorem tailTrace_651182 : CollatzResearch.WordTrace tailWord_651182 prefixEnd_651182 222912906370784320753517 := by
  unfold tailWord_651182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968819840860787734573475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15833705817924201251058533 2968819840860787734573475)
  ·
    refine ⟨4453229761291181601860213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2968819840860787734573475 4453229761291181601860213)
    ·
      refine ⟨417490290121048275174395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4453229761291181601860213 417490290121048275174395)
      ·
        refine ⟨626235435181572412761593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417490290121048275174395 626235435181572412761593)
        ·
          refine ⟨469676576386179309571195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626235435181572412761593 469676576386179309571195)
          ·
            refine ⟨704514864579268964356793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469676576386179309571195 704514864579268964356793)
            ·
              refine ⟨528386148434451723267595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704514864579268964356793 528386148434451723267595)
              ·
                refine ⟨792579222651677584901393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528386148434451723267595 792579222651677584901393)
                ·
                  refine ⟨594434416988758188676045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 792579222651677584901393 594434416988758188676045)
                  ·
                    refine ⟨222912906370784320753517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594434416988758188676045 222912906370784320753517)
                    ·
                      rfl

theorem cell22_651182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_651182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651182 prefixEnd_651182 := by exact prefixLift 651182
  have htrace : WordTrace (prefixWord ++ tailWord_651182) baseStart_651182 baseEnd_651182 := by
    simpa [prefixWord, tailWord_651182, baseEnd_651182] using wordTrace_append hprefix tailTrace_651182
  have hstable : (prefixWord ++ tailWord_651182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651182).length < 2 ^ (prefixWord ++ tailWord_651182).sum := by decide
  have hdescent : baseEnd_651182 < baseStart_651182 := by decide
  rcases family_descends (prefixWord ++ tailWord_651182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651189 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 5]
def baseStart_651189 : Nat := 118140960795 + 651189 * 2 ^ 59
def prefixEnd_651189 : Nat := 4983230072969 + 3 ^ 40 * 651189 * 2
def baseEnd_651189 : Nat := 74305100871279545276165

theorem tailTrace_651189 : CollatzResearch.WordTrace tailWord_651189 prefixEnd_651189 74305100871279545276165 := by
  unfold tailWord_651189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750814037860942072092621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833876025240628048061747 23750814037860942072092621)
  ·
    refine ⟨8906555264197853277034733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23750814037860942072092621 8906555264197853277034733)
    ·
      refine ⟨3339958224074194978888025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8906555264197853277034733 3339958224074194978888025)
      ·
        refine ⟨2504968668055646234166019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339958224074194978888025 2504968668055646234166019)
        ·
          refine ⟨3757453002083469351249029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504968668055646234166019 3757453002083469351249029)
          ·
            refine ⟨704522437890650503359193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3757453002083469351249029 704522437890650503359193)
            ·
              refine ⟨528391828417987877519395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704522437890650503359193 528391828417987877519395)
              ·
                refine ⟨792587742626981816279093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528391828417987877519395 792587742626981816279093)
                ·
                  refine ⟨74305100871279545276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792587742626981816279093 74305100871279545276165)
                  ·
                    rfl

theorem cell22_651189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_651189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651189 prefixEnd_651189 := by exact prefixLift 651189
  have htrace : WordTrace (prefixWord ++ tailWord_651189) baseStart_651189 baseEnd_651189 := by
    simpa [prefixWord, tailWord_651189, baseEnd_651189] using wordTrace_append hprefix tailTrace_651189
  have hstable : (prefixWord ++ tailWord_651189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651189).length < 2 ^ (prefixWord ++ tailWord_651189).sum := by decide
  have hdescent : baseEnd_651189 < baseStart_651189 := by decide
  rcases family_descends (prefixWord ++ tailWord_651189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651215 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_651215 : Nat := 118140960795 + 651215 * 2 ^ 59
def prefixEnd_651215 : Nat := 4983230072969 + 3 ^ 40 * 651215 * 2
def baseEnd_651215 : Nat := 222924202945183234678415

theorem tailTrace_651215 : CollatzResearch.WordTrace tailWord_651215 prefixEnd_651215 222924202945183234678415 := by
  unfold tailWord_651215
  simp only [CollatzResearch.WordTrace]
  refine ⟨23751762335766748512539099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15834508223844499008359399 23751762335766748512539099)
  ·
    refine ⟨35627643503650122768808649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23751762335766748512539099 35627643503650122768808649)
    ·
      refine ⟨26720732627737592076606487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35627643503650122768808649 26720732627737592076606487)
      ·
        refine ⟨40081098941606388114909731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26720732627737592076606487 40081098941606388114909731)
        ·
          refine ⟨60121648412409582172364597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40081098941606388114909731 60121648412409582172364597)
          ·
            refine ⟨5636404538663398328659181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60121648412409582172364597 5636404538663398328659181)
            ·
              refine ⟨2113651701998774373247193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5636404538663398328659181 2113651701998774373247193)
              ·
                refine ⟨1585238776499080779935395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113651701998774373247193 1585238776499080779935395)
                ·
                  refine ⟨2377858164748621169903093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585238776499080779935395 2377858164748621169903093)
                  ·
                    refine ⟨222924202945183234678415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2377858164748621169903093 222924202945183234678415)
                    ·
                      rfl

theorem cell22_651215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_651215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651215 prefixEnd_651215 := by exact prefixLift 651215
  have htrace : WordTrace (prefixWord ++ tailWord_651215) baseStart_651215 baseEnd_651215 := by
    simpa [prefixWord, tailWord_651215, baseEnd_651215] using wordTrace_append hprefix tailTrace_651215
  have hstable : (prefixWord ++ tailWord_651215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651215).length < 2 ^ (prefixWord ++ tailWord_651215).sum := by decide
  have hdescent : baseEnd_651215 < baseStart_651215 := by decide
  rcases family_descends (prefixWord ++ tailWord_651215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651270 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_651270 : Nat := 118140960795 + 651270 * 2 ^ 59
def prefixEnd_651270 : Nat := 4983230072969 + 3 ^ 40 * 651270 * 2
def baseEnd_651270 : Nat := 222943030569181424553247

theorem tailTrace_651270 : CollatzResearch.WordTrace tailWord_651270 prefixEnd_651270 222943030569181424553247 := by
  unfold tailWord_651270
  simp only [CollatzResearch.WordTrace]
  refine ⟨742305260955234153305977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15835845567044995270527509 742305260955234153305977)
  ·
    refine ⟨556728945716425614979483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 742305260955234153305977 556728945716425614979483)
    ·
      refine ⟨835093418574638422469225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556728945716425614979483 835093418574638422469225)
      ·
        refine ⟨626320063930978816851919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835093418574638422469225 626320063930978816851919)
        ·
          refine ⟨939480095896468225277879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626320063930978816851919 939480095896468225277879)
          ·
            refine ⟨1409220143844702337916819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939480095896468225277879 1409220143844702337916819)
            ·
              refine ⟨2113830215767053506875229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409220143844702337916819 2113830215767053506875229)
              ·
                refine ⟨792686330912645065078211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2113830215767053506875229 792686330912645065078211)
                ·
                  refine ⟨1189029496368967597617317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792686330912645065078211 1189029496368967597617317)
                  ·
                    refine ⟨222943030569181424553247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189029496368967597617317 222943030569181424553247)
                    ·
                      rfl

theorem cell22_651270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_651270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651270 prefixEnd_651270 := by exact prefixLift 651270
  have htrace : WordTrace (prefixWord ++ tailWord_651270) baseStart_651270 baseEnd_651270 := by
    simpa [prefixWord, tailWord_651270, baseEnd_651270] using wordTrace_append hprefix tailTrace_651270
  have hstable : (prefixWord ++ tailWord_651270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651270).length < 2 ^ (prefixWord ++ tailWord_651270).sum := by decide
  have hdescent : baseEnd_651270 < baseStart_651270 := by decide
  rcases family_descends (prefixWord ++ tailWord_651270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651337 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_651337 : Nat := 118140960795 + 651337 * 2 ^ 59
def prefixEnd_651337 : Nat := 4983230072969 + 3 ^ 40 * 651337 * 2
def baseEnd_651337 : Nat := 222965966038415583128041

theorem tailTrace_651337 : CollatzResearch.WordTrace tailWord_651337 prefixEnd_651337 222965966038415583128041 := by
  unfold tailWord_651337
  simp only [CollatzResearch.WordTrace]
  refine ⟨23756212041324763348480265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15837474694216508898986843 23756212041324763348480265)
  ·
    refine ⟨17817159030993572511360199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23756212041324763348480265 17817159030993572511360199)
    ·
      refine ⟨26725738546490358767040299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17817159030993572511360199 26725738546490358767040299)
      ·
        refine ⟨40088607819735538150560449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26725738546490358767040299 40088607819735538150560449)
        ·
          refine ⟨30066455864801653612920337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40088607819735538150560449 30066455864801653612920337)
          ·
            refine ⟨22549841898601240209690253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30066455864801653612920337 22549841898601240209690253)
            ·
              refine ⟨8456190711975465078633845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22549841898601240209690253 8456190711975465078633845)
              ·
                refine ⟨792767879247699851121923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8456190711975465078633845 792767879247699851121923)
                ·
                  refine ⟨1189151818871549776682885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792767879247699851121923 1189151818871549776682885)
                  ·
                    refine ⟨222965966038415583128041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189151818871549776682885 222965966038415583128041)
                    ·
                      rfl

theorem cell22_651337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_651337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651337 prefixEnd_651337 := by exact prefixLift 651337
  have htrace : WordTrace (prefixWord ++ tailWord_651337) baseStart_651337 baseEnd_651337 := by
    simpa [prefixWord, tailWord_651337, baseEnd_651337] using wordTrace_append hprefix tailTrace_651337
  have hstable : (prefixWord ++ tailWord_651337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651337).length < 2 ^ (prefixWord ++ tailWord_651337).sum := by decide
  have hdescent : baseEnd_651337 < baseStart_651337 := by decide
  rcases family_descends (prefixWord ++ tailWord_651337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651352 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_651352 : Nat := 118140960795 + 651352 * 2 ^ 59
def prefixEnd_651352 : Nat := 4983230072969 + 3 ^ 40 * 651352 * 2
def baseEnd_651352 : Nat := 74323700281653514667665

theorem tailTrace_651352 : CollatzResearch.WordTrace tailWord_651352 prefixEnd_651352 74323700281653514667665 := by
  unfold tailWord_651352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11878379568135210455138155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15837839424180280606850873 11878379568135210455138155)
  ·
    refine ⟨17817569352202815682707233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11878379568135210455138155 17817569352202815682707233)
    ·
      refine ⟨13363177014152111762030425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17817569352202815682707233 13363177014152111762030425)
      ·
        refine ⟨10022382760614083821522819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13363177014152111762030425 10022382760614083821522819)
        ·
          refine ⟨15033574140921125732284229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10022382760614083821522819 15033574140921125732284229)
          ·
            refine ⟨2818795151422711074803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15033574140921125732284229 2818795151422711074803293)
            ·
              refine ⟨1057048181783516653051235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818795151422711074803293 1057048181783516653051235)
              ·
                refine ⟨1585572272675274979576853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057048181783516653051235 1585572272675274979576853)
                ·
                  refine ⟨74323700281653514667665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1585572272675274979576853 74323700281653514667665)
                  ·
                    rfl

theorem cell22_651352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_651352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651352 prefixEnd_651352 := by exact prefixLift 651352
  have htrace : WordTrace (prefixWord ++ tailWord_651352) baseStart_651352 baseEnd_651352 := by
    simpa [prefixWord, tailWord_651352, baseEnd_651352] using wordTrace_append hprefix tailTrace_651352
  have hstable : (prefixWord ++ tailWord_651352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651352).length < 2 ^ (prefixWord ++ tailWord_651352).sum := by decide
  have hdescent : baseEnd_651352 < baseStart_651352 := by decide
  rcases family_descends (prefixWord ++ tailWord_651352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651358 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_651358 : Nat := 118140960795 + 651358 * 2 ^ 59
def prefixEnd_651358 : Nat := 4983230072969 + 3 ^ 40 * 651358 * 2
def baseEnd_651358 : Nat := 74324384922526176117659

theorem tailTrace_651358 : CollatzResearch.WordTrace tailWord_651358 prefixEnd_651358 74324384922526176117659 := by
  unfold tailWord_651358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969622246781085491874341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15837985316165789289996485 2969622246781085491874341)
  ·
    refine ⟨556804171271453529726439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2969622246781085491874341 556804171271453529726439)
    ·
      refine ⟨835206256907180294589659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556804171271453529726439 835206256907180294589659)
      ·
        refine ⟨1252809385360770441884489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835206256907180294589659 1252809385360770441884489)
        ·
          refine ⟨939607039020577831413367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252809385360770441884489 939607039020577831413367)
          ·
            refine ⟨1409410558530866747120051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939607039020577831413367 1409410558530866747120051)
            ·
              refine ⟨2114115837796300120680077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409410558530866747120051 2114115837796300120680077)
              ·
                refine ⟨792793439173612545255029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2114115837796300120680077 792793439173612545255029)
                ·
                  refine ⟨74324384922526176117659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792793439173612545255029 74324384922526176117659)
                  ·
                    rfl

theorem cell22_651358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_651358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651358 prefixEnd_651358 := by exact prefixLift 651358
  have htrace : WordTrace (prefixWord ++ tailWord_651358) baseStart_651358 baseEnd_651358 := by
    simpa [prefixWord, tailWord_651358, baseEnd_651358] using wordTrace_append hprefix tailTrace_651358
  have hstable : (prefixWord ++ tailWord_651358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651358).length < 2 ^ (prefixWord ++ tailWord_651358).sum := by decide
  have hdescent : baseEnd_651358 < baseStart_651358 := by decide
  rcases family_descends (prefixWord ++ tailWord_651358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651367 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_651367 : Nat := 118140960795 + 651367 * 2 ^ 59
def prefixEnd_651367 : Nat := 4983230072969 + 3 ^ 40 * 651367 * 2
def baseEnd_651367 : Nat := 222976235651505504877949

theorem tailTrace_651367 : CollatzResearch.WordTrace tailWord_651367 prefixEnd_651367 222976235651505504877949 := by
  unfold tailWord_651367
  simp only [CollatzResearch.WordTrace]
  refine ⟨23757306231216078472072355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15838204154144052314714903 23757306231216078472072355)
  ·
    refine ⟨35635959346824117708108533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23757306231216078472072355 35635959346824117708108533)
    ·
      refine ⟨3340871188764761035135175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35635959346824117708108533 3340871188764761035135175)
      ·
        refine ⟨5011306783147141552702763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340871188764761035135175 5011306783147141552702763)
        ·
          refine ⟨7516960174720712329054145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011306783147141552702763 7516960174720712329054145)
          ·
            refine ⟨5637720131040534246790609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7516960174720712329054145 5637720131040534246790609)
            ·
              refine ⟨4228290098280400685092957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637720131040534246790609 4228290098280400685092957)
              ·
                refine ⟨1585608786855150256909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4228290098280400685092957 1585608786855150256909859)
                ·
                  refine ⟨2378413180282725385364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585608786855150256909859 2378413180282725385364789)
                  ·
                    refine ⟨222976235651505504877949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2378413180282725385364789 222976235651505504877949)
                    ·
                      rfl

theorem cell22_651367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_651367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651367 prefixEnd_651367 := by exact prefixLift 651367
  have htrace : WordTrace (prefixWord ++ tailWord_651367) baseStart_651367 baseEnd_651367 := by
    simpa [prefixWord, tailWord_651367, baseEnd_651367] using wordTrace_append hprefix tailTrace_651367
  have hstable : (prefixWord ++ tailWord_651367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651367).length < 2 ^ (prefixWord ++ tailWord_651367).sum := by decide
  have hdescent : baseEnd_651367 < baseStart_651367 := by decide
  rcases family_descends (prefixWord ++ tailWord_651367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651429 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_651429 : Nat := 118140960795 + 651429 * 2 ^ 59
def prefixEnd_651429 : Nat := 4983230072969 + 3 ^ 40 * 651429 * 2
def baseEnd_651429 : Nat := 222997459518558009827759

theorem tailTrace_651429 : CollatzResearch.WordTrace tailWord_651429 prefixEnd_651429 222997459518558009827759 := by
  unfold tailWord_651429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759567556991463060829341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15839711704660975373886227 23759567556991463060829341)
  ·
    refine ⟨8909837833871798647811003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23759567556991463060829341 8909837833871798647811003)
    ·
      refine ⟨13364756750807697971716505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8909837833871798647811003 13364756750807697971716505)
      ·
        refine ⟨10023567563105773478787379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13364756750807697971716505 10023567563105773478787379)
        ·
          refine ⟨15035351344658660218181069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023567563105773478787379 15035351344658660218181069)
          ·
            refine ⟨5638256754246997581817901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15035351344658660218181069 5638256754246997581817901)
            ·
              refine ⟨2114346282842624093181713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5638256754246997581817901 2114346282842624093181713)
              ·
                refine ⟨1585759712131968069886285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114346282842624093181713 1585759712131968069886285)
                ·
                  refine ⟨594659892049488026207357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1585759712131968069886285 594659892049488026207357)
                  ·
                    refine ⟨222997459518558009827759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594659892049488026207357 222997459518558009827759)
                    ·
                      rfl

theorem cell22_651429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_651429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651429 prefixEnd_651429 := by exact prefixLift 651429
  have htrace : WordTrace (prefixWord ++ tailWord_651429) baseStart_651429 baseEnd_651429 := by
    simpa [prefixWord, tailWord_651429, baseEnd_651429] using wordTrace_append hprefix tailTrace_651429
  have hstable : (prefixWord ++ tailWord_651429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651429).length < 2 ^ (prefixWord ++ tailWord_651429).sum := by decide
  have hdescent : baseEnd_651429 < baseStart_651429 := by decide
  rcases family_descends (prefixWord ++ tailWord_651429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651431 : List Nat := [1, 1, 6, 2, 2, 1, 3, 6]
def baseStart_651431 : Nat := 118140960795 + 651431 * 2 ^ 59
def prefixEnd_651431 : Nat := 4983230072969 + 3 ^ 40 * 651431 * 2
def baseEnd_651431 : Nat := 24777571573270074586417

theorem tailTrace_651431 : CollatzResearch.WordTrace tailWord_651431 prefixEnd_651431 24777571573270074586417 := by
  unfold tailWord_651431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759640502984217402402147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15839760335322811601601431 23759640502984217402402147)
  ·
    refine ⟨35639460754476326103603221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23759640502984217402402147 35639460754476326103603221)
    ·
      refine ⟨1670599722866077786106401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35639460754476326103603221 1670599722866077786106401)
      ·
        refine ⟨1252949792149558339579801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1670599722866077786106401 1252949792149558339579801)
        ·
          refine ⟨939712344112168754684851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252949792149558339579801 939712344112168754684851)
          ·
            refine ⟨1409568516168253132027277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939712344112168754684851 1409568516168253132027277)
            ·
              refine ⟨528588193563094924510229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409568516168253132027277 528588193563094924510229)
              ·
                refine ⟨24777571573270074586417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 528588193563094924510229 24777571573270074586417)
                ·
                  rfl

theorem cell22_651431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 6].length) (baseStart_651431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651431 prefixEnd_651431 := by exact prefixLift 651431
  have htrace : WordTrace (prefixWord ++ tailWord_651431) baseStart_651431 baseEnd_651431 := by
    simpa [prefixWord, tailWord_651431, baseEnd_651431] using wordTrace_append hprefix tailTrace_651431
  have hstable : (prefixWord ++ tailWord_651431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651431).length < 2 ^ (prefixWord ++ tailWord_651431).sum := by decide
  have hdescent : baseEnd_651431 < baseStart_651431 := by decide
  rcases family_descends (prefixWord ++ tailWord_651431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651442 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_651442 : Nat := 118140960795 + 651442 * 2 ^ 59
def prefixEnd_651442 : Nat := 4983230072969 + 3 ^ 40 * 651442 * 2
def baseEnd_651442 : Nat := 74333969894743436417573

theorem tailTrace_651442 : CollatzResearch.WordTrace tailWord_651442 prefixEnd_651442 74333969894743436417573 := by
  unfold tailWord_651442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940010426486091570263145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15840027803962910854035053 5940010426486091570263145)
  ·
    refine ⟨4455007819864568677697359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5940010426486091570263145 4455007819864568677697359)
    ·
      refine ⟨6682511729796853016546039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455007819864568677697359 6682511729796853016546039)
      ·
        refine ⟨10023767594695279524819059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682511729796853016546039 10023767594695279524819059)
        ·
          refine ⟨15035651392042919287228589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023767594695279524819059 15035651392042919287228589)
          ·
            refine ⟨5638369272016094732710721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15035651392042919287228589 5638369272016094732710721)
            ·
              refine ⟨4228776954012071049533041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5638369272016094732710721 4228776954012071049533041)
              ·
                refine ⟨3171582715509053287149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228776954012071049533041 3171582715509053287149781)
                ·
                  refine ⟨74333969894743436417573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3171582715509053287149781 74333969894743436417573)
                  ·
                    rfl

theorem cell22_651442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_651442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651442 prefixEnd_651442 := by exact prefixLift 651442
  have htrace : WordTrace (prefixWord ++ tailWord_651442) baseStart_651442 baseEnd_651442 := by
    simpa [prefixWord, tailWord_651442, baseEnd_651442] using wordTrace_append hprefix tailTrace_651442
  have hstable : (prefixWord ++ tailWord_651442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651442).length < 2 ^ (prefixWord ++ tailWord_651442).sum := by decide
  have hdescent : baseEnd_651442 < baseStart_651442 := by decide
  rcases family_descends (prefixWord ++ tailWord_651442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651474 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_651474 : Nat := 118140960795 + 651474 * 2 ^ 59
def prefixEnd_651474 : Nat := 4983230072969 + 3 ^ 40 * 651474 * 2
def baseEnd_651474 : Nat := 223012863938192892452621

theorem tailTrace_651474 : CollatzResearch.WordTrace tailWord_651474 prefixEnd_651474 223012863938192892452621 := by
  unfold tailWord_651474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940302210457108936554369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15840805894552290497478317 5940302210457108936554369)
  ·
    refine ⟨4455226657842831702415777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5940302210457108936554369 4455226657842831702415777)
    ·
      refine ⟨3341419993382123776811833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4455226657842831702415777 3341419993382123776811833)
      ·
        refine ⟨2506064995036592832608875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3341419993382123776811833 2506064995036592832608875)
        ·
          refine ⟨3759097492554889248913313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506064995036592832608875 3759097492554889248913313)
          ·
            refine ⟨2819323119416166936684985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759097492554889248913313 2819323119416166936684985)
            ·
              refine ⟨2114492339562125202513739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819323119416166936684985 2114492339562125202513739)
              ·
                refine ⟨3171738509343187803770609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114492339562125202513739 3171738509343187803770609)
                ·
                  refine ⟨2378803882007390852827957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171738509343187803770609 2378803882007390852827957)
                  ·
                    refine ⟨223012863938192892452621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2378803882007390852827957 223012863938192892452621)
                    ·
                      rfl

theorem cell22_651474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_651474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651474 prefixEnd_651474 := by exact prefixLift 651474
  have htrace : WordTrace (prefixWord ++ tailWord_651474) baseStart_651474 baseEnd_651474 := by
    simpa [prefixWord, tailWord_651474, baseEnd_651474] using wordTrace_append hprefix tailTrace_651474
  have hstable : (prefixWord ++ tailWord_651474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651474).length < 2 ^ (prefixWord ++ tailWord_651474).sum := by decide
  have hdescent : baseEnd_651474 < baseStart_651474 := by decide
  rcases family_descends (prefixWord ++ tailWord_651474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651506 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_651506 : Nat := 118140960795 + 651506 * 2 ^ 59
def prefixEnd_651506 : Nat := 4983230072969 + 3 ^ 40 * 651506 * 2
def baseEnd_651506 : Nat := 223023818192155475652523

theorem tailTrace_651506 : CollatzResearch.WordTrace tailWord_651506 prefixEnd_651506 223023818192155475652523 := by
  unfold tailWord_651506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940593994428126302845593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15841583985141670140921581 5940593994428126302845593)
  ·
    refine ⟨4455445495821094727134195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5940593994428126302845593 4455445495821094727134195)
    ·
      refine ⟨6683168243731642090701293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455445495821094727134195 6683168243731642090701293)
      ·
        refine ⟨2506188091399365784012985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6683168243731642090701293 2506188091399365784012985)
        ·
          refine ⟨1879641068549524338009739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506188091399365784012985 1879641068549524338009739)
          ·
            refine ⟨2819461602824286507014609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879641068549524338009739 2819461602824286507014609)
            ·
              refine ⟨2114596202118214880260957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819461602824286507014609 2114596202118214880260957)
              ·
                refine ⟨792973575794330580097859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2114596202118214880260957 792973575794330580097859)
                ·
                  refine ⟨1189460363691495870146789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792973575794330580097859 1189460363691495870146789)
                  ·
                    refine ⟨223023818192155475652523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189460363691495870146789 223023818192155475652523)
                    ·
                      rfl

theorem cell22_651506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_651506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651506 prefixEnd_651506 := by exact prefixLift 651506
  have htrace : WordTrace (prefixWord ++ tailWord_651506) baseStart_651506 baseEnd_651506 := by
    simpa [prefixWord, tailWord_651506, baseEnd_651506] using wordTrace_append hprefix tailTrace_651506
  have hstable : (prefixWord ++ tailWord_651506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651506).length < 2 ^ (prefixWord ++ tailWord_651506).sum := by decide
  have hdescent : baseEnd_651506 < baseStart_651506 := by decide
  rcases family_descends (prefixWord ++ tailWord_651506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651519 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 4, 3]
def baseStart_651519 : Nat := 118140960795 + 651519 * 2 ^ 59
def prefixEnd_651519 : Nat := 4983230072969 + 3 ^ 40 * 651519 * 2
def baseEnd_651519 : Nat := 223028268357827775077483

theorem tailTrace_651519 : CollatzResearch.WordTrace tailWord_651519 prefixEnd_651519 223028268357827775077483 := by
  unfold tailWord_651519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23762850126665408431605611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15841900084443605621070407 23762850126665408431605611)
  ·
    refine ⟨35644275189998112647408417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23762850126665408431605611 35644275189998112647408417)
    ·
      refine ⟨26733206392498584485556313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35644275189998112647408417 26733206392498584485556313)
      ·
        refine ⟨20049904794373938364167235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26733206392498584485556313 20049904794373938364167235)
        ·
          refine ⟨30074857191560907546250853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20049904794373938364167235 30074857191560907546250853)
          ·
            refine ⟨5639035723417670164922035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30074857191560907546250853 5639035723417670164922035)
            ·
              refine ⟨8458553585126505247383053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639035723417670164922035 8458553585126505247383053)
              ·
                refine ⟨3171957594422439467768645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8458553585126505247383053 3171957594422439467768645)
                ·
                  refine ⟨594742048954207400206621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3171957594422439467768645 594742048954207400206621)
                  ·
                    refine ⟨223028268357827775077483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594742048954207400206621 223028268357827775077483)
                    ·
                      rfl

theorem cell22_651519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_651519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651519 prefixEnd_651519 := by exact prefixLift 651519
  have htrace : WordTrace (prefixWord ++ tailWord_651519) baseStart_651519 baseEnd_651519 := by
    simpa [prefixWord, tailWord_651519, baseEnd_651519] using wordTrace_append hprefix tailTrace_651519
  have hstable : (prefixWord ++ tailWord_651519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651519).length < 2 ^ (prefixWord ++ tailWord_651519).sum := by decide
  have hdescent : baseEnd_651519 < baseStart_651519 := by decide
  rcases family_descends (prefixWord ++ tailWord_651519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651534 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_651534 : Nat := 118140960795 + 651534 * 2 ^ 59
def prefixEnd_651534 : Nat := 4983230072969 + 3 ^ 40 * 651534 * 2
def baseEnd_651534 : Nat := 223033403164372735952437

theorem tailTrace_651534 : CollatzResearch.WordTrace tailWord_651534 prefixEnd_651534 223033403164372735952437 := by
  unfold tailWord_651534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970424652701383249175207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15842264814407377328934437 2970424652701383249175207)
  ·
    refine ⟨4455636979052074873762811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2970424652701383249175207 4455636979052074873762811)
    ·
      refine ⟨6683455468578112310644217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455636979052074873762811 6683455468578112310644217)
      ·
        refine ⟨5012591601433584232983163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6683455468578112310644217 5012591601433584232983163)
        ·
          refine ⟨7518887402150376349474745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012591601433584232983163 7518887402150376349474745)
          ·
            refine ⟨5639165551612782262106059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7518887402150376349474745 5639165551612782262106059)
            ·
              refine ⟨8458748327419173393159089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639165551612782262106059 8458748327419173393159089)
              ·
                refine ⟨6344061245564380044869317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458748327419173393159089 6344061245564380044869317)
                ·
                  refine ⟨1189511483543321258412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6344061245564380044869317 1189511483543321258412997)
                  ·
                    refine ⟨223033403164372735952437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189511483543321258412997 223033403164372735952437)
                    ·
                      rfl

theorem cell22_651534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_651534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651534 prefixEnd_651534 := by exact prefixLift 651534
  have htrace : WordTrace (prefixWord ++ tailWord_651534) baseStart_651534 baseEnd_651534 := by
    simpa [prefixWord, tailWord_651534, baseEnd_651534] using wordTrace_append hprefix tailTrace_651534
  have hstable : (prefixWord ++ tailWord_651534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651534).length < 2 ^ (prefixWord ++ tailWord_651534).sum := by decide
  have hdescent : baseEnd_651534 < baseStart_651534 := by decide
  rcases family_descends (prefixWord ++ tailWord_651534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651547 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_651547 : Nat := 118140960795 + 651547 * 2 ^ 59
def prefixEnd_651547 : Nat := 4983230072969 + 3 ^ 40 * 651547 * 2
def baseEnd_651547 : Nat := 223037853330045035377397

theorem tailTrace_651547 : CollatzResearch.WordTrace tailWord_651547 prefixEnd_651547 223037853330045035377397 := by
  unfold tailWord_651547
  simp only [CollatzResearch.WordTrace]
  refine ⟨23763871370563969213624895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15842580913709312809083263 23763871370563969213624895)
  ·
    refine ⟨35645807055845953820437343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23763871370563969213624895 35645807055845953820437343)
    ·
      refine ⟨53468710583768930730656015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35645807055845953820437343 53468710583768930730656015)
      ·
        refine ⟨80203065875653396095984023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53468710583768930730656015 80203065875653396095984023)
        ·
          refine ⟨120304598813480094143976035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80203065875653396095984023 120304598813480094143976035)
          ·
            refine ⟨180456898220220141215964053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120304598813480094143976035 180456898220220141215964053)
            ·
              refine ⟨8458917104072819119498315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180456898220220141215964053 8458917104072819119498315)
              ·
                refine ⟨12688375656109228679247473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8458917104072819119498315 12688375656109228679247473)
                ·
                  refine ⟨9516281742081921509435605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12688375656109228679247473 9516281742081921509435605)
                  ·
                    refine ⟨223037853330045035377397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9516281742081921509435605 223037853330045035377397)
                    ·
                      rfl

theorem cell22_651547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_651547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651547 prefixEnd_651547 := by exact prefixLift 651547
  have htrace : WordTrace (prefixWord ++ tailWord_651547) baseStart_651547 baseEnd_651547 := by
    simpa [prefixWord, tailWord_651547, baseEnd_651547] using wordTrace_append hprefix tailTrace_651547
  have hstable : (prefixWord ++ tailWord_651547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651547).length < 2 ^ (prefixWord ++ tailWord_651547).sum := by decide
  have hdescent : baseEnd_651547 < baseStart_651547 := by decide
  rcases family_descends (prefixWord ++ tailWord_651547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651551 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_651551 : Nat := 118140960795 + 651551 * 2 ^ 59
def prefixEnd_651551 : Nat := 4983230072969 + 3 ^ 40 * 651551 * 2
def baseEnd_651551 : Nat := 223039222611790358277385

theorem tailTrace_651551 : CollatzResearch.WordTrace tailWord_651551 prefixEnd_651551 223039222611790358277385 := by
  unfold tailWord_651551
  simp only [CollatzResearch.WordTrace]
  refine ⟨23764017262549477896770507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15842678175032985264513671 23764017262549477896770507)
  ·
    refine ⟨35646025893824216845155761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23764017262549477896770507 35646025893824216845155761)
    ·
      refine ⟨26734519420368162633866821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35646025893824216845155761 26734519420368162633866821)
      ·
        refine ⟨5012722391319030493850029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26734519420368162633866821 5012722391319030493850029)
        ·
          refine ⟨1879770896744636435193761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5012722391319030493850029 1879770896744636435193761)
          ·
            refine ⟨1409828172558477326395321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1879770896744636435193761 1409828172558477326395321)
            ·
              refine ⟨1057371129418857994796491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409828172558477326395321 1057371129418857994796491)
              ·
                refine ⟨1586056694128286992194737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057371129418857994796491 1586056694128286992194737)
                ·
                  refine ⟨1189542520596215244146053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1586056694128286992194737 1189542520596215244146053)
                  ·
                    refine ⟨223039222611790358277385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189542520596215244146053 223039222611790358277385)
                    ·
                      rfl

theorem cell22_651551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_651551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651551 prefixEnd_651551 := by exact prefixLift 651551
  have htrace : WordTrace (prefixWord ++ tailWord_651551) baseStart_651551 baseEnd_651551 := by
    simpa [prefixWord, tailWord_651551, baseEnd_651551] using wordTrace_append hprefix tailTrace_651551
  have hstable : (prefixWord ++ tailWord_651551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651551).length < 2 ^ (prefixWord ++ tailWord_651551).sum := by decide
  have hdescent : baseEnd_651551 < baseStart_651551 := by decide
  rcases family_descends (prefixWord ++ tailWord_651551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651566 : List Nat := [4, 1, 3, 3, 1, 10]
def baseStart_651566 : Nat := 118140960795 + 651566 * 2 ^ 59
def prefixEnd_651566 : Nat := 4983230072969 + 3 ^ 40 * 651566 * 2
def baseEnd_651566 : Nat := 2753634042201670606819

theorem tailTrace_651566 : CollatzResearch.WordTrace tailWord_651566 prefixEnd_651566 2753634042201670606819 := by
  unfold tailWord_651566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970570544686891932320819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15843042904996756972377701 2970570544686891932320819)
  ·
    refine ⟨4455855817030337898481229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2970570544686891932320819 4455855817030337898481229)
    ·
      refine ⟨1670945931386376711930461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4455855817030337898481229 1670945931386376711930461)
      ·
        refine ⟨626604724269891266973923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1670945931386376711930461 626604724269891266973923)
        ·
          refine ⟨939907086404836900460885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626604724269891266973923 939907086404836900460885)
          ·
            refine ⟨2753634042201670606819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 939907086404836900460885 2753634042201670606819)
            ·
              rfl

theorem cell22_651566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 10].length) (baseStart_651566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651566 prefixEnd_651566 := by exact prefixLift 651566
  have htrace : WordTrace (prefixWord ++ tailWord_651566) baseStart_651566 baseEnd_651566 := by
    simpa [prefixWord, tailWord_651566, baseEnd_651566] using wordTrace_append hprefix tailTrace_651566
  have hstable : (prefixWord ++ tailWord_651566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651566).length < 2 ^ (prefixWord ++ tailWord_651566).sum := by decide
  have hdescent : baseEnd_651566 < baseStart_651566 := by decide
  rcases family_descends (prefixWord ++ tailWord_651566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651626 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_651626 : Nat := 118140960795 + 651626 * 2 ^ 59
def prefixEnd_651626 : Nat := 4983230072969 + 3 ^ 40 * 651626 * 2
def baseEnd_651626 : Nat := 223064896644515162652155

theorem tailTrace_651626 : CollatzResearch.WordTrace tailWord_651626 prefixEnd_651626 223064896644515162652155 := by
  unfold tailWord_651626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941688184319441426437683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15844501824851843803833821 5941688184319441426437683)
  ·
    refine ⟨8912532276479162139656525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5941688184319441426437683 8912532276479162139656525)
    ·
      refine ⟨3342199603679685802371197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8912532276479162139656525 3342199603679685802371197)
      ·
        refine ⟨1253324851379882175889199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3342199603679685802371197 1253324851379882175889199)
        ·
          refine ⟨1879987277069823263833799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253324851379882175889199 1879987277069823263833799)
          ·
            refine ⟨2819980915604734895750699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879987277069823263833799 2819980915604734895750699)
            ·
              refine ⟨4229971373407102343626049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819980915604734895750699 4229971373407102343626049)
              ·
                refine ⟨3172478530055326757719537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229971373407102343626049 3172478530055326757719537)
                ·
                  refine ⟨2379358897541495068289653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172478530055326757719537 2379358897541495068289653)
                  ·
                    refine ⟨223064896644515162652155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2379358897541495068289653 223064896644515162652155)
                    ·
                      rfl

theorem cell22_651626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_651626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651626 prefixEnd_651626 := by exact prefixLift 651626
  have htrace : WordTrace (prefixWord ++ tailWord_651626) baseStart_651626 baseEnd_651626 := by
    simpa [prefixWord, tailWord_651626, baseEnd_651626] using wordTrace_append hprefix tailTrace_651626
  have hstable : (prefixWord ++ tailWord_651626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651626).length < 2 ^ (prefixWord ++ tailWord_651626).sum := by decide
  have hdescent : baseEnd_651626 < baseStart_651626 := by decide
  rcases family_descends (prefixWord ++ tailWord_651626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651628 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_651628 : Nat := 118140960795 + 651628 * 2 ^ 59
def prefixEnd_651628 : Nat := 4983230072969 + 3 ^ 40 * 651628 * 2
def baseEnd_651628 : Nat := 74355193761795941367383

theorem tailTrace_651628 : CollatzResearch.WordTrace tailWord_651628 prefixEnd_651628 74355193761795941367383 := by
  unfold tailWord_651628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883412841635260023661769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15844550455513680031549025 11883412841635260023661769)
  ·
    refine ⟨8912559631226445017746327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11883412841635260023661769 8912559631226445017746327)
    ·
      refine ⟨13368839446839667526619491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912559631226445017746327 13368839446839667526619491)
      ·
        refine ⟨20053259170259501289929237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368839446839667526619491 20053259170259501289929237)
        ·
          refine ⟨939996523605914122965433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20053259170259501289929237 939996523605914122965433)
          ·
            refine ⟨704997392704435592224075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939996523605914122965433 704997392704435592224075)
            ·
              refine ⟨1057496089056653388336113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704997392704435592224075 1057496089056653388336113)
              ·
                refine ⟨793122066792490041252085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057496089056653388336113 793122066792490041252085)
                ·
                  refine ⟨74355193761795941367383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793122066792490041252085 74355193761795941367383)
                  ·
                    rfl

theorem cell22_651628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_651628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651628 prefixEnd_651628 := by exact prefixLift 651628
  have htrace : WordTrace (prefixWord ++ tailWord_651628) baseStart_651628 baseEnd_651628 := by
    simpa [prefixWord, tailWord_651628, baseEnd_651628] using wordTrace_append hprefix tailTrace_651628
  have hstable : (prefixWord ++ tailWord_651628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651628).length < 2 ^ (prefixWord ++ tailWord_651628).sum := by decide
  have hdescent : baseEnd_651628 < baseStart_651628 := by decide
  rcases family_descends (prefixWord ++ tailWord_651628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651671 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 4, 3]
def baseStart_651671 : Nat := 118140960795 + 651671 * 2 ^ 59
def prefixEnd_651671 : Nat := 4983230072969 + 3 ^ 40 * 651671 * 2
def baseEnd_651671 : Nat := 223080301064150045277017

theorem tailTrace_651671 : CollatzResearch.WordTrace tailWord_651671 prefixEnd_651671 223080301064150045277017 := by
  unfold tailWord_651671
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768394022114738391138867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15845596014743158927425911 23768394022114738391138867)
  ·
    refine ⟨35652591033172107586708301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23768394022114738391138867 35652591033172107586708301)
    ·
      refine ⟨13369721637439540345015613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35652591033172107586708301 13369721637439540345015613)
      ·
        refine ⟨5013645614039827629380855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13369721637439540345015613 5013645614039827629380855)
        ·
          refine ⟨7520468421059741444071283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013645614039827629380855 7520468421059741444071283)
          ·
            refine ⟨11280702631589612166106925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520468421059741444071283 11280702631589612166106925)
            ·
              refine ⟨4230263486846104562290097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11280702631589612166106925 4230263486846104562290097)
              ·
                refine ⟨3172697615134578421717573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230263486846104562290097 3172697615134578421717573)
                ·
                  refine ⟨594880802837733454072045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3172697615134578421717573 594880802837733454072045)
                  ·
                    refine ⟨223080301064150045277017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594880802837733454072045 223080301064150045277017)
                    ·
                      rfl

theorem cell22_651671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_651671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651671 prefixEnd_651671 := by exact prefixLift 651671
  have htrace : WordTrace (prefixWord ++ tailWord_651671) baseStart_651671 baseEnd_651671 := by
    simpa [prefixWord, tailWord_651671, baseEnd_651671] using wordTrace_append hprefix tailTrace_651671
  have hstable : (prefixWord ++ tailWord_651671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651671).length < 2 ^ (prefixWord ++ tailWord_651671).sum := by decide
  have hdescent : baseEnd_651671 < baseStart_651671 := by decide
  rcases family_descends (prefixWord ++ tailWord_651671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651684 : List Nat := [2, 3, 1, 2, 1, 1, 12]
def baseStart_651684 : Nat := 118140960795 + 651684 * 2 ^ 59
def prefixEnd_651684 : Nat := 4983230072969 + 3 ^ 40 * 651684 * 2
def baseEnd_651684 : Nat := 8262398193697123877851

theorem tailTrace_651684 : CollatzResearch.WordTrace tailWord_651684 prefixEnd_651684 8262398193697123877851 := by
  unfold tailWord_651684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11884434085533820805681053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15845912114045094407574737 11884434085533820805681053)
  ·
    refine ⟨4456662782075182802130395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11884434085533820805681053 4456662782075182802130395)
    ·
      refine ⟨6684994173112774203195593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456662782075182802130395 6684994173112774203195593)
      ·
        refine ⟨5013745629834580652396695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6684994173112774203195593 5013745629834580652396695)
        ·
          refine ⟨7520618444751870978595043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013745629834580652396695 7520618444751870978595043)
          ·
            refine ⟨11280927667127806467892565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520618444751870978595043 11280927667127806467892565)
            ·
              refine ⟨8262398193697123877851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11280927667127806467892565 8262398193697123877851)
              ·
                rfl

theorem cell22_651684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 12].length) (baseStart_651684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651684 prefixEnd_651684 := by exact prefixLift 651684
  have htrace : WordTrace (prefixWord ++ tailWord_651684) baseStart_651684 baseEnd_651684 := by
    simpa [prefixWord, tailWord_651684, baseEnd_651684] using wordTrace_append hprefix tailTrace_651684
  have hstable : (prefixWord ++ tailWord_651684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651684).length < 2 ^ (prefixWord ++ tailWord_651684).sum := by decide
  have hdescent : baseEnd_651684 < baseStart_651684 := by decide
  rcases family_descends (prefixWord ++ tailWord_651684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651705 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_651705 : Nat := 118140960795 + 651705 * 2 ^ 59
def prefixEnd_651705 : Nat := 4983230072969 + 3 ^ 40 * 651705 * 2
def baseEnd_651705 : Nat := 223091939958985289926913

theorem tailTrace_651705 : CollatzResearch.WordTrace tailWord_651705 prefixEnd_651705 223091939958985289926913 := by
  unfold tailWord_651705
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769634103991562197876569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15846422735994374798584379 23769634103991562197876569)
  ·
    refine ⟨17827225577993671648407427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23769634103991562197876569 17827225577993671648407427)
    ·
      refine ⟨26740838366990507472611141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17827225577993671648407427 26740838366990507472611141)
      ·
        refine ⟨5013907193810720151114589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26740838366990507472611141 5013907193810720151114589)
        ·
          refine ⟨1880215197679020056667971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5013907193810720151114589 1880215197679020056667971)
          ·
            refine ⟨2820322796518530085001957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880215197679020056667971 2820322796518530085001957)
            ·
              refine ⟨528810524347224390937867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2820322796518530085001957 528810524347224390937867)
              ·
                refine ⟨793215786520836586406801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528810524347224390937867 793215786520836586406801)
                ·
                  refine ⟨594911839890627439805101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 793215786520836586406801 594911839890627439805101)
                  ·
                    refine ⟨223091939958985289926913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594911839890627439805101 223091939958985289926913)
                    ·
                      rfl

theorem cell22_651705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_651705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651705 prefixEnd_651705 := by exact prefixLift 651705
  have htrace : WordTrace (prefixWord ++ tailWord_651705) baseStart_651705 baseEnd_651705 := by
    simpa [prefixWord, tailWord_651705, baseEnd_651705] using wordTrace_append hprefix tailTrace_651705
  have hstable : (prefixWord ++ tailWord_651705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651705).length < 2 ^ (prefixWord ++ tailWord_651705).sum := by decide
  have hdescent : baseEnd_651705 < baseStart_651705 := by decide
  rcases family_descends (prefixWord ++ tailWord_651705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651729 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 9]
def baseStart_651729 : Nat := 118140960795 + 651729 * 2 ^ 59
def prefixEnd_651729 : Nat := 4983230072969 + 3 ^ 40 * 651729 * 2
def baseEnd_651729 : Nat := 74366718549819075775613

theorem tailTrace_651729 : CollatzResearch.WordTrace tailWord_651729 prefixEnd_651729 74366718549819075775613 := by
  unfold tailWord_651729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23770509455904614296750241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15847006303936409531166827 23770509455904614296750241)
  ·
    refine ⟨17827882091928460722562681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23770509455904614296750241 17827882091928460722562681)
    ·
      refine ⟨13370911568946345541922011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17827882091928460722562681 13370911568946345541922011)
      ·
        refine ⟨20056367353419518312883017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13370911568946345541922011 20056367353419518312883017)
        ·
          refine ⟨15042275515064638734662263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20056367353419518312883017 15042275515064638734662263)
          ·
            refine ⟨22563413272596958101993395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15042275515064638734662263 22563413272596958101993395)
            ·
              refine ⟨33845119908895437152990093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22563413272596958101993395 33845119908895437152990093)
              ·
                refine ⟨12691919965835788932371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33845119908895437152990093 12691919965835788932371285)
                ·
                  refine ⟨74366718549819075775613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12691919965835788932371285 74366718549819075775613)
                  ·
                    rfl

theorem cell22_651729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_651729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651729 prefixEnd_651729 := by exact prefixLift 651729
  have htrace : WordTrace (prefixWord ++ tailWord_651729) baseStart_651729 baseEnd_651729 := by
    simpa [prefixWord, tailWord_651729, baseEnd_651729] using wordTrace_append hprefix tailTrace_651729
  have hstable : (prefixWord ++ tailWord_651729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651729).length < 2 ^ (prefixWord ++ tailWord_651729).sum := by decide
  have hdescent : baseEnd_651729 < baseStart_651729 := by decide
  rcases family_descends (prefixWord ++ tailWord_651729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651761 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_651761 : Nat := 118140960795 + 651761 * 2 ^ 59
def prefixEnd_651761 : Nat := 4983230072969 + 3 ^ 40 * 651761 * 2
def baseEnd_651761 : Nat := 223111109903419810526741

theorem tailTrace_651761 : CollatzResearch.WordTrace tailWord_651761 prefixEnd_651761 223111109903419810526741 := by
  unfold tailWord_651761
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771676591788683761915137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15847784394525789174610091 23771676591788683761915137)
  ·
    refine ⟨17828757443841512821436353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23771676591788683761915137 17828757443841512821436353)
    ·
      refine ⟨13371568082881134616077265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17828757443841512821436353 13371568082881134616077265)
      ·
        refine ⟨10028676062160850962057949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13371568082881134616077265 10028676062160850962057949)
        ·
          refine ⟨3760753523310319110771731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10028676062160850962057949 3760753523310319110771731)
          ·
            refine ⟨5641130284965478666157597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760753523310319110771731 5641130284965478666157597)
            ·
              refine ⟨2115423856862054499809099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5641130284965478666157597 2115423856862054499809099)
              ·
                refine ⟨3173135785293081749713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115423856862054499809099 3173135785293081749713649)
                ·
                  refine ⟨2379851838969811312285237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173135785293081749713649 2379851838969811312285237)
                  ·
                    refine ⟨223111109903419810526741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2379851838969811312285237 223111109903419810526741)
                    ·
                      rfl

theorem cell22_651761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_651761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651761 prefixEnd_651761 := by exact prefixLift 651761
  have htrace : WordTrace (prefixWord ++ tailWord_651761) baseStart_651761 baseEnd_651761 := by
    simpa [prefixWord, tailWord_651761, baseEnd_651761] using wordTrace_append hprefix tailTrace_651761
  have hstable : (prefixWord ++ tailWord_651761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651761).length < 2 ^ (prefixWord ++ tailWord_651761).sum := by decide
  have hdescent : baseEnd_651761 < baseStart_651761 := by decide
  rcases family_descends (prefixWord ++ tailWord_651761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651853 : List Nat := [1, 6, 1, 1, 2, 1, 10]
def baseStart_651853 : Nat := 118140960795 + 651853 * 2 ^ 59
def prefixEnd_651853 : Nat := 4983230072969 + 3 ^ 40 * 651853 * 2
def baseEnd_651853 : Nat := 8264540866057860638017

theorem tailTrace_651853 : CollatzResearch.WordTrace tailWord_651853 prefixEnd_651853 8264540866057860638017 := by
  unfold tailWord_651853
  simp only [CollatzResearch.WordTrace]
  refine ⟨23775032107455383474264213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15850021404970255649509475 23775032107455383474264213)
  ·
    refine ⟨1114454630036971100356135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23775032107455383474264213 1114454630036971100356135)
    ·
      refine ⟨1671681945055456650534203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114454630036971100356135 1671681945055456650534203)
      ·
        refine ⟨2507522917583184975801305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671681945055456650534203 2507522917583184975801305)
        ·
          refine ⟨1880642188187388731850979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507522917583184975801305 1880642188187388731850979)
          ·
            refine ⟨2820963282281083097776469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880642188187388731850979 2820963282281083097776469)
            ·
              refine ⟨8264540866057860638017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2820963282281083097776469 8264540866057860638017)
              ·
                rfl

theorem cell22_651853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 10].length) (baseStart_651853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651853 prefixEnd_651853 := by exact prefixLift 651853
  have htrace : WordTrace (prefixWord ++ tailWord_651853) baseStart_651853 baseEnd_651853 := by
    simpa [prefixWord, tailWord_651853, baseEnd_651853] using wordTrace_append hprefix tailTrace_651853
  have hstable : (prefixWord ++ tailWord_651853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651853).length < 2 ^ (prefixWord ++ tailWord_651853).sum := by decide
  have hdescent : baseEnd_651853 < baseStart_651853 := by decide
  rcases family_descends (prefixWord ++ tailWord_651853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651874 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_651874 : Nat := 118140960795 + 651874 * 2 ^ 59
def prefixEnd_651874 : Nat := 4983230072969 + 3 ^ 40 * 651874 * 2
def baseEnd_651874 : Nat := 223149792112725182451395

theorem tailTrace_651874 : CollatzResearch.WordTrace tailWord_651874 prefixEnd_651874 223149792112725182451395 := by
  unfold tailWord_651874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943949510094826015194669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15850532026919536040519117 5943949510094826015194669)
  ·
    refine ⟨2228981066285559755698001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5943949510094826015194669 2228981066285559755698001)
    ·
      refine ⟨1671735799714169816773501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2228981066285559755698001 1671735799714169816773501)
      ·
        refine ⟨626900924892813681290063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1671735799714169816773501 626900924892813681290063)
        ·
          refine ⟨940351387339220521935095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626900924892813681290063 940351387339220521935095)
          ·
            refine ⟨1410527081008830782902643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940351387339220521935095 1410527081008830782902643)
            ·
              refine ⟨2115790621513246174353965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410527081008830782902643 2115790621513246174353965)
              ·
                refine ⟨793421483067467315382737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2115790621513246174353965 793421483067467315382737)
                ·
                  refine ⟨595066112300600486537053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 793421483067467315382737 595066112300600486537053)
                  ·
                    refine ⟨223149792112725182451395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595066112300600486537053 223149792112725182451395)
                    ·
                      rfl

theorem cell22_651874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_651874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651874 prefixEnd_651874 := by exact prefixLift 651874
  have htrace : WordTrace (prefixWord ++ tailWord_651874) baseStart_651874 baseEnd_651874 := by
    simpa [prefixWord, tailWord_651874, baseEnd_651874] using wordTrace_append hprefix tailTrace_651874
  have hstable : (prefixWord ++ tailWord_651874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651874).length < 2 ^ (prefixWord ++ tailWord_651874).sum := by decide
  have hdescent : baseEnd_651874 < baseStart_651874 := by decide
  rcases family_descends (prefixWord ++ tailWord_651874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651896 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_651896 : Nat := 118140960795 + 651896 * 2 ^ 59
def prefixEnd_651896 : Nat := 4983230072969 + 3 ^ 40 * 651896 * 2
def baseEnd_651896 : Nat := 223157323162324458401327

theorem tailTrace_651896 : CollatzResearch.WordTrace tailWord_651896 prefixEnd_651896 223157323162324458401327 := by
  unfold tailWord_651896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888300223149800909039771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15851066964199734545386361 11888300223149800909039771)
  ·
    refine ⟨17832450334724701363559657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888300223149800909039771 17832450334724701363559657)
    ·
      refine ⟨13374337751043526022669743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17832450334724701363559657 13374337751043526022669743)
      ·
        refine ⟨20061506626565289034004615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13374337751043526022669743 20061506626565289034004615)
        ·
          refine ⟨30092259939847933551006923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20061506626565289034004615 30092259939847933551006923)
          ·
            refine ⟨45138389909771900326510385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30092259939847933551006923 45138389909771900326510385)
            ·
              refine ⟨33853792432328925244882789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45138389909771900326510385 33853792432328925244882789)
              ·
                refine ⟨6347586081061673483415523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33853792432328925244882789 6347586081061673483415523)
                ·
                  refine ⟨9521379121592510225123285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347586081061673483415523 9521379121592510225123285)
                  ·
                    refine ⟨223157323162324458401327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9521379121592510225123285 223157323162324458401327)
                    ·
                      rfl

theorem cell22_651896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_651896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651896 prefixEnd_651896 := by exact prefixLift 651896
  have htrace : WordTrace (prefixWord ++ tailWord_651896) baseStart_651896 baseEnd_651896 := by
    simpa [prefixWord, tailWord_651896, baseEnd_651896] using wordTrace_append hprefix tailTrace_651896
  have hstable : (prefixWord ++ tailWord_651896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651896).length < 2 ^ (prefixWord ++ tailWord_651896).sum := by decide
  have hdescent : baseEnd_651896 < baseStart_651896 := by decide
  rcases family_descends (prefixWord ++ tailWord_651896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651928 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_651928 : Nat := 118140960795 + 651928 * 2 ^ 59
def prefixEnd_651928 : Nat := 4983230072969 + 3 ^ 40 * 651928 * 2
def baseEnd_651928 : Nat := 223168277416287041601229

theorem tailTrace_651928 : CollatzResearch.WordTrace tailWord_651928 prefixEnd_651928 223168277416287041601229 := by
  unfold tailWord_651928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888883791091835641622219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15851845054789114188829625 11888883791091835641622219)
  ·
    refine ⟨17833325686637753462433329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888883791091835641622219 17833325686637753462433329)
    ·
      refine ⟨13374994264978315096824997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17833325686637753462433329 13374994264978315096824997)
      ·
        refine ⟨2507811424683434080654687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13374994264978315096824997 2507811424683434080654687)
        ·
          refine ⟨3761717137025151120982031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507811424683434080654687 3761717137025151120982031)
          ·
            refine ⟨5642575705537726681473047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761717137025151120982031 5642575705537726681473047)
            ·
              refine ⟨8463863558306590022209571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642575705537726681473047 8463863558306590022209571)
              ·
                refine ⟨12695795337459885033314357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463863558306590022209571 12695795337459885033314357)
                ·
                  refine ⟨1190230812886864221873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12695795337459885033314357 1190230812886864221873221)
                  ·
                    refine ⟨223168277416287041601229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190230812886864221873221 223168277416287041601229)
                    ·
                      rfl

theorem cell22_651928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_651928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651928 prefixEnd_651928 := by exact prefixLift 651928
  have htrace : WordTrace (prefixWord ++ tailWord_651928) baseStart_651928 baseEnd_651928 := by
    simpa [prefixWord, tailWord_651928, baseEnd_651928] using wordTrace_append hprefix tailTrace_651928
  have hstable : (prefixWord ++ tailWord_651928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651928).length < 2 ^ (prefixWord ++ tailWord_651928).sum := by decide
  have hdescent : baseEnd_651928 < baseStart_651928 := by decide
  rcases family_descends (prefixWord ++ tailWord_651928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651975 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 2, 3]
def baseStart_651975 : Nat := 118140960795 + 651975 * 2 ^ 59
def prefixEnd_651975 : Nat := 4983230072969 + 3 ^ 40 * 651975 * 2
def baseEnd_651975 : Nat := 223184366476794585676085

theorem tailTrace_651975 : CollatzResearch.WordTrace tailWord_651975 prefixEnd_651975 223184366476794585676085 := by
  unfold tailWord_651975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23779481813013398310205379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15852987875342265540136919 23779481813013398310205379)
  ·
    refine ⟨35669222719520097465308069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23779481813013398310205379 35669222719520097465308069)
    ·
      refine ⟨6687979259910018274745263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35669222719520097465308069 6687979259910018274745263)
      ·
        refine ⟨10031968889865027412117895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687979259910018274745263 10031968889865027412117895)
        ·
          refine ⟨15047953334797541118176843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10031968889865027412117895 15047953334797541118176843)
          ·
            refine ⟨22571930002196311677265265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15047953334797541118176843 22571930002196311677265265)
            ·
              refine ⟨16928947501647233757948949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22571930002196311677265265 16928947501647233757948949)
              ·
                refine ⟨793544414139714082403857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16928947501647233757948949 793544414139714082403857)
                ·
                  refine ⟨595158310604785561802893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 793544414139714082403857 595158310604785561802893)
                  ·
                    refine ⟨223184366476794585676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595158310604785561802893 223184366476794585676085)
                    ·
                      rfl

theorem cell22_651975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_651975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_651975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_651975 prefixEnd_651975 := by exact prefixLift 651975
  have htrace : WordTrace (prefixWord ++ tailWord_651975) baseStart_651975 baseEnd_651975 := by
    simpa [prefixWord, tailWord_651975, baseEnd_651975] using wordTrace_append hprefix tailTrace_651975
  have hstable : (prefixWord ++ tailWord_651975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651975).length < 2 ^ (prefixWord ++ tailWord_651975).sum := by decide
  have hdescent : baseEnd_651975 < baseStart_651975 := by decide
  rcases family_descends (prefixWord ++ tailWord_651975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652005 : List Nat := [1, 3, 1, 4, 1, 2, 4, 6]
def baseStart_652005 : Nat := 118140960795 + 652005 * 2 ^ 59
def prefixEnd_652005 : Nat := 4983230072969 + 3 ^ 40 * 652005 * 2
def baseEnd_652005 : Nat := 24799404009987167491777

theorem tailTrace_652005 : CollatzResearch.WordTrace tailWord_652005 prefixEnd_652005 24799404009987167491777 := by
  unfold tailWord_652005
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780576002904713433797469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15853717335269808955864979 23780576002904713433797469)
  ·
    refine ⟨8917716001089267537674051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23780576002904713433797469 8917716001089267537674051)
    ·
      refine ⟨13376574001633901306511077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917716001089267537674051 13376574001633901306511077)
      ·
        refine ⟨2508107625306356494970827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13376574001633901306511077 2508107625306356494970827)
        ·
          refine ⟨3762161437959534742456241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508107625306356494970827 3762161437959534742456241)
          ·
            refine ⟨2821621078469651056842181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762161437959534742456241 2821621078469651056842181)
            ·
              refine ⟨529053952213059573157909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2821621078469651056842181 529053952213059573157909)
              ·
                refine ⟨24799404009987167491777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 529053952213059573157909 24799404009987167491777)
                ·
                  rfl

theorem cell22_652005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 6].length) (baseStart_652005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652005 prefixEnd_652005 := by exact prefixLift 652005
  have htrace : WordTrace (prefixWord ++ tailWord_652005) baseStart_652005 baseEnd_652005 := by
    simpa [prefixWord, tailWord_652005, baseEnd_652005] using wordTrace_append hprefix tailTrace_652005
  have hstable : (prefixWord ++ tailWord_652005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652005).length < 2 ^ (prefixWord ++ tailWord_652005).sum := by decide
  have hdescent : baseEnd_652005 < baseStart_652005 := by decide
  rcases family_descends (prefixWord ++ tailWord_652005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652037 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_652037 : Nat := 118140960795 + 652037 * 2 ^ 59
def prefixEnd_652037 : Nat := 4983230072969 + 3 ^ 40 * 652037 * 2
def baseEnd_652037 : Nat := 223205590343847090625895

theorem tailTrace_652037 : CollatzResearch.WordTrace tailWord_652037 prefixEnd_652037 223205590343847090625895 := by
  unfold tailWord_652037
  simp only [CollatzResearch.WordTrace]
  refine ⟨23781743138788782898962365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15854495425859188599308243 23781743138788782898962365)
  ·
    refine ⟨8918153677045793587110887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23781743138788782898962365 8918153677045793587110887)
    ·
      refine ⟨13377230515568690380666331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918153677045793587110887 13377230515568690380666331)
      ·
        refine ⟨20065845773353035570999497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13377230515568690380666331 20065845773353035570999497)
        ·
          refine ⟨15049384330014776678249623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20065845773353035570999497 15049384330014776678249623)
          ·
            refine ⟨22574076495022165017374435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15049384330014776678249623 22574076495022165017374435)
            ·
              refine ⟨33861114742533247526061653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22574076495022165017374435 33861114742533247526061653)
              ·
                refine ⟨396809938389061494446035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33861114742533247526061653 396809938389061494446035)
                ·
                  refine ⟨595214907583592241669053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396809938389061494446035 595214907583592241669053)
                  ·
                    refine ⟨223205590343847090625895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595214907583592241669053 223205590343847090625895)
                    ·
                      rfl

theorem cell22_652037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_652037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652037 prefixEnd_652037 := by exact prefixLift 652037
  have htrace : WordTrace (prefixWord ++ tailWord_652037) baseStart_652037 baseEnd_652037 := by
    simpa [prefixWord, tailWord_652037, baseEnd_652037] using wordTrace_append hprefix tailTrace_652037
  have hstable : (prefixWord ++ tailWord_652037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652037).length < 2 ^ (prefixWord ++ tailWord_652037).sum := by decide
  have hdescent : baseEnd_652037 < baseStart_652037 := by decide
  rcases family_descends (prefixWord ++ tailWord_652037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652080 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_652080 : Nat := 118140960795 + 652080 * 2 ^ 59
def prefixEnd_652080 : Nat := 4983230072969 + 3 ^ 40 * 652080 * 2
def baseEnd_652080 : Nat := 223220310122609311800763

theorem tailTrace_652080 : CollatzResearch.WordTrace tailWord_652080 prefixEnd_652080 223220310122609311800763 := by
  unfold tailWord_652080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891655738816500621388847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15855540985088667495185129 11891655738816500621388847)
  ·
    refine ⟨17837483608224750932083271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11891655738816500621388847 17837483608224750932083271)
    ·
      refine ⟨26756225412337126398124907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17837483608224750932083271 26756225412337126398124907)
      ·
        refine ⟨40134338118505689597187361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26756225412337126398124907 40134338118505689597187361)
        ·
          refine ⟨30100753588879267197890521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40134338118505689597187361 30100753588879267197890521)
          ·
            refine ⟨22575565191659450398417891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30100753588879267197890521 22575565191659450398417891)
            ·
              refine ⟨33863347787489175597626837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22575565191659450398417891 33863347787489175597626837)
              ·
                refine ⟨793672213769277553069379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33863347787489175597626837 793672213769277553069379)
                ·
                  refine ⟨1190508320653916329604069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793672213769277553069379 1190508320653916329604069)
                  ·
                    refine ⟨223220310122609311800763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190508320653916329604069 223220310122609311800763)
                    ·
                      rfl

theorem cell22_652080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_652080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652080 prefixEnd_652080 := by exact prefixLift 652080
  have htrace : WordTrace (prefixWord ++ tailWord_652080) baseStart_652080 baseEnd_652080 := by
    simpa [prefixWord, tailWord_652080, baseEnd_652080] using wordTrace_append hprefix tailTrace_652080
  have hstable : (prefixWord ++ tailWord_652080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652080).length < 2 ^ (prefixWord ++ tailWord_652080).sum := by decide
  have hdescent : baseEnd_652080 < baseStart_652080 := by decide
  rcases family_descends (prefixWord ++ tailWord_652080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652084 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_652084 : Nat := 118140960795 + 652084 * 2 ^ 59
def prefixEnd_652084 : Nat := 4983230072969 + 3 ^ 40 * 652084 * 2
def baseEnd_652084 : Nat := 74407226468118211566917

theorem tailTrace_652084 : CollatzResearch.WordTrace tailWord_652084 prefixEnd_652084 74407226468118211566917 := by
  unfold tailWord_652084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891728684809254962961653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15855638246412339950615537 11891728684809254962961653)
  ·
    refine ⟨1114849564200867652777655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11891728684809254962961653 1114849564200867652777655)
    ·
      refine ⟨1672274346301301479166483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114849564200867652777655 1672274346301301479166483)
      ·
        refine ⟨2508411519451952218749725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672274346301301479166483 2508411519451952218749725)
        ·
          refine ⟨940654319794482082031147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2508411519451952218749725 940654319794482082031147)
          ·
            refine ⟨1410981479691723123046721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940654319794482082031147 1410981479691723123046721)
            ·
              refine ⟨1058236109768792342285041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410981479691723123046721 1058236109768792342285041)
              ·
                refine ⟨793677082326594256713781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058236109768792342285041 793677082326594256713781)
                ·
                  refine ⟨74407226468118211566917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793677082326594256713781 74407226468118211566917)
                  ·
                    rfl

theorem cell22_652084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_652084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652084 prefixEnd_652084 := by exact prefixLift 652084
  have htrace : WordTrace (prefixWord ++ tailWord_652084) baseStart_652084 baseEnd_652084 := by
    simpa [prefixWord, tailWord_652084, baseEnd_652084] using wordTrace_append hprefix tailTrace_652084
  have hstable : (prefixWord ++ tailWord_652084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652084).length < 2 ^ (prefixWord ++ tailWord_652084).sum := by decide
  have hdescent : baseEnd_652084 < baseStart_652084 := by decide
  rcases family_descends (prefixWord ++ tailWord_652084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652172 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_652172 : Nat := 118140960795 + 652172 * 2 ^ 59
def prefixEnd_652172 : Nat := 4983230072969 + 3 ^ 40 * 652172 * 2
def baseEnd_652172 : Nat := 223251803602751738500481

theorem tailTrace_652172 : CollatzResearch.WordTrace tailWord_652172 prefixEnd_652172 223251803602751738500481 := by
  unfold tailWord_652172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893333496649850477563385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15857777995533133970084513 11893333496649850477563385)
  ·
    refine ⟨8920000122487387858172539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11893333496649850477563385 8920000122487387858172539)
    ·
      refine ⟨13380000183731081787258809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8920000122487387858172539 13380000183731081787258809)
      ·
        refine ⟨10035000137798311340444107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13380000183731081787258809 10035000137798311340444107)
        ·
          refine ⟨15052500206697467010666161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10035000137798311340444107 15052500206697467010666161)
          ·
            refine ⟨11289375155023100257999621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15052500206697467010666161 11289375155023100257999621)
            ·
              refine ⟨2116757841566831298374929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11289375155023100257999621 2116757841566831298374929)
              ·
                refine ⟨1587568381175123473781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116757841566831298374929 1587568381175123473781197)
                ·
                  refine ⟨595338142940671302667949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587568381175123473781197 595338142940671302667949)
                  ·
                    refine ⟨223251803602751738500481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595338142940671302667949 223251803602751738500481)
                    ·
                      rfl

theorem cell22_652172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_652172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652172 prefixEnd_652172 := by exact prefixLift 652172
  have htrace : WordTrace (prefixWord ++ tailWord_652172) baseStart_652172 baseEnd_652172 := by
    simpa [prefixWord, tailWord_652172, baseEnd_652172] using wordTrace_append hprefix tailTrace_652172
  have hstable : (prefixWord ++ tailWord_652172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652172).length < 2 ^ (prefixWord ++ tailWord_652172).sum := by decide
  have hdescent : baseEnd_652172 < baseStart_652172 := by decide
  rcases family_descends (prefixWord ++ tailWord_652172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652307 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 7, 3]
def baseStart_652307 : Nat := 118140960795 + 652307 * 2 ^ 59
def prefixEnd_652307 : Nat := 4983230072969 + 3 ^ 40 * 652307 * 2
def baseEnd_652307 : Nat := 223298016861656386375067

theorem tailTrace_652307 : CollatzResearch.WordTrace tailWord_652307 prefixEnd_652307 223298016861656386375067 := by
  unfold tailWord_652307
  simp only [CollatzResearch.WordTrace]
  refine ⟨23791590847810619011291175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15861060565207079340860783 23791590847810619011291175)
  ·
    refine ⟨35687386271715928516936763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23791590847810619011291175 35687386271715928516936763)
    ·
      refine ⟨53531079407573892775405145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35687386271715928516936763 53531079407573892775405145)
      ·
        refine ⟨40148309555680419581553859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53531079407573892775405145 40148309555680419581553859)
        ·
          refine ⟨60222464333520629372330789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40148309555680419581553859 60222464333520629372330789)
          ·
            refine ⟨11291712062535118007312023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60222464333520629372330789 11291712062535118007312023)
            ·
              refine ⟨16937568093802677010968035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11291712062535118007312023 16937568093802677010968035)
              ·
                refine ⟨25406352140704015516452053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937568093802677010968035 25406352140704015516452053)
                ·
                  refine ⟨595461378297750363666845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25406352140704015516452053 595461378297750363666845)
                  ·
                    refine ⟨223298016861656386375067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595461378297750363666845 223298016861656386375067)
                    ·
                      rfl

theorem cell22_652307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 3].length) (baseStart_652307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652307 prefixEnd_652307 := by exact prefixLift 652307
  have htrace : WordTrace (prefixWord ++ tailWord_652307) baseStart_652307 baseEnd_652307 := by
    simpa [prefixWord, tailWord_652307, baseEnd_652307] using wordTrace_append hprefix tailTrace_652307
  have hstable : (prefixWord ++ tailWord_652307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652307).length < 2 ^ (prefixWord ++ tailWord_652307).sum := by decide
  have hdescent : baseEnd_652307 < baseStart_652307 := by decide
  rcases family_descends (prefixWord ++ tailWord_652307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652444 : List Nat := [2, 2, 3, 2, 1, 2, 3, 7]
def baseStart_652444 : Nat := 118140960795 + 652444 * 2 ^ 59
def prefixEnd_652444 : Nat := 4983230072969 + 3 ^ 40 * 652444 * 2
def baseEnd_652444 : Nat := 24816101640159299522183

theorem tailTrace_652444 : CollatzResearch.WordTrace tailWord_652444 prefixEnd_652444 24816101640159299522183 := by
  unfold tailWord_652444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11898293824157145704514193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15864391765542860939352257 11898293824157145704514193)
  ·
    refine ⟨8923720368117859278385645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11898293824157145704514193 8923720368117859278385645)
    ·
      refine ⟨3346395138044197229394617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8923720368117859278385645 3346395138044197229394617)
      ·
        refine ⟨2509796353533147922045963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3346395138044197229394617 2509796353533147922045963)
        ·
          refine ⟨3764694530299721883068945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509796353533147922045963 3764694530299721883068945)
          ·
            refine ⟨2823520897724791412301709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764694530299721883068945 2823520897724791412301709)
            ·
              refine ⟨1058820336646796779613141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2823520897724791412301709 1058820336646796779613141)
              ·
                refine ⟨24816101640159299522183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1058820336646796779613141 24816101640159299522183)
                ·
                  rfl

theorem cell22_652444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_652444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652444 prefixEnd_652444 := by exact prefixLift 652444
  have htrace : WordTrace (prefixWord ++ tailWord_652444) baseStart_652444 baseEnd_652444 := by
    simpa [prefixWord, tailWord_652444, baseEnd_652444] using wordTrace_append hprefix tailTrace_652444
  have hstable : (prefixWord ++ tailWord_652444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652444).length < 2 ^ (prefixWord ++ tailWord_652444).sum := by decide
  have hdescent : baseEnd_652444 < baseStart_652444 := by decide
  rcases family_descends (prefixWord ++ tailWord_652444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652527 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 1, 3]
def baseStart_652527 : Nat := 118140960795 + 652527 * 2 ^ 59
def prefixEnd_652527 : Nat := 4983230072969 + 3 ^ 40 * 652527 * 2
def baseEnd_652527 : Nat := 223373327357649145874393

theorem tailTrace_652527 : CollatzResearch.WordTrace tailWord_652527 prefixEnd_652527 223373327357649145874393 := by
  unfold tailWord_652527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23799614907013596584299835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15866409938009064389533223 23799614907013596584299835)
  ·
    refine ⟨35699422360520394876449753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23799614907013596584299835 35699422360520394876449753)
    ·
      refine ⟨26774566770390296157337315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35699422360520394876449753 26774566770390296157337315)
      ·
        refine ⟨40161850155585444236005973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26774566770390296157337315 40161850155585444236005973)
        ·
          refine ⟨470646681510766924640695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 40161850155585444236005973 470646681510766924640695)
          ·
            refine ⟨705970022266150386961043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470646681510766924640695 705970022266150386961043)
            ·
              refine ⟨1058955033399225580441565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705970022266150386961043 1058955033399225580441565)
              ·
                refine ⟨397108137524709592665587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058955033399225580441565 397108137524709592665587)
                ·
                  refine ⟨595662206287064388998381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397108137524709592665587 595662206287064388998381)
                  ·
                    refine ⟨223373327357649145874393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595662206287064388998381 223373327357649145874393)
                    ·
                      rfl

theorem cell22_652527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_652527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652527 prefixEnd_652527 := by exact prefixLift 652527
  have htrace : WordTrace (prefixWord ++ tailWord_652527) baseStart_652527 baseEnd_652527 := by
    simpa [prefixWord, tailWord_652527, baseEnd_652527] using wordTrace_append hprefix tailTrace_652527
  have hstable : (prefixWord ++ tailWord_652527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652527).length < 2 ^ (prefixWord ++ tailWord_652527).sum := by decide
  have hdescent : baseEnd_652527 < baseStart_652527 := by decide
  rcases family_descends (prefixWord ++ tailWord_652527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652579 : List Nat := [1, 1, 1, 4, 2, 3, 2, 8]
def baseStart_652579 : Nat := 118140960795 + 652579 * 2 ^ 59
def prefixEnd_652579 : Nat := 4983230072969 + 3 ^ 40 * 652579 * 2
def baseEnd_652579 : Nat := 24821236446704260397137

theorem tailTrace_652579 : CollatzResearch.WordTrace tailWord_652579 prefixEnd_652579 24821236446704260397137 := by
  unfold tailWord_652579
  simp only [CollatzResearch.WordTrace]
  refine ⟨23801511502825209465192791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15867674335216806310128527 23801511502825209465192791)
  ·
    refine ⟨35702267254237814197789187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23801511502825209465192791 35702267254237814197789187)
    ·
      refine ⟨53553400881356721296683781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35702267254237814197789187 53553400881356721296683781)
      ·
        refine ⟨10041262665254385243128209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53553400881356721296683781 10041262665254385243128209)
        ·
          refine ⟨7530946998940788932346157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10041262665254385243128209 7530946998940788932346157)
          ·
            refine ⟨2824105124602795849629809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7530946998940788932346157 2824105124602795849629809)
            ·
              refine ⟨2118078843452096887222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824105124602795849629809 2118078843452096887222357)
              ·
                refine ⟨24821236446704260397137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2118078843452096887222357 24821236446704260397137)
                ·
                  rfl

theorem cell22_652579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_652579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652579 prefixEnd_652579 := by exact prefixLift 652579
  have htrace : WordTrace (prefixWord ++ tailWord_652579) baseStart_652579 baseEnd_652579 := by
    simpa [prefixWord, tailWord_652579, baseEnd_652579] using wordTrace_append hprefix tailTrace_652579
  have hstable : (prefixWord ++ tailWord_652579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652579).length < 2 ^ (prefixWord ++ tailWord_652579).sum := by decide
  have hdescent : baseEnd_652579 < baseStart_652579 := by decide
  rcases family_descends (prefixWord ++ tailWord_652579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652581 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_652581 : Nat := 118140960795 + 652581 * 2 ^ 59
def prefixEnd_652581 : Nat := 4983230072969 + 3 ^ 40 * 652581 * 2
def baseEnd_652581 : Nat := 223391812661211005024227

theorem tailTrace_652581 : CollatzResearch.WordTrace tailWord_652581 prefixEnd_652581 223391812661211005024227 := by
  unfold tailWord_652581
  simp only [CollatzResearch.WordTrace]
  refine ⟨23801584448817963806765597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15867722965878642537843731 23801584448817963806765597)
  ·
    refine ⟨8925594168306736427537099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23801584448817963806765597 8925594168306736427537099)
    ·
      refine ⟨13388391252460104641305649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8925594168306736427537099 13388391252460104641305649)
      ·
        refine ⟨10041293439345078480979237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13388391252460104641305649 10041293439345078480979237)
        ·
          refine ⟨1882742519877202215183607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10041293439345078480979237 1882742519877202215183607)
          ·
            refine ⟨2824113779815803322775411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882742519877202215183607 2824113779815803322775411)
            ·
              refine ⟨4236170669723704984163117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824113779815803322775411 4236170669723704984163117)
              ·
                refine ⟨1588564001146389369061169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4236170669723704984163117 1588564001146389369061169)
                ·
                  refine ⟨1191423000859792026795877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588564001146389369061169 1191423000859792026795877)
                  ·
                    refine ⟨223391812661211005024227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191423000859792026795877 223391812661211005024227)
                    ·
                      rfl

theorem cell22_652581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_652581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652581 prefixEnd_652581 := by exact prefixLift 652581
  have htrace : WordTrace (prefixWord ++ tailWord_652581) baseStart_652581 baseEnd_652581 := by
    simpa [prefixWord, tailWord_652581, baseEnd_652581] using wordTrace_append hprefix tailTrace_652581
  have hstable : (prefixWord ++ tailWord_652581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652581).length < 2 ^ (prefixWord ++ tailWord_652581).sum := by decide
  have hdescent : baseEnd_652581 < baseStart_652581 := by decide
  rcases family_descends (prefixWord ++ tailWord_652581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652611 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 3, 3]
def baseStart_652611 : Nat := 118140960795 + 652611 * 2 ^ 59
def prefixEnd_652611 : Nat := 4983230072969 + 3 ^ 40 * 652611 * 2
def baseEnd_652611 : Nat := 223402082274300926774135

theorem tailTrace_652611 : CollatzResearch.WordTrace tailWord_652611 prefixEnd_652611 223402082274300926774135 := by
  unfold tailWord_652611
  simp only [CollatzResearch.WordTrace]
  refine ⟨23802678638709278930357687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15868452425806185953571791 23802678638709278930357687)
  ·
    refine ⟨35704017958063918395536531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23802678638709278930357687 35704017958063918395536531)
    ·
      refine ⟨53556026937095877593304797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35704017958063918395536531 53556026937095877593304797)
      ·
        refine ⟨20083510101410954097489299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53556026937095877593304797 20083510101410954097489299)
        ·
          refine ⟨30125265152116431146233949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20083510101410954097489299 30125265152116431146233949)
          ·
            refine ⟨11296974432043661679837731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30125265152116431146233949 11296974432043661679837731)
            ·
              refine ⟨16945461648065492519756597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296974432043661679837731 16945461648065492519756597)
              ·
                refine ⟨1588637029506139923727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16945461648065492519756597 1588637029506139923727181)
                ·
                  refine ⟨595738886064802471397693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1588637029506139923727181 595738886064802471397693)
                  ·
                    refine ⟨223402082274300926774135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595738886064802471397693 223402082274300926774135)
                    ·
                      rfl

theorem cell22_652611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].length) (baseStart_652611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652611 prefixEnd_652611 := by exact prefixLift 652611
  have htrace : WordTrace (prefixWord ++ tailWord_652611) baseStart_652611 baseEnd_652611 := by
    simpa [prefixWord, tailWord_652611, baseEnd_652611] using wordTrace_append hprefix tailTrace_652611
  have hstable : (prefixWord ++ tailWord_652611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652611).length < 2 ^ (prefixWord ++ tailWord_652611).sum := by decide
  have hdescent : baseEnd_652611 < baseStart_652611 := by decide
  rcases family_descends (prefixWord ++ tailWord_652611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652628 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_652628 : Nat := 118140960795 + 652628 * 2 ^ 59
def prefixEnd_652628 : Nat := 4983230072969 + 3 ^ 40 * 652628 * 2
def baseEnd_652628 : Nat := 223407901721718549099083

theorem tailTrace_652628 : CollatzResearch.WordTrace tailWord_652628 prefixEnd_652628 223407901721718549099083 := by
  unfold tailWord_652628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901649339823845416863269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15868865786431793889151025 11901649339823845416863269)
  ·
    refine ⟨2231559251216971015661863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11901649339823845416863269 2231559251216971015661863)
    ·
      refine ⟨3347338876825456523492795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231559251216971015661863 3347338876825456523492795)
      ·
        refine ⟨5021008315238184785239193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347338876825456523492795 5021008315238184785239193)
        ·
          refine ⟨3765756236428638588929395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5021008315238184785239193 3765756236428638588929395)
          ·
            refine ⟨5648634354642957883394093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765756236428638588929395 5648634354642957883394093)
            ·
              refine ⟨2118237882991109206272785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5648634354642957883394093 2118237882991109206272785)
              ·
                refine ⟨1588678412243331904704589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118237882991109206272785 1588678412243331904704589)
                ·
                  refine ⟨595754404591249464264221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1588678412243331904704589 595754404591249464264221)
                  ·
                    refine ⟨223407901721718549099083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595754404591249464264221 223407901721718549099083)
                    ·
                      rfl

theorem cell22_652628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_652628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652628 prefixEnd_652628 := by exact prefixLift 652628
  have htrace : WordTrace (prefixWord ++ tailWord_652628) baseStart_652628 baseEnd_652628 := by
    simpa [prefixWord, tailWord_652628, baseEnd_652628] using wordTrace_append hprefix tailTrace_652628
  have hstable : (prefixWord ++ tailWord_652628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652628).length < 2 ^ (prefixWord ++ tailWord_652628).sum := by decide
  have hdescent : baseEnd_652628 < baseStart_652628 := by decide
  rcases family_descends (prefixWord ++ tailWord_652628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652639 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_652639 : Nat := 118140960795 + 652639 * 2 ^ 59
def prefixEnd_652639 : Nat := 4983230072969 + 3 ^ 40 * 652639 * 2
def baseEnd_652639 : Nat := 223411667246518187074049

theorem tailTrace_652639 : CollatzResearch.WordTrace tailWord_652639 prefixEnd_652639 223411667246518187074049 := by
  unfold tailWord_652639
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803699882607839712376971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15869133255071893141584647 23803699882607839712376971)
  ·
    refine ⟨35705549823911759568565457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23803699882607839712376971 35705549823911759568565457)
    ·
      refine ⟨26779162367933819676424093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35705549823911759568565457 26779162367933819676424093)
      ·
        refine ⟨10042185887975182378659035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26779162367933819676424093 10042185887975182378659035)
        ·
          refine ⟨15063278831962773567988553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042185887975182378659035 15063278831962773567988553)
          ·
            refine ⟨11297459123972080175991415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15063278831962773567988553 11297459123972080175991415)
            ·
              refine ⟨16946188685958120263987123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297459123972080175991415 16946188685958120263987123)
              ·
                refine ⟨25419283028937180395980685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16946188685958120263987123 25419283028937180395980685)
                ·
                  refine ⟨9532231135851442648492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25419283028937180395980685 9532231135851442648492757)
                  ·
                    refine ⟨223411667246518187074049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9532231135851442648492757 223411667246518187074049)
                    ·
                      rfl

theorem cell22_652639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_652639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652639 prefixEnd_652639 := by exact prefixLift 652639
  have htrace : WordTrace (prefixWord ++ tailWord_652639) baseStart_652639 baseEnd_652639 := by
    simpa [prefixWord, tailWord_652639, baseEnd_652639] using wordTrace_append hprefix tailTrace_652639
  have hstable : (prefixWord ++ tailWord_652639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652639).length < 2 ^ (prefixWord ++ tailWord_652639).sum := by decide
  have hdescent : baseEnd_652639 < baseStart_652639 := by decide
  rcases family_descends (prefixWord ++ tailWord_652639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652645 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_652645 : Nat := 118140960795 + 652645 * 2 ^ 59
def prefixEnd_652645 : Nat := 4983230072969 + 3 ^ 40 * 652645 * 2
def baseEnd_652645 : Nat := 223413721169136171424031

theorem tailTrace_652645 : CollatzResearch.WordTrace tailWord_652645 prefixEnd_652645 223413721169136171424031 := by
  unfold tailWord_652645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803918720586102737095389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15869279147057401824730259 23803918720586102737095389)
  ·
    refine ⟨8926469520219788526410771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23803918720586102737095389 8926469520219788526410771)
    ·
      refine ⟨13389704280329682789616157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8926469520219788526410771 13389704280329682789616157)
      ·
        refine ⟨5021139105123631046106059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13389704280329682789616157 5021139105123631046106059)
        ·
          refine ⟨7531708657685446569159089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5021139105123631046106059 7531708657685446569159089)
          ·
            refine ⟨5648781493264084926869317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7531708657685446569159089 5648781493264084926869317)
            ·
              refine ⟨1059146529987015923787997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5648781493264084926869317 1059146529987015923787997)
              ·
                refine ⟨397179948745130971420499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059146529987015923787997 397179948745130971420499)
                ·
                  refine ⟨595769923117696457130749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397179948745130971420499 595769923117696457130749)
                  ·
                    refine ⟨223413721169136171424031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595769923117696457130749 223413721169136171424031)
                    ·
                      rfl

theorem cell22_652645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_652645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652645 prefixEnd_652645 := by exact prefixLift 652645
  have htrace : WordTrace (prefixWord ++ tailWord_652645) baseStart_652645 baseEnd_652645 := by
    simpa [prefixWord, tailWord_652645, baseEnd_652645] using wordTrace_append hprefix tailTrace_652645
  have hstable : (prefixWord ++ tailWord_652645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652645).length < 2 ^ (prefixWord ++ tailWord_652645).sum := by decide
  have hdescent : baseEnd_652645 < baseStart_652645 := by decide
  rcases family_descends (prefixWord ++ tailWord_652645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652716 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_652716 : Nat := 118140960795 + 652716 * 2 ^ 59
def prefixEnd_652716 : Nat := 4983230072969 + 3 ^ 40 * 652716 * 2
def baseEnd_652716 : Nat := 223438025920115652898813

theorem tailTrace_652716 : CollatzResearch.WordTrace tailWord_652716 prefixEnd_652716 223438025920115652898813 := by
  unfold tailWord_652716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903254151664440931465001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15871005535552587908620001 11903254151664440931465001)
  ·
    refine ⟨8927440613748330698598751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11903254151664440931465001 8927440613748330698598751)
    ·
      refine ⟨13391160920622496047898127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927440613748330698598751 13391160920622496047898127)
      ·
        refine ⟨20086741380933744071847191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391160920622496047898127 20086741380933744071847191)
        ·
          refine ⟨30130112071400616107770787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20086741380933744071847191 30130112071400616107770787)
          ·
            refine ⟨45195168107100924161656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130112071400616107770787 45195168107100924161656181)
            ·
              refine ⟨4237047010040711640155267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45195168107100924161656181 4237047010040711640155267)
              ·
                refine ⟨6355570515061067460232901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237047010040711640155267 6355570515061067460232901)
                ·
                  refine ⟨1191669471573950148793669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6355570515061067460232901 1191669471573950148793669)
                  ·
                    refine ⟨223438025920115652898813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191669471573950148793669 223438025920115652898813)
                    ·
                      rfl

theorem cell22_652716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_652716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652716 prefixEnd_652716 := by exact prefixLift 652716
  have htrace : WordTrace (prefixWord ++ tailWord_652716) baseStart_652716 baseEnd_652716 := by
    simpa [prefixWord, tailWord_652716, baseEnd_652716] using wordTrace_append hprefix tailTrace_652716
  have hstable : (prefixWord ++ tailWord_652716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652716).length < 2 ^ (prefixWord ++ tailWord_652716).sum := by decide
  have hdescent : baseEnd_652716 < baseStart_652716 := by decide
  rcases family_descends (prefixWord ++ tailWord_652716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652814 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_652814 : Nat := 118140960795 + 652814 * 2 ^ 59
def prefixEnd_652814 : Nat := 4983230072969 + 3 ^ 40 * 652814 * 2
def baseEnd_652814 : Nat := 223471573322876063948513

theorem tailTrace_652814 : CollatzResearch.WordTrace tailWord_652814 prefixEnd_652814 223471573322876063948513 := by
  unfold tailWord_652814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976260332121730574999687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15873388437982563066664997 2976260332121730574999687)
  ·
    refine ⟨4464390498182595862499531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976260332121730574999687 4464390498182595862499531)
    ·
      refine ⟨6696585747273893793749297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4464390498182595862499531 6696585747273893793749297)
      ·
        refine ⟨5022439310455420345311973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6696585747273893793749297 5022439310455420345311973)
        ·
          refine ⟨941707370710391314745995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5022439310455420345311973 941707370710391314745995)
          ·
            refine ⟨1412561056065586972118993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941707370710391314745995 1412561056065586972118993)
            ·
              refine ⟨1059420792049190229089245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412561056065586972118993 1059420792049190229089245)
              ·
                refine ⟨397282797018446335908467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059420792049190229089245 397282797018446335908467)
                ·
                  refine ⟨595924195527669503862701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397282797018446335908467 595924195527669503862701)
                  ·
                    refine ⟨223471573322876063948513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595924195527669503862701 223471573322876063948513)
                    ·
                      rfl

theorem cell22_652814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_652814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652814 prefixEnd_652814 := by exact prefixLift 652814
  have htrace : WordTrace (prefixWord ++ tailWord_652814) baseStart_652814 baseEnd_652814 := by
    simpa [prefixWord, tailWord_652814, baseEnd_652814] using wordTrace_append hprefix tailTrace_652814
  have hstable : (prefixWord ++ tailWord_652814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652814).length < 2 ^ (prefixWord ++ tailWord_652814).sum := by decide
  have hdescent : baseEnd_652814 < baseStart_652814 := by decide
  rcases family_descends (prefixWord ++ tailWord_652814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652904 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_652904 : Nat := 118140960795 + 652904 * 2 ^ 59
def prefixEnd_652904 : Nat := 4983230072969 + 3 ^ 40 * 652904 * 2
def baseEnd_652904 : Nat := 223502382162145829198237

theorem tailTrace_652904 : CollatzResearch.WordTrace tailWord_652904 prefixEnd_652904 223502382162145829198237 := by
  unfold tailWord_652904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11906682613323894985386883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15875576817765193313849177 11906682613323894985386883)
  ·
    refine ⟨17860023919985842478080325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11906682613323894985386883 17860023919985842478080325)
    ·
      refine ⟨3348754484997345464640061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17860023919985842478080325 3348754484997345464640061)
      ·
        refine ⟨1255782931874004549240023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3348754484997345464640061 1255782931874004549240023)
        ·
          refine ⟨1883674397811006823860035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255782931874004549240023 1883674397811006823860035)
          ·
            refine ⟨2825511596716510235790053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883674397811006823860035 2825511596716510235790053)
            ·
              refine ⟨529783424384345669210635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2825511596716510235790053 529783424384345669210635)
              ·
                refine ⟨794675136576518503815953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529783424384345669210635 794675136576518503815953)
                ·
                  refine ⟨596006352432388877861965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794675136576518503815953 596006352432388877861965)
                  ·
                    refine ⟨223502382162145829198237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596006352432388877861965 223502382162145829198237)
                    ·
                      rfl

theorem cell22_652904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_652904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652904 prefixEnd_652904 := by exact prefixLift 652904
  have htrace : WordTrace (prefixWord ++ tailWord_652904) baseStart_652904 baseEnd_652904 := by
    simpa [prefixWord, tailWord_652904, baseEnd_652904] using wordTrace_append hprefix tailTrace_652904
  have hstable : (prefixWord ++ tailWord_652904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652904).length < 2 ^ (prefixWord ++ tailWord_652904).sum := by decide
  have hdescent : baseEnd_652904 < baseStart_652904 := by decide
  rcases family_descends (prefixWord ++ tailWord_652904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652960 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_652960 : Nat := 118140960795 + 652960 * 2 ^ 59
def prefixEnd_652960 : Nat := 4983230072969 + 3 ^ 40 * 652960 * 2
def baseEnd_652960 : Nat := 223521552106580349798065

theorem tailTrace_652960 : CollatzResearch.WordTrace tailWord_652960 prefixEnd_652960 223521552106580349798065 := by
  unfold tailWord_652960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907703857222455767406167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15876938476296607689874889 11907703857222455767406167)
  ·
    refine ⟨17861555785833683651109251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907703857222455767406167 17861555785833683651109251)
    ·
      refine ⟨26792333678750525476663877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17861555785833683651109251 26792333678750525476663877)
      ·
        refine ⟨5023562564765723526874477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26792333678750525476663877 5023562564765723526874477)
        ·
          refine ⟨1883835961787146322577929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5023562564765723526874477 1883835961787146322577929)
          ·
            refine ⟨1412876971340359741933447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883835961787146322577929 1412876971340359741933447)
            ·
              refine ⟨2119315457010539612900171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412876971340359741933447 2119315457010539612900171)
              ·
                refine ⟨3178973185515809419350257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119315457010539612900171 3178973185515809419350257)
                ·
                  refine ⟨2384229889136857064512693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178973185515809419350257 2384229889136857064512693)
                  ·
                    refine ⟨223521552106580349798065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2384229889136857064512693 223521552106580349798065)
                    ·
                      rfl

theorem cell22_652960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_652960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652960 prefixEnd_652960 := by exact prefixLift 652960
  have htrace : WordTrace (prefixWord ++ tailWord_652960) baseStart_652960 baseEnd_652960 := by
    simpa [prefixWord, tailWord_652960, baseEnd_652960] using wordTrace_append hprefix tailTrace_652960
  have hstable : (prefixWord ++ tailWord_652960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652960).length < 2 ^ (prefixWord ++ tailWord_652960).sum := by decide
  have hdescent : baseEnd_652960 < baseStart_652960 := by decide
  rcases family_descends (prefixWord ++ tailWord_652960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652975 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 1, 4]
def baseStart_652975 : Nat := 118140960795 + 652975 * 2 ^ 59
def prefixEnd_652975 : Nat := 4983230072969 + 3 ^ 40 * 652975 * 2
def baseEnd_652975 : Nat := 223526686913125310673019

theorem tailTrace_652975 : CollatzResearch.WordTrace tailWord_652975 prefixEnd_652975 223526686913125310673019 := by
  unfold tailWord_652975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815954809390569096608379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15877303206260379397738919 23815954809390569096608379)
  ·
    refine ⟨35723932214085853644912569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815954809390569096608379 35723932214085853644912569)
    ·
      refine ⟨26792949160564390233684427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35723932214085853644912569 26792949160564390233684427)
      ·
        refine ⟨40189423740846585350526641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26792949160564390233684427 40189423740846585350526641)
        ·
          refine ⟨30142067805634939012894981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40189423740846585350526641 30142067805634939012894981)
          ·
            refine ⟨5651637713556551064917809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30142067805634939012894981 5651637713556551064917809)
            ·
              refine ⟨4238728285167413298688357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5651637713556551064917809 4238728285167413298688357)
              ·
                refine ⟨794761553468889993504067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4238728285167413298688357 794761553468889993504067)
                ·
                  refine ⟨1192142330203334990256101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794761553468889993504067 1192142330203334990256101)
                  ·
                    refine ⟨223526686913125310673019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192142330203334990256101 223526686913125310673019)
                    ·
                      rfl

theorem cell22_652975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_652975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_652975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_652975 prefixEnd_652975 := by exact prefixLift 652975
  have htrace : WordTrace (prefixWord ++ tailWord_652975) baseStart_652975 baseEnd_652975 := by
    simpa [prefixWord, tailWord_652975, baseEnd_652975] using wordTrace_append hprefix tailTrace_652975
  have hstable : (prefixWord ++ tailWord_652975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652975).length < 2 ^ (prefixWord ++ tailWord_652975).sum := by decide
  have hdescent : baseEnd_652975 < baseStart_652975 := by decide
  rcases family_descends (prefixWord ++ tailWord_652975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653033 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_653033 : Nat := 118140960795 + 653033 * 2 ^ 59
def prefixEnd_653033 : Nat := 4983230072969 + 3 ^ 40 * 653033 * 2
def baseEnd_653033 : Nat := 223546541498432492722841

theorem tailTrace_653033 : CollatzResearch.WordTrace tailWord_653033 prefixEnd_653033 223546541498432492722841 := by
  unfold tailWord_653033
  simp only [CollatzResearch.WordTrace]
  refine ⟨23818070243180445002219753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15878713495453630001479835 23818070243180445002219753)
  ·
    refine ⟨17863552682385333751664815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23818070243180445002219753 17863552682385333751664815)
    ·
      refine ⟨26795329023578000627497223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863552682385333751664815 26795329023578000627497223)
      ·
        refine ⟨40192993535367000941245835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795329023578000627497223 40192993535367000941245835)
        ·
          refine ⟨60289490303050501411868753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40192993535367000941245835 60289490303050501411868753)
          ·
            refine ⟨45217117727287876058901565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60289490303050501411868753 45217117727287876058901565)
            ·
              refine ⟨16956419147732953522088087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45217117727287876058901565 16956419147732953522088087)
              ·
                refine ⟨25434628721599430283132131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16956419147732953522088087 25434628721599430283132131)
                ·
                  refine ⟨38151943082399145424698197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25434628721599430283132131 38151943082399145424698197)
                  ·
                    refine ⟨223546541498432492722841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38151943082399145424698197 223546541498432492722841)
                    ·
                      rfl

theorem cell22_653033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_653033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653033 prefixEnd_653033 := by exact prefixLift 653033
  have htrace : WordTrace (prefixWord ++ tailWord_653033) baseStart_653033 baseEnd_653033 := by
    simpa [prefixWord, tailWord_653033, baseEnd_653033] using wordTrace_append hprefix tailTrace_653033
  have hstable : (prefixWord ++ tailWord_653033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653033).length < 2 ^ (prefixWord ++ tailWord_653033).sum := by decide
  have hdescent : baseEnd_653033 < baseStart_653033 := by decide
  rcases family_descends (prefixWord ++ tailWord_653033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653035 : List Nat := [1, 1, 1, 1, 2, 4, 6, 6]
def baseStart_653035 : Nat := 118140960795 + 653035 * 2 ^ 59
def prefixEnd_653035 : Nat := 4983230072969 + 3 ^ 40 * 653035 * 2
def baseEnd_653035 : Nat := 24838580682145017130315

theorem tailTrace_653035 : CollatzResearch.WordTrace tailWord_653035 prefixEnd_653035 24838580682145017130315 := by
  unfold tailWord_653035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23818143189173199343792559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15878762126115466229195039 23818143189173199343792559)
  ·
    refine ⟨35727214783759799015688839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23818143189173199343792559 35727214783759799015688839)
    ·
      refine ⟨53590822175639698523533259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35727214783759799015688839 53590822175639698523533259)
      ·
        refine ⟨80386233263459547785299889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53590822175639698523533259 80386233263459547785299889)
        ·
          refine ⟨60289674947594660838974917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80386233263459547785299889 60289674947594660838974917)
          ·
            refine ⟨11304314052673998907307797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60289674947594660838974917 11304314052673998907307797)
            ·
              refine ⟨529889721219093698780053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11304314052673998907307797 529889721219093698780053)
              ·
                refine ⟨24838580682145017130315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 529889721219093698780053 24838580682145017130315)
                ·
                  rfl

theorem cell22_653035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6].length) (baseStart_653035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653035 prefixEnd_653035 := by exact prefixLift 653035
  have htrace : WordTrace (prefixWord ++ tailWord_653035) baseStart_653035 baseEnd_653035 := by
    simpa [prefixWord, tailWord_653035, baseEnd_653035] using wordTrace_append hprefix tailTrace_653035
  have hstable : (prefixWord ++ tailWord_653035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653035).length < 2 ^ (prefixWord ++ tailWord_653035).sum := by decide
  have hdescent : baseEnd_653035 < baseStart_653035 := by decide
  rcases family_descends (prefixWord ++ tailWord_653035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653054 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_653054 : Nat := 118140960795 + 653054 * 2 ^ 59
def prefixEnd_653054 : Nat := 4983230072969 + 3 ^ 40 * 653054 * 2
def baseEnd_653054 : Nat := 223553730227595437947777

theorem tailTrace_653054 : CollatzResearch.WordTrace tailWord_653054 prefixEnd_653054 223553730227595437947777 := by
  unfold tailWord_653054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977354522013045698591777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15879224117402910392489477 2977354522013045698591777)
  ·
    refine ⟨2233015891509784273943833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2977354522013045698591777 2233015891509784273943833)
    ·
      refine ⟨1674761918632338205457875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2233015891509784273943833 1674761918632338205457875)
      ·
        refine ⟨2512142877948507308186813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674761918632338205457875 2512142877948507308186813)
        ·
          refine ⟨942053579230690240570055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2512142877948507308186813 942053579230690240570055)
          ·
            refine ⟨1413080368846035360855083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942053579230690240570055 1413080368846035360855083)
            ·
              refine ⟨2119620553269053041282625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413080368846035360855083 2119620553269053041282625)
              ·
                refine ⟨1589715414951789780961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119620553269053041282625 1589715414951789780961969)
                ·
                  refine ⟨1192286561213842335721477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589715414951789780961969 1192286561213842335721477)
                  ·
                    refine ⟨223553730227595437947777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192286561213842335721477 223553730227595437947777)
                    ·
                      rfl

theorem cell22_653054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_653054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653054 prefixEnd_653054 := by exact prefixLift 653054
  have htrace : WordTrace (prefixWord ++ tailWord_653054) baseStart_653054 baseEnd_653054 := by
    simpa [prefixWord, tailWord_653054, baseEnd_653054] using wordTrace_append hprefix tailTrace_653054
  have hstable : (prefixWord ++ tailWord_653054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653054).length < 2 ^ (prefixWord ++ tailWord_653054).sum := by decide
  have hdescent : baseEnd_653054 < baseStart_653054 := by decide
  rcases family_descends (prefixWord ++ tailWord_653054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653067 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 3, 3]
def baseStart_653067 : Nat := 118140960795 + 653067 * 2 ^ 59
def prefixEnd_653067 : Nat := 4983230072969 + 3 ^ 40 * 653067 * 2
def baseEnd_653067 : Nat := 223558180393267737372737

theorem tailTrace_653067 : CollatzResearch.WordTrace tailWord_653067 prefixEnd_653067 223558180393267737372737 := by
  unfold tailWord_653067
  simp only [CollatzResearch.WordTrace]
  refine ⟨23819310325057268808957455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15879540216704845872638303 23819310325057268808957455)
  ·
    refine ⟨35728965487585903213436183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23819310325057268808957455 35728965487585903213436183)
    ·
      refine ⟨53593448231378854820154275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35728965487585903213436183 53593448231378854820154275)
      ·
        refine ⟨80390172347068282230231413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53593448231378854820154275 80390172347068282230231413)
        ·
          refine ⟨7536578657537651459084195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80390172347068282230231413 7536578657537651459084195)
          ·
            refine ⟨11304867986306477188626293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536578657537651459084195 11304867986306477188626293)
            ·
              refine ⟨1059831373716232236433715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11304867986306477188626293 1059831373716232236433715)
              ·
                refine ⟨1589747060574348354650573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059831373716232236433715 1589747060574348354650573)
                ·
                  refine ⟨596155147715380632993965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1589747060574348354650573 596155147715380632993965)
                  ·
                    refine ⟨223558180393267737372737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596155147715380632993965 223558180393267737372737)
                    ·
                      rfl

theorem cell22_653067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].length) (baseStart_653067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653067 prefixEnd_653067 := by exact prefixLift 653067
  have htrace : WordTrace (prefixWord ++ tailWord_653067) baseStart_653067 baseEnd_653067 := by
    simpa [prefixWord, tailWord_653067, baseEnd_653067] using wordTrace_append hprefix tailTrace_653067
  have hstable : (prefixWord ++ tailWord_653067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653067).length < 2 ^ (prefixWord ++ tailWord_653067).sum := by decide
  have hdescent : baseEnd_653067 < baseStart_653067 := by decide
  rcases family_descends (prefixWord ++ tailWord_653067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653118 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_653118 : Nat := 118140960795 + 653118 * 2 ^ 59
def prefixEnd_653118 : Nat := 4983230072969 + 3 ^ 40 * 653118 * 2
def baseEnd_653118 : Nat := 223575638735520604347581

theorem tailTrace_653118 : CollatzResearch.WordTrace tailWord_653118 prefixEnd_653118 223575638735520604347581 := by
  unfold tailWord_653118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977646305984063064883001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15880780298581669679376005 2977646305984063064883001)
  ·
    refine ⟨2233234729488047298662251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2977646305984063064883001 2233234729488047298662251)
    ·
      refine ⟨3349852094232070947993377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233234729488047298662251 3349852094232070947993377)
      ·
        refine ⟨2512389070674053210995033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3349852094232070947993377 2512389070674053210995033)
        ·
          refine ⟨1884291803005539908246275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512389070674053210995033 1884291803005539908246275)
          ·
            refine ⟨2826437704508309862369413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884291803005539908246275 2826437704508309862369413)
            ·
              refine ⟨529957069595308099194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2826437704508309862369413 529957069595308099194265)
              ·
                refine ⟨397467802196481074395699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529957069595308099194265 397467802196481074395699)
                ·
                  refine ⟨596201703294721611593549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397467802196481074395699 596201703294721611593549)
                  ·
                    refine ⟨223575638735520604347581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596201703294721611593549 223575638735520604347581)
                    ·
                      rfl

theorem cell22_653118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_653118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653118 prefixEnd_653118 := by exact prefixLift 653118
  have htrace : WordTrace (prefixWord ++ tailWord_653118) baseStart_653118 baseEnd_653118 := by
    simpa [prefixWord, tailWord_653118, baseEnd_653118] using wordTrace_append hprefix tailTrace_653118
  have hstable : (prefixWord ++ tailWord_653118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653118).length < 2 ^ (prefixWord ++ tailWord_653118).sum := by decide
  have hdescent : baseEnd_653118 < baseStart_653118 := by decide
  rcases family_descends (prefixWord ++ tailWord_653118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653125 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 6]
def baseStart_653125 : Nat := 118140960795 + 653125 * 2 ^ 59
def prefixEnd_653125 : Nat := 4983230072969 + 3 ^ 40 * 653125 * 2
def baseEnd_653125 : Nat := 74526011659524973140853

theorem tailTrace_653125 : CollatzResearch.WordTrace tailWord_653125 prefixEnd_653125 74526011659524973140853 := by
  unfold tailWord_653125
  simp only [CollatzResearch.WordTrace]
  refine ⟨23821425758847144714568829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15880950505898096476379219 23821425758847144714568829)
  ·
    refine ⟨8933034659567679267963311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23821425758847144714568829 8933034659567679267963311)
    ·
      refine ⟨13399551989351518901944967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933034659567679267963311 13399551989351518901944967)
      ·
        refine ⟨20099327984027278352917451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13399551989351518901944967 20099327984027278352917451)
        ·
          refine ⟨30148991976040917529376177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099327984027278352917451 30148991976040917529376177)
          ·
            refine ⟨22611743982030688147032133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30148991976040917529376177 22611743982030688147032133)
            ·
              refine ⟨4239701996630754027568525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22611743982030688147032133 4239701996630754027568525)
              ·
                refine ⟨1589888248736532760338197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239701996630754027568525 1589888248736532760338197)
                ·
                  refine ⟨74526011659524973140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1589888248736532760338197 74526011659524973140853)
                  ·
                    rfl

theorem cell22_653125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_653125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653125 prefixEnd_653125 := by exact prefixLift 653125
  have htrace : WordTrace (prefixWord ++ tailWord_653125) baseStart_653125 baseEnd_653125 := by
    simpa [prefixWord, tailWord_653125, baseEnd_653125] using wordTrace_append hprefix tailTrace_653125
  have hstable : (prefixWord ++ tailWord_653125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653125).length < 2 ^ (prefixWord ++ tailWord_653125).sum := by decide
  have hdescent : baseEnd_653125 < baseStart_653125 := by decide
  rcases family_descends (prefixWord ++ tailWord_653125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653157 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_653157 : Nat := 118140960795 + 653157 * 2 ^ 59
def prefixEnd_653157 : Nat := 4983230072969 + 3 ^ 40 * 653157 * 2
def baseEnd_653157 : Nat := 223588989232537502622461

theorem tailTrace_653157 : CollatzResearch.WordTrace tailWord_653157 prefixEnd_653157 223588989232537502622461 := by
  unfold tailWord_653157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23822592894731214179733725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15881728596487476119822483 23822592894731214179733725)
  ·
    refine ⟨8933472335524205317400147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23822592894731214179733725 8933472335524205317400147)
    ·
      refine ⟨13400208503286307976100221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933472335524205317400147 13400208503286307976100221)
      ·
        refine ⟨5025078188732365491037583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13400208503286307976100221 5025078188732365491037583)
        ·
          refine ⟨7537617283098548236556375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025078188732365491037583 7537617283098548236556375)
          ·
            refine ⟨11306425924647822354834563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7537617283098548236556375 11306425924647822354834563)
            ·
              refine ⟨16959638886971733532251845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11306425924647822354834563 16959638886971733532251845)
              ·
                refine ⟨3179932291307200037297221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16959638886971733532251845 3179932291307200037297221)
                ·
                  refine ⟨596237304620100006993229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3179932291307200037297221 596237304620100006993229)
                  ·
                    refine ⟨223588989232537502622461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596237304620100006993229 223588989232537502622461)
                    ·
                      rfl

theorem cell22_653157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_653157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653157 prefixEnd_653157 := by exact prefixLift 653157
  have htrace : WordTrace (prefixWord ++ tailWord_653157) baseStart_653157 baseEnd_653157 := by
    simpa [prefixWord, tailWord_653157, baseEnd_653157] using wordTrace_append hprefix tailTrace_653157
  have hstable : (prefixWord ++ tailWord_653157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653157).length < 2 ^ (prefixWord ++ tailWord_653157).sum := by decide
  have hdescent : baseEnd_653157 < baseStart_653157 := by decide
  rcases family_descends (prefixWord ++ tailWord_653157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653159 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 4]
def baseStart_653159 : Nat := 118140960795 + 653159 * 2 ^ 59
def prefixEnd_653159 : Nat := 4983230072969 + 3 ^ 40 * 653159 * 2
def baseEnd_653159 : Nat := 74529891291136721357485

theorem tailTrace_653159 : CollatzResearch.WordTrace tailWord_653159 prefixEnd_653159 74529891291136721357485 := by
  unfold tailWord_653159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23822665840723968521306531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15881777227149312347537687 23822665840723968521306531)
  ·
    refine ⟨35733998761085952781959797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23822665840723968521306531 35733998761085952781959797)
    ·
      refine ⟨3350062383851808073308731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35733998761085952781959797 3350062383851808073308731)
      ·
        refine ⟨5025093575777712109963097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350062383851808073308731 5025093575777712109963097)
        ·
          refine ⟨3768820181833284082472323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5025093575777712109963097 3768820181833284082472323)
          ·
            refine ⟨5653230272749926123708485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768820181833284082472323 5653230272749926123708485)
            ·
              refine ⟨1059980676140611148195341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5653230272749926123708485 1059980676140611148195341)
              ·
                refine ⟨397492753552729180573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059980676140611148195341 397492753552729180573253)
                ·
                  refine ⟨74529891291136721357485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397492753552729180573253 74529891291136721357485)
                  ·
                    rfl

theorem cell22_653159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 4].length) (baseStart_653159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653159 prefixEnd_653159 := by exact prefixLift 653159
  have htrace : WordTrace (prefixWord ++ tailWord_653159) baseStart_653159 baseEnd_653159 := by
    simpa [prefixWord, tailWord_653159, baseEnd_653159] using wordTrace_append hprefix tailTrace_653159
  have hstable : (prefixWord ++ tailWord_653159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653159).length < 2 ^ (prefixWord ++ tailWord_653159).sum := by decide
  have hdescent : baseEnd_653159 < baseStart_653159 := by decide
  rcases family_descends (prefixWord ++ tailWord_653159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653191 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 5]
def baseStart_653191 : Nat := 118140960795 + 653191 * 2 ^ 59
def prefixEnd_653191 : Nat := 4983230072969 + 3 ^ 40 * 653191 * 2
def baseEnd_653191 : Nat := 223600628127372747272357

theorem tailTrace_653191 : CollatzResearch.WordTrace tailWord_653191 prefixEnd_653191 223600628127372747272357 := by
  unfold tailWord_653191
  simp only [CollatzResearch.WordTrace]
  refine ⟨23823832976608037986471427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15882555317738691990980951 23823832976608037986471427)
  ·
    refine ⟨35735749464912056979707141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23823832976608037986471427 35735749464912056979707141)
    ·
      refine ⟨6700453024671010683695089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35735749464912056979707141 6700453024671010683695089)
      ·
        refine ⟨5025339768503258012771317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6700453024671010683695089 5025339768503258012771317)
        ·
          refine ⟨471125603297180438697311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5025339768503258012771317 471125603297180438697311)
          ·
            refine ⟨706688404945770658045967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471125603297180438697311 706688404945770658045967)
            ·
              refine ⟨1060032607418655987068951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706688404945770658045967 1060032607418655987068951)
              ·
                refine ⟨1590048911127983980603427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060032607418655987068951 1590048911127983980603427)
                ·
                  refine ⟨2385073366691975970905141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590048911127983980603427 2385073366691975970905141)
                  ·
                    refine ⟨223600628127372747272357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2385073366691975970905141 223600628127372747272357)
                    ·
                      rfl

theorem cell22_653191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_653191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653191 prefixEnd_653191 := by exact prefixLift 653191
  have htrace : WordTrace (prefixWord ++ tailWord_653191) baseStart_653191 baseEnd_653191 := by
    simpa [prefixWord, tailWord_653191, baseEnd_653191] using wordTrace_append hprefix tailTrace_653191
  have hstable : (prefixWord ++ tailWord_653191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653191).length < 2 ^ (prefixWord ++ tailWord_653191).sum := by decide
  have hdescent : baseEnd_653191 < baseStart_653191 := by decide
  rcases family_descends (prefixWord ++ tailWord_653191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653200 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_653200 : Nat := 118140960795 + 653200 * 2 ^ 59
def prefixEnd_653200 : Nat := 4983230072969 + 3 ^ 40 * 653200 * 2
def baseEnd_653200 : Nat := 223603709011299723797329

theorem tailTrace_653200 : CollatzResearch.WordTrace tailWord_653200 prefixEnd_653200 223603709011299723797329 := by
  unfold tailWord_653200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912080616787716261774527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15882774155716955015699369 11912080616787716261774527)
  ·
    refine ⟨17868120925181574392661791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11912080616787716261774527 17868120925181574392661791)
    ·
      refine ⟨26802181387772361588992687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17868120925181574392661791 26802181387772361588992687)
      ·
        refine ⟨40203272081658542383489031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26802181387772361588992687 40203272081658542383489031)
        ·
          refine ⟨60304908122487813575233547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40203272081658542383489031 60304908122487813575233547)
          ·
            refine ⟨90457362183731720362850321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60304908122487813575233547 90457362183731720362850321)
            ·
              refine ⟨67843021637798790272137741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90457362183731720362850321 67843021637798790272137741)
              ·
                refine ⟨25441133114174546352051653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67843021637798790272137741 25441133114174546352051653)
                ·
                  refine ⟨4770212458907727441009685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25441133114174546352051653 4770212458907727441009685)
                  ·
                    refine ⟨223603709011299723797329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4770212458907727441009685 223603709011299723797329)
                    ·
                      rfl

theorem cell22_653200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_653200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653200 prefixEnd_653200 := by exact prefixLift 653200
  have htrace : WordTrace (prefixWord ++ tailWord_653200) baseStart_653200 baseEnd_653200 := by
    simpa [prefixWord, tailWord_653200, baseEnd_653200] using wordTrace_append hprefix tailTrace_653200
  have hstable : (prefixWord ++ tailWord_653200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653200).length < 2 ^ (prefixWord ++ tailWord_653200).sum := by decide
  have hdescent : baseEnd_653200 < baseStart_653200 := by decide
  rcases family_descends (prefixWord ++ tailWord_653200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653204 : List Nat := [2, 4, 2, 1, 1, 2, 4, 6]
def baseStart_653204 : Nat := 118140960795 + 653204 * 2 ^ 59
def prefixEnd_653204 : Nat := 4983230072969 + 3 ^ 40 * 653204 * 2
def baseEnd_653204 : Nat := 24845008699227227410813

theorem tailTrace_653204 : CollatzResearch.WordTrace tailWord_653204 prefixEnd_653204 24845008699227227410813 := by
  unfold tailWord_653204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912153562780470603347333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15882871417040627471129777 11912153562780470603347333)
  ·
    refine ⟨2233528793021338238127625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11912153562780470603347333 2233528793021338238127625)
    ·
      refine ⟨1675146594766003678595719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2233528793021338238127625 1675146594766003678595719)
      ·
        refine ⟨2512719892149005517893579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675146594766003678595719 2512719892149005517893579)
        ·
          refine ⟨3769079838223508276840369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512719892149005517893579 3769079838223508276840369)
          ·
            refine ⟨2826809878667631207630277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769079838223508276840369 2826809878667631207630277)
            ·
              refine ⟨530026852250180851430677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2826809878667631207630277 530026852250180851430677)
              ·
                refine ⟨24845008699227227410813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 530026852250180851430677 24845008699227227410813)
                ·
                  rfl

theorem cell22_653204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_653204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653204 prefixEnd_653204 := by exact prefixLift 653204
  have htrace : WordTrace (prefixWord ++ tailWord_653204) baseStart_653204 baseEnd_653204 := by
    simpa [prefixWord, tailWord_653204, baseEnd_653204] using wordTrace_append hprefix tailTrace_653204
  have hstable : (prefixWord ++ tailWord_653204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653204).length < 2 ^ (prefixWord ++ tailWord_653204).sum := by decide
  have hdescent : baseEnd_653204 < baseStart_653204 := by decide
  rcases family_descends (prefixWord ++ tailWord_653204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653287 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 1, 3]
def baseStart_653287 : Nat := 118140960795 + 653287 * 2 ^ 59
def prefixEnd_653287 : Nat := 4983230072969 + 3 ^ 40 * 653287 * 2
def baseEnd_653287 : Nat := 223633490889260496872063

theorem tailTrace_653287 : CollatzResearch.WordTrace tailWord_653287 prefixEnd_653287 223633490889260496872063 := by
  unfold tailWord_653287
  simp only [CollatzResearch.WordTrace]
  refine ⟨23827334384260246381966115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15884889589506830921310743 23827334384260246381966115)
  ·
    refine ⟨35741001576390369572949173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23827334384260246381966115 35741001576390369572949173)
    ·
      refine ⟨3350718897786597147463985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35741001576390369572949173 3350718897786597147463985)
      ·
        refine ⟨2513039173339947860597989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350718897786597147463985 2513039173339947860597989)
        ·
          refine ⟨471194845001240223862123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2513039173339947860597989 471194845001240223862123)
          ·
            refine ⟨706792267501860335793185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471194845001240223862123 706792267501860335793185)
            ·
              refine ⟨530094200626395251844889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706792267501860335793185 530094200626395251844889)
              ·
                refine ⟨397570650469796438883667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530094200626395251844889 397570650469796438883667)
                ·
                  refine ⟨596355975704694658325501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397570650469796438883667 596355975704694658325501)
                  ·
                    refine ⟨223633490889260496872063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596355975704694658325501 223633490889260496872063)
                    ·
                      rfl

theorem cell22_653287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_653287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653287 prefixEnd_653287 := by exact prefixLift 653287
  have htrace : WordTrace (prefixWord ++ tailWord_653287) baseStart_653287 baseEnd_653287 := by
    simpa [prefixWord, tailWord_653287, baseEnd_653287] using wordTrace_append hprefix tailTrace_653287
  have hstable : (prefixWord ++ tailWord_653287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653287).length < 2 ^ (prefixWord ++ tailWord_653287).sum := by decide
  have hdescent : baseEnd_653287 < baseStart_653287 := by decide
  rcases family_descends (prefixWord ++ tailWord_653287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653307 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_653307 : Nat := 118140960795 + 653307 * 2 ^ 59
def prefixEnd_653307 : Nat := 4983230072969 + 3 ^ 40 * 653307 * 2
def baseEnd_653307 : Nat := 223640337297987111372001

theorem tailTrace_653307 : CollatzResearch.WordTrace tailWord_653307 prefixEnd_653307 223640337297987111372001 := by
  unfold tailWord_653307
  simp only [CollatzResearch.WordTrace]
  refine ⟨23828063844187789797694175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15885375896125193198462783 23828063844187789797694175)
  ·
    refine ⟨35742095766281684696541263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23828063844187789797694175 35742095766281684696541263)
    ·
      refine ⟨53613143649422527044811895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35742095766281684696541263 53613143649422527044811895)
      ·
        refine ⟨80419715474133790567217843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53613143649422527044811895 80419715474133790567217843)
        ·
          refine ⟨120629573211200685850826765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80419715474133790567217843 120629573211200685850826765)
          ·
            refine ⟨45236089954200257194060037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120629573211200685850826765 45236089954200257194060037)
            ·
              refine ⟨8481766866412548223886257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45236089954200257194060037 8481766866412548223886257)
              ·
                refine ⟨6361325149809411167914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481766866412548223886257 6361325149809411167914693)
                ·
                  refine ⟨1192748465589264593984005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6361325149809411167914693 1192748465589264593984005)
                  ·
                    refine ⟨223640337297987111372001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192748465589264593984005 223640337297987111372001)
                    ·
                      rfl

theorem cell22_653307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_653307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653307 prefixEnd_653307 := by exact prefixLift 653307
  have htrace : WordTrace (prefixWord ++ tailWord_653307) baseStart_653307 baseEnd_653307 := by
    simpa [prefixWord, tailWord_653307, baseEnd_653307] using wordTrace_append hprefix tailTrace_653307
  have hstable : (prefixWord ++ tailWord_653307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653307).length < 2 ^ (prefixWord ++ tailWord_653307).sum := by decide
  have hdescent : baseEnd_653307 < baseStart_653307 := by decide
  rcases family_descends (prefixWord ++ tailWord_653307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653388 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_653388 : Nat := 118140960795 + 653388 * 2 ^ 59
def prefixEnd_653388 : Nat := 4983230072969 + 3 ^ 40 * 653388 * 2
def baseEnd_653388 : Nat := 223668065253329900096753

theorem tailTrace_653388 : CollatzResearch.WordTrace tailWord_653388 prefixEnd_653388 223668065253329900096753 := by
  unfold tailWord_653388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915509078447170315696409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15887345437929560420928545 11915509078447170315696409)
  ·
    refine ⟨8936631808835377736772307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11915509078447170315696409 8936631808835377736772307)
    ·
      refine ⟨13404947713253066605158461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936631808835377736772307 13404947713253066605158461)
      ·
        refine ⟨5026855392469899976934423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13404947713253066605158461 5026855392469899976934423)
        ·
          refine ⟨7540283088704849965401635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026855392469899976934423 7540283088704849965401635)
          ·
            refine ⟨11310424633057274948102453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540283088704849965401635 11310424633057274948102453)
            ·
              refine ⟨1060352309349119526384605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11310424633057274948102453 1060352309349119526384605)
              ·
                refine ⟨397632116005919822394227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060352309349119526384605 397632116005919822394227)
                ·
                  refine ⟨596448174008879733591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397632116005919822394227 596448174008879733591341)
                  ·
                    refine ⟨223668065253329900096753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596448174008879733591341 223668065253329900096753)
                    ·
                      rfl

theorem cell22_653388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_653388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653388 prefixEnd_653388 := by exact prefixLift 653388
  have htrace : WordTrace (prefixWord ++ tailWord_653388) baseStart_653388 baseEnd_653388 := by
    simpa [prefixWord, tailWord_653388, baseEnd_653388] using wordTrace_append hprefix tailTrace_653388
  have hstable : (prefixWord ++ tailWord_653388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653388).length < 2 ^ (prefixWord ++ tailWord_653388).sum := by decide
  have hdescent : baseEnd_653388 < baseStart_653388 := by decide
  rcases family_descends (prefixWord ++ tailWord_653388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653405 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_653405 : Nat := 118140960795 + 653405 * 2 ^ 59
def prefixEnd_653405 : Nat := 4983230072969 + 3 ^ 40 * 653405 * 2
def baseEnd_653405 : Nat := 223673884700747522421701

theorem tailTrace_653405 : CollatzResearch.WordTrace tailWord_653405 prefixEnd_653405 223673884700747522421701 := by
  unfold tailWord_653405
  simp only [CollatzResearch.WordTrace]
  refine ⟨23831638197832752534761669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15887758798555168356507779 23831638197832752534761669)
  ·
    refine ⟨4468432162093641100267813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23831638197832752534761669 4468432162093641100267813)
    ·
      refine ⟨837831030392557706300215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4468432162093641100267813 837831030392557706300215)
      ·
        refine ⟨1256746545588836559450323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837831030392557706300215 1256746545588836559450323)
        ·
          refine ⟨1885119818383254839175485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256746545588836559450323 1885119818383254839175485)
          ·
            refine ⟨706919931893720564690807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1885119818383254839175485 706919931893720564690807)
            ·
              refine ⟨1060379897840580847036211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706919931893720564690807 1060379897840580847036211)
              ·
                refine ⟨1590569846760871270554317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060379897840580847036211 1590569846760871270554317)
                ·
                  refine ⟨596463692535326726457869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1590569846760871270554317 596463692535326726457869)
                  ·
                    refine ⟨223673884700747522421701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596463692535326726457869 223673884700747522421701)
                    ·
                      rfl

theorem cell22_653405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_653405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653405 prefixEnd_653405 := by exact prefixLift 653405
  have htrace : WordTrace (prefixWord ++ tailWord_653405) baseStart_653405 baseEnd_653405 := by
    simpa [prefixWord, tailWord_653405, baseEnd_653405] using wordTrace_append hprefix tailTrace_653405
  have hstable : (prefixWord ++ tailWord_653405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653405).length < 2 ^ (prefixWord ++ tailWord_653405).sum := by decide
  have hdescent : baseEnd_653405 < baseStart_653405 := by decide
  rcases family_descends (prefixWord ++ tailWord_653405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653431 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 1, 4]
def baseStart_653431 : Nat := 118140960795 + 653431 * 2 ^ 59
def prefixEnd_653431 : Nat := 4983230072969 + 3 ^ 40 * 653431 * 2
def baseEnd_653431 : Nat := 223682785032092121271621

theorem tailTrace_653431 : CollatzResearch.WordTrace tailWord_653431 prefixEnd_653431 223682785032092121271621 := by
  unfold tailWord_653431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832586495738558975208147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15888390997159039316805431 23832586495738558975208147)
  ·
    refine ⟨35748879743607838462812221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23832586495738558975208147 35748879743607838462812221)
    ·
      refine ⟨13405829903852939423554583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35748879743607838462812221 13405829903852939423554583)
      ·
        refine ⟨20108744855779409135331875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405829903852939423554583 20108744855779409135331875)
        ·
          refine ⟨30163117283669113702997813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20108744855779409135331875 30163117283669113702997813)
          ·
            refine ⟨2827792245343979409656045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30163117283669113702997813 2827792245343979409656045)
            ·
              refine ⟨1060422092003992278621017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2827792245343979409656045 1060422092003992278621017)
              ·
                refine ⟨795316569002994208965763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060422092003992278621017 795316569002994208965763)
                ·
                  refine ⟨1192974853504491313448645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795316569002994208965763 1192974853504491313448645)
                  ·
                    refine ⟨223682785032092121271621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192974853504491313448645 223682785032092121271621)
                    ·
                      rfl

theorem cell22_653431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_653431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653431 prefixEnd_653431 := by exact prefixLift 653431
  have htrace : WordTrace (prefixWord ++ tailWord_653431) baseStart_653431 baseEnd_653431 := by
    simpa [prefixWord, tailWord_653431, baseEnd_653431] using wordTrace_append hprefix tailTrace_653431
  have hstable : (prefixWord ++ tailWord_653431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653431).length < 2 ^ (prefixWord ++ tailWord_653431).sum := by decide
  have hdescent : baseEnd_653431 < baseStart_653431 := by decide
  rcases family_descends (prefixWord ++ tailWord_653431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653463 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 4]
def baseStart_653463 : Nat := 118140960795 + 653463 * 2 ^ 59
def prefixEnd_653463 : Nat := 4983230072969 + 3 ^ 40 * 653463 * 2
def baseEnd_653463 : Nat := 74564579762018234823841

theorem tailTrace_653463 : CollatzResearch.WordTrace tailWord_653463 prefixEnd_653463 74564579762018234823841 := by
  unfold tailWord_653463
  simp only [CollatzResearch.WordTrace]
  refine ⟨23833753631622628440373043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15889169087748418960248695 23833753631622628440373043)
  ·
    refine ⟨35750630447433942660559565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23833753631622628440373043 35750630447433942660559565)
    ·
      refine ⟨13406486417787728497709837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35750630447433942660559565 13406486417787728497709837)
      ·
        refine ⟨5027432406670398186641189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13406486417787728497709837 5027432406670398186641189)
        ·
          refine ⟨942643576250699659995223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5027432406670398186641189 942643576250699659995223)
          ·
            refine ⟨1413965364376049489992835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942643576250699659995223 1413965364376049489992835)
            ·
              refine ⟨2120948046564074234989253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413965364376049489992835 2120948046564074234989253)
              ·
                refine ⟨397677758730763919060485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2120948046564074234989253 397677758730763919060485)
                ·
                  refine ⟨74564579762018234823841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397677758730763919060485 74564579762018234823841)
                  ·
                    rfl

theorem cell22_653463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 4].length) (baseStart_653463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653463 prefixEnd_653463 := by exact prefixLift 653463
  have htrace : WordTrace (prefixWord ++ tailWord_653463) baseStart_653463 baseEnd_653463 := by
    simpa [prefixWord, tailWord_653463, baseEnd_653463] using wordTrace_append hprefix tailTrace_653463
  have hstable : (prefixWord ++ tailWord_653463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653463).length < 2 ^ (prefixWord ++ tailWord_653463).sum := by decide
  have hdescent : baseEnd_653463 < baseStart_653463 := by decide
  rcases family_descends (prefixWord ++ tailWord_653463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653493 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_653493 : Nat := 118140960795 + 653493 * 2 ^ 59
def prefixEnd_653493 : Nat := 4983230072969 + 3 ^ 40 * 653493 * 2
def baseEnd_653493 : Nat := 223704008899144626221431

theorem tailTrace_653493 : CollatzResearch.WordTrace tailWord_653493 prefixEnd_653493 223704008899144626221431 := by
  unfold tailWord_653493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23834847821513943563965133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15889898547675962375976755 23834847821513943563965133)
  ·
    refine ⟨8938067933067728836486925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23834847821513943563965133 8938067933067728836486925)
    ·
      refine ⟨3351775474900398313682597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8938067933067728836486925 3351775474900398313682597)
      ·
        refine ⟨628457901543824683815487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3351775474900398313682597 628457901543824683815487)
        ·
          refine ⟨942686852315737025723231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628457901543824683815487 942686852315737025723231)
          ·
            refine ⟨1414030278473605538584847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942686852315737025723231 1414030278473605538584847)
            ·
              refine ⟨2121045417710408307877271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414030278473605538584847 2121045417710408307877271)
              ·
                refine ⟨3181568126565612461815907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121045417710408307877271 3181568126565612461815907)
                ·
                  refine ⟨4772352189848418692723861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181568126565612461815907 4772352189848418692723861)
                  ·
                    refine ⟨223704008899144626221431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4772352189848418692723861 223704008899144626221431)
                    ·
                      rfl

theorem cell22_653493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_653493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653493 prefixEnd_653493 := by exact prefixLift 653493
  have htrace : WordTrace (prefixWord ++ tailWord_653493) baseStart_653493 baseEnd_653493 := by
    simpa [prefixWord, tailWord_653493, baseEnd_653493] using wordTrace_append hprefix tailTrace_653493
  have hstable : (prefixWord ++ tailWord_653493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653493).length < 2 ^ (prefixWord ++ tailWord_653493).sum := by decide
  have hdescent : baseEnd_653493 < baseStart_653493 := by decide
  rcases family_descends (prefixWord ++ tailWord_653493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653519 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 7]
def baseStart_653519 : Nat := 118140960795 + 653519 * 2 ^ 59
def prefixEnd_653519 : Nat := 4983230072969 + 3 ^ 40 * 653519 * 2
def baseEnd_653519 : Nat := 74570969743496408357117

theorem tailTrace_653519 : CollatzResearch.WordTrace tailWord_653519 prefixEnd_653519 74570969743496408357117 := by
  unfold tailWord_653519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23835796119419750004411611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15890530746279833336274407 23835796119419750004411611)
  ·
    refine ⟨35753694179129625006617417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23835796119419750004411611 35753694179129625006617417)
    ·
      refine ⟨26815270634347218754963063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35753694179129625006617417 26815270634347218754963063)
      ·
        refine ⟨40222905951520828132444595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26815270634347218754963063 40222905951520828132444595)
        ·
          refine ⟨60334358927281242198666893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40222905951520828132444595 60334358927281242198666893)
          ·
            refine ⟨22625384597730465824500085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60334358927281242198666893 22625384597730465824500085)
            ·
              refine ⟨2121129806037231171046883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22625384597730465824500085 2121129806037231171046883)
              ·
                refine ⟨3181694709055846756570325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121129806037231171046883 3181694709055846756570325)
                ·
                  refine ⟨74570969743496408357117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3181694709055846756570325 74570969743496408357117)
                  ·
                    rfl

theorem cell22_653519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_653519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653519 prefixEnd_653519 := by exact prefixLift 653519
  have htrace : WordTrace (prefixWord ++ tailWord_653519) baseStart_653519 baseEnd_653519 := by
    simpa [prefixWord, tailWord_653519, baseEnd_653519] using wordTrace_append hprefix tailTrace_653519
  have hstable : (prefixWord ++ tailWord_653519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653519).length < 2 ^ (prefixWord ++ tailWord_653519).sum := by decide
  have hdescent : baseEnd_653519 < baseStart_653519 := by decide
  rcases family_descends (prefixWord ++ tailWord_653519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653596 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_653596 : Nat := 118140960795 + 653596 * 2 ^ 59
def prefixEnd_653596 : Nat := 4983230072969 + 3 ^ 40 * 653596 * 2
def baseEnd_653596 : Nat := 223739267904086690896115

theorem tailTrace_653596 : CollatzResearch.WordTrace tailWord_653596 prefixEnd_653596 223739267904086690896115 := by
  unfold tailWord_653596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919302270070396077482321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15892403026760528103309761 11919302270070396077482321)
  ·
    refine ⟨8939476702552797058111741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11919302270070396077482321 8939476702552797058111741)
    ·
      refine ⟨3352303763457298896791903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8939476702552797058111741 3352303763457298896791903)
      ·
        refine ⟨5028455645185948345187855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352303763457298896791903 5028455645185948345187855)
        ·
          refine ⟨7542683467778922517781783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028455645185948345187855 7542683467778922517781783)
          ·
            refine ⟨11314025201668383776672675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542683467778922517781783 11314025201668383776672675)
            ·
              refine ⟨16971037802502575665009013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11314025201668383776672675 16971037802502575665009013)
              ·
                refine ⟨1591034793984616468594595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16971037802502575665009013 1591034793984616468594595)
                ·
                  refine ⟨2386552190976924702891893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591034793984616468594595 2386552190976924702891893)
                  ·
                    refine ⟨223739267904086690896115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2386552190976924702891893 223739267904086690896115)
                    ·
                      rfl

theorem cell22_653596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_653596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653596 prefixEnd_653596 := by exact prefixLift 653596
  have htrace : WordTrace (prefixWord ++ tailWord_653596) baseStart_653596 baseEnd_653596 := by
    simpa [prefixWord, tailWord_653596, baseEnd_653596] using wordTrace_append hprefix tailTrace_653596
  have hstable : (prefixWord ++ tailWord_653596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653596).length < 2 ^ (prefixWord ++ tailWord_653596).sum := by decide
  have hdescent : baseEnd_653596 < baseStart_653596 := by decide
  rcases family_descends (prefixWord ++ tailWord_653596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653600 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_653600 : Nat := 118140960795 + 653600 * 2 ^ 59
def prefixEnd_653600 : Nat := 4983230072969 + 3 ^ 40 * 653600 * 2
def baseEnd_653600 : Nat := 223740637185832013796103

theorem tailTrace_653600 : CollatzResearch.WordTrace tailWord_653600 prefixEnd_653600 223740637185832013796103 := by
  unfold tailWord_653600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919375216063150419055127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15892500288084200558740169 11919375216063150419055127)
  ·
    refine ⟨17879062824094725628582691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11919375216063150419055127 17879062824094725628582691)
    ·
      refine ⟨26818594236142088442874037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17879062824094725628582691 26818594236142088442874037)
      ·
        refine ⟨2514243209638320791519441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26818594236142088442874037 2514243209638320791519441)
        ·
          refine ⟨1885682407228740593639581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514243209638320791519441 1885682407228740593639581)
          ·
            refine ⟨707130902710777722614843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1885682407228740593639581 707130902710777722614843)
            ·
              refine ⟨1060696354066166583922265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707130902710777722614843 1060696354066166583922265)
              ·
                refine ⟨795522265549624937941699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060696354066166583922265 795522265549624937941699)
                ·
                  refine ⟨1193283398324437406912549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795522265549624937941699 1193283398324437406912549)
                  ·
                    refine ⟨223740637185832013796103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193283398324437406912549 223740637185832013796103)
                    ·
                      rfl

theorem cell22_653600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_653600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653600 prefixEnd_653600 := by exact prefixLift 653600
  have htrace : WordTrace (prefixWord ++ tailWord_653600) baseStart_653600 baseEnd_653600 := by
    simpa [prefixWord, tailWord_653600, baseEnd_653600] using wordTrace_append hprefix tailTrace_653600
  have hstable : (prefixWord ++ tailWord_653600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653600).length < 2 ^ (prefixWord ++ tailWord_653600).sum := by decide
  have hdescent : baseEnd_653600 < baseStart_653600 := by decide
  rcases family_descends (prefixWord ++ tailWord_653600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653630 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_653630 : Nat := 118140960795 + 653630 * 2 ^ 59
def prefixEnd_653630 : Nat := 4983230072969 + 3 ^ 40 * 653630 * 2
def baseEnd_653630 : Nat := 223750906798921935546011

theorem tailTrace_653630 : CollatzResearch.WordTrace tailWord_653630 prefixEnd_653630 223750906798921935546011 := by
  unfold tailWord_653630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979980577752201995212793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15893229748011743974468229 2979980577752201995212793)
  ·
    refine ⟨2234985433314151496409595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2979980577752201995212793 2234985433314151496409595)
    ·
      refine ⟨3352478149971227244614393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234985433314151496409595 3352478149971227244614393)
      ·
        refine ⟨2514358612478420433460795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3352478149971227244614393 2514358612478420433460795)
        ·
          refine ⟨3771537918717630650191193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514358612478420433460795 3771537918717630650191193)
          ·
            refine ⟨2828653439038222987643395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771537918717630650191193 2828653439038222987643395)
            ·
              refine ⟨4242980158557334481465093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828653439038222987643395 4242980158557334481465093)
              ·
                refine ⟨795558779729500215274705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4242980158557334481465093 795558779729500215274705)
                ·
                  refine ⟨596669084797125161456029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795558779729500215274705 596669084797125161456029)
                  ·
                    refine ⟨223750906798921935546011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596669084797125161456029 223750906798921935546011)
                    ·
                      rfl

theorem cell22_653630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_653630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653630 prefixEnd_653630 := by exact prefixLift 653630
  have htrace : WordTrace (prefixWord ++ tailWord_653630) baseStart_653630 baseEnd_653630 := by
    simpa [prefixWord, tailWord_653630, baseEnd_653630] using wordTrace_append hprefix tailTrace_653630
  have hstable : (prefixWord ++ tailWord_653630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653630).length < 2 ^ (prefixWord ++ tailWord_653630).sum := by decide
  have hdescent : baseEnd_653630 < baseStart_653630 := by decide
  rcases family_descends (prefixWord ++ tailWord_653630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653705 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 5]
def baseStart_653705 : Nat := 118140960795 + 653705 * 2 ^ 59
def prefixEnd_653705 : Nat := 4983230072969 + 3 ^ 40 * 653705 * 2
def baseEnd_653705 : Nat := 74592193610548913306927

theorem tailTrace_653705 : CollatzResearch.WordTrace tailWord_653705 prefixEnd_653705 74592193610548913306927 := by
  unfold tailWord_653705
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842580096745903770682569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15895053397830602513788379 23842580096745903770682569)
  ·
    refine ⟨17881935072559427828011927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23842580096745903770682569 17881935072559427828011927)
    ·
      refine ⟨26822902608839141742017891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17881935072559427828011927 26822902608839141742017891)
      ·
        refine ⟨40234353913258712613026837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26822902608839141742017891 40234353913258712613026837)
        ·
          refine ⟨1885985339684002153735633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40234353913258712613026837 1885985339684002153735633)
          ·
            refine ⟨1414489004763001615301725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885985339684002153735633 1414489004763001615301725)
            ·
              refine ⟨530433376786125605738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1414489004763001615301725 530433376786125605738147)
              ·
                refine ⟨795650065179188408607221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530433376786125605738147 795650065179188408607221)
                ·
                  refine ⟨74592193610548913306927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 795650065179188408607221 74592193610548913306927)
                  ·
                    rfl

theorem cell22_653705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_653705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653705 prefixEnd_653705 := by exact prefixLift 653705
  have htrace : WordTrace (prefixWord ++ tailWord_653705) baseStart_653705 baseEnd_653705 := by
    simpa [prefixWord, tailWord_653705, baseEnd_653705] using wordTrace_append hprefix tailTrace_653705
  have hstable : (prefixWord ++ tailWord_653705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653705).length < 2 ^ (prefixWord ++ tailWord_653705).sum := by decide
  have hdescent : baseEnd_653705 < baseStart_653705 := by decide
  rcases family_descends (prefixWord ++ tailWord_653705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653726 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_653726 : Nat := 118140960795 + 653726 * 2 ^ 59
def prefixEnd_653726 : Nat := 4983230072969 + 3 ^ 40 * 653726 * 2
def baseEnd_653726 : Nat := 223783769560809685145717

theorem tailTrace_653726 : CollatzResearch.WordTrace tailWord_653726 prefixEnd_653726 223783769560809685145717 := by
  unfold tailWord_653726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980418253708728044649629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15895564019779882904798021 2980418253708728044649629)
  ·
    refine ⟨1117656845140773016743611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2980418253708728044649629 1117656845140773016743611)
    ·
      refine ⟨1676485267711159525115417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117656845140773016743611 1676485267711159525115417)
      ·
        refine ⟨1257363950783369643836563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676485267711159525115417 1257363950783369643836563)
        ·
          refine ⟨1886045926175054465754845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257363950783369643836563 1886045926175054465754845)
          ·
            refine ⟨707267222315645424658067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1886045926175054465754845 707267222315645424658067)
            ·
              refine ⟨1060900833473468136987101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707267222315645424658067 1060900833473468136987101)
              ·
                refine ⟨397837812552550551370163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060900833473468136987101 397837812552550551370163)
                ·
                  refine ⟨596756718828825827055245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397837812552550551370163 596756718828825827055245)
                  ·
                    refine ⟨223783769560809685145717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596756718828825827055245 223783769560809685145717)
                    ·
                      rfl

theorem cell22_653726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_653726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653726 prefixEnd_653726 := by exact prefixLift 653726
  have htrace : WordTrace (prefixWord ++ tailWord_653726) baseStart_653726 baseEnd_653726 := by
    simpa [prefixWord, tailWord_653726, baseEnd_653726] using wordTrace_append hprefix tailTrace_653726
  have hstable : (prefixWord ++ tailWord_653726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653726).length < 2 ^ (prefixWord ++ tailWord_653726).sum := by decide
  have hdescent : baseEnd_653726 < baseStart_653726 := by decide
  rcases family_descends (prefixWord ++ tailWord_653726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653735 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 1, 4]
def baseStart_653735 : Nat := 118140960795 + 653735 * 2 ^ 59
def prefixEnd_653735 : Nat := 4983230072969 + 3 ^ 40 * 653735 * 2
def baseEnd_653735 : Nat := 223786850444736661670689

theorem tailTrace_653735 : CollatzResearch.WordTrace tailWord_653735 prefixEnd_653735 223786850444736661670689 := by
  unfold tailWord_653735
  simp only [CollatzResearch.WordTrace]
  refine ⟨23843674286637218894274659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15895782857758145929516439 23843674286637218894274659)
  ·
    refine ⟨35765511429955828341411989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23843674286637218894274659 35765511429955828341411989)
    ·
      refine ⟨1676508348279179453503687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35765511429955828341411989 1676508348279179453503687)
      ·
        refine ⟨2514762522418769180255531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676508348279179453503687 2514762522418769180255531)
        ·
          refine ⟨3772143783628153770383297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514762522418769180255531 3772143783628153770383297)
          ·
            refine ⟨2829107837721115327787473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772143783628153770383297 2829107837721115327787473)
            ·
              refine ⟨2121830878290836495840605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829107837721115327787473 2121830878290836495840605)
              ·
                refine ⟨795686579359063685940227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2121830878290836495840605 795686579359063685940227)
                ·
                  refine ⟨1193529869038595528910341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795686579359063685940227 1193529869038595528910341)
                  ·
                    refine ⟨223786850444736661670689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193529869038595528910341 223786850444736661670689)
                    ·
                      rfl

theorem cell22_653735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_653735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653735 prefixEnd_653735 := by exact prefixLift 653735
  have htrace : WordTrace (prefixWord ++ tailWord_653735) baseStart_653735 baseEnd_653735 := by
    simpa [prefixWord, tailWord_653735, baseEnd_653735] using wordTrace_append hprefix tailTrace_653735
  have hstable : (prefixWord ++ tailWord_653735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653735).length < 2 ^ (prefixWord ++ tailWord_653735).sum := by decide
  have hdescent : baseEnd_653735 < baseStart_653735 := by decide
  rcases family_descends (prefixWord ++ tailWord_653735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653780 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_653780 : Nat := 118140960795 + 653780 * 2 ^ 59
def prefixEnd_653780 : Nat := 4983230072969 + 3 ^ 40 * 653780 * 2
def baseEnd_653780 : Nat := 223802254864371544295551

theorem tailTrace_653780 : CollatzResearch.WordTrace tailWord_653780 prefixEnd_653780 223802254864371544295551 := by
  unfold tailWord_653780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922657785737095789831397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15896877047649461053108529 11922657785737095789831397)
  ·
    refine ⟨2235498334825705460593387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11922657785737095789831397 2235498334825705460593387)
    ·
      refine ⟨3353247502238558190890081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235498334825705460593387 3353247502238558190890081)
      ·
        refine ⟨2514935626678918643167561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3353247502238558190890081 2514935626678918643167561)
        ·
          refine ⟨1886201720009188982375671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514935626678918643167561 1886201720009188982375671)
          ·
            refine ⟨2829302580013783473563507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886201720009188982375671 2829302580013783473563507)
            ·
              refine ⟨4243953870020675210345261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829302580013783473563507 4243953870020675210345261)
              ·
                refine ⟨1591482701257753203879473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243953870020675210345261 1591482701257753203879473)
                ·
                  refine ⟨1193612025943314902909605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591482701257753203879473 1193612025943314902909605)
                  ·
                    refine ⟨223802254864371544295551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193612025943314902909605 223802254864371544295551)
                    ·
                      rfl

theorem cell22_653780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_653780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653780 prefixEnd_653780 := by exact prefixLift 653780
  have htrace : WordTrace (prefixWord ++ tailWord_653780) baseStart_653780 baseEnd_653780 := by
    simpa [prefixWord, tailWord_653780, baseEnd_653780] using wordTrace_append hprefix tailTrace_653780
  have hstable : (prefixWord ++ tailWord_653780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653780).length < 2 ^ (prefixWord ++ tailWord_653780).sum := by decide
  have hdescent : baseEnd_653780 < baseStart_653780 := by decide
  rcases family_descends (prefixWord ++ tailWord_653780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653823 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 5]
def baseStart_653823 : Nat := 118140960795 + 653823 * 2 ^ 59
def prefixEnd_653823 : Nat := 4983230072969 + 3 ^ 40 * 653823 * 2
def baseEnd_653823 : Nat := 74605658214377921823473

theorem tailTrace_653823 : CollatzResearch.WordTrace tailWord_653823 prefixEnd_653823 74605658214377921823473 := by
  unfold tailWord_653823
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846883910318409923478123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897922606878939948985415 23846883910318409923478123)
  ·
    refine ⟨35770325865477614885217185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846883910318409923478123 35770325865477614885217185)
    ·
      refine ⟨26827744399108211163912889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35770325865477614885217185 26827744399108211163912889)
      ·
        refine ⟨20120808299331158372934667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26827744399108211163912889 20120808299331158372934667)
        ·
          refine ⟨30181212448996737559402001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20120808299331158372934667 30181212448996737559402001)
          ·
            refine ⟨22635909336747553169551501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30181212448996737559402001 22635909336747553169551501)
            ·
              refine ⟨8488466001280332438581813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22635909336747553169551501 8488466001280332438581813)
              ·
                refine ⟨795793687620031166117045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8488466001280332438581813 795793687620031166117045)
                ·
                  refine ⟨74605658214377921823473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 795793687620031166117045 74605658214377921823473)
                  ·
                    rfl

theorem cell22_653823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].length) (baseStart_653823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653823 prefixEnd_653823 := by exact prefixLift 653823
  have htrace : WordTrace (prefixWord ++ tailWord_653823) baseStart_653823 baseEnd_653823 := by
    simpa [prefixWord, tailWord_653823, baseEnd_653823] using wordTrace_append hprefix tailTrace_653823
  have hstable : (prefixWord ++ tailWord_653823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653823).length < 2 ^ (prefixWord ++ tailWord_653823).sum := by decide
  have hdescent : baseEnd_653823 < baseStart_653823 := by decide
  rcases family_descends (prefixWord ++ tailWord_653823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653885 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 6]
def baseStart_653885 : Nat := 118140960795 + 653885 * 2 ^ 59
def prefixEnd_653885 : Nat := 4983230072969 + 3 ^ 40 * 653885 * 2
def baseEnd_653885 : Nat := 74612732836728756806743

theorem tailTrace_653885 : CollatzResearch.WordTrace tailWord_653885 prefixEnd_653885 74612732836728756806743 := by
  unfold tailWord_653885
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849145236093794512235109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15899430157395863008156739 23849145236093794512235109)
  ·
    refine ⟨4471714731767586471044083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23849145236093794512235109 4471714731767586471044083)
    ·
      refine ⟨6707572097651379706566125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471714731767586471044083 6707572097651379706566125)
      ·
        refine ⟨2515339536619267389962297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6707572097651379706566125 2515339536619267389962297)
        ·
          refine ⟨1886504652464450542471723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2515339536619267389962297 1886504652464450542471723)
          ·
            refine ⟨2829756978696675813707585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886504652464450542471723 2829756978696675813707585)
            ·
              refine ⟨2122317734022506860280689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829756978696675813707585 2122317734022506860280689)
              ·
                refine ⟨1591738300516880145210517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122317734022506860280689 1591738300516880145210517)
                ·
                  refine ⟨74612732836728756806743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1591738300516880145210517 74612732836728756806743)
                  ·
                    rfl

theorem cell22_653885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_653885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653885 prefixEnd_653885 := by exact prefixLift 653885
  have htrace : WordTrace (prefixWord ++ tailWord_653885) baseStart_653885 baseEnd_653885 := by
    simpa [prefixWord, tailWord_653885, baseEnd_653885] using wordTrace_append hprefix tailTrace_653885
  have hstable : (prefixWord ++ tailWord_653885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653885).length < 2 ^ (prefixWord ++ tailWord_653885).sum := by decide
  have hdescent : baseEnd_653885 < baseStart_653885 := by decide
  rcases family_descends (prefixWord ++ tailWord_653885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653900 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_653900 : Nat := 118140960795 + 653900 * 2 ^ 59
def prefixEnd_653900 : Nat := 4983230072969 + 3 ^ 40 * 653900 * 2
def baseEnd_653900 : Nat := 223843333316731231295183

theorem tailTrace_653900 : CollatzResearch.WordTrace tailWord_653900 prefixEnd_653900 223843333316731231295183 := by
  unfold tailWord_653900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924846165519726037015577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15899794887359634716020769 11924846165519726037015577)
  ·
    refine ⟨8943634624139794527761683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11924846165519726037015577 8943634624139794527761683)
    ·
      refine ⟨13415451936209691791642525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943634624139794527761683 13415451936209691791642525)
      ·
        refine ⟨5030794476078634421865947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13415451936209691791642525 5030794476078634421865947)
        ·
          refine ⟨7546191714117951632798921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030794476078634421865947 7546191714117951632798921)
          ·
            refine ⟨5659643785588463724599191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546191714117951632798921 5659643785588463724599191)
            ·
              refine ⟨8489465678382695586898787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659643785588463724599191 8489465678382695586898787)
              ·
                refine ⟨12734198517574043380348181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489465678382695586898787 12734198517574043380348181)
                ·
                  refine ⟨596915555511283283453821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12734198517574043380348181 596915555511283283453821)
                  ·
                    refine ⟨223843333316731231295183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596915555511283283453821 223843333316731231295183)
                    ·
                      rfl

theorem cell22_653900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_653900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653900 prefixEnd_653900 := by exact prefixLift 653900
  have htrace : WordTrace (prefixWord ++ tailWord_653900) baseStart_653900 baseEnd_653900 := by
    simpa [prefixWord, tailWord_653900, baseEnd_653900] using wordTrace_append hprefix tailTrace_653900
  have hstable : (prefixWord ++ tailWord_653900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653900).length < 2 ^ (prefixWord ++ tailWord_653900).sum := by decide
  have hdescent : baseEnd_653900 < baseStart_653900 := by decide
  rcases family_descends (prefixWord ++ tailWord_653900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653902 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_653902 : Nat := 118140960795 + 653902 * 2 ^ 59
def prefixEnd_653902 : Nat := 4983230072969 + 3 ^ 40 * 653902 * 2
def baseEnd_653902 : Nat := 74614672652534630915059

theorem tailTrace_653902 : CollatzResearch.WordTrace tailWord_653902 prefixEnd_653902 74614672652534630915059 := by
  unfold tailWord_653902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981220659629025801950495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15899843518021470943735973 2981220659629025801950495)
  ·
    refine ⟨4471830989443538702925743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981220659629025801950495 4471830989443538702925743)
    ·
      refine ⟨6707746484165308054388615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471830989443538702925743 6707746484165308054388615)
      ·
        refine ⟨10061619726247962081582923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707746484165308054388615 10061619726247962081582923)
        ·
          refine ⟨15092429589371943122374385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061619726247962081582923 15092429589371943122374385)
          ·
            refine ⟨11319322192028957341780789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15092429589371943122374385 11319322192028957341780789)
            ·
              refine ⟨1061186455502714750791949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11319322192028957341780789 1061186455502714750791949)
              ·
                refine ⟨397944920813518031546981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061186455502714750791949 397944920813518031546981)
                ·
                  refine ⟨74614672652534630915059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397944920813518031546981 74614672652534630915059)
                  ·
                    rfl

theorem cell22_653902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_653902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653902 prefixEnd_653902 := by exact prefixLift 653902
  have htrace : WordTrace (prefixWord ++ tailWord_653902) baseStart_653902 baseEnd_653902 := by
    simpa [prefixWord, tailWord_653902, baseEnd_653902] using wordTrace_append hprefix tailTrace_653902
  have hstable : (prefixWord ++ tailWord_653902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653902).length < 2 ^ (prefixWord ++ tailWord_653902).sum := by decide
  have hdescent : baseEnd_653902 < baseStart_653902 := by decide
  rcases family_descends (prefixWord ++ tailWord_653902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653930 : List Nat := [3, 1, 3, 2, 1, 1, 4, 7]
def baseStart_653930 : Nat := 118140960795 + 653930 * 2 ^ 59
def prefixEnd_653930 : Nat := 4983230072969 + 3 ^ 40 * 653930 * 2
def baseEnd_653930 : Nat := 24872622547757905893899

theorem tailTrace_653930 : CollatzResearch.WordTrace tailWord_653930 prefixEnd_653930 24872622547757905893899 := by
  unfold tailWord_653930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962696630232691799405811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15900524347287178131748829 5962696630232691799405811)
  ·
    refine ⟨8944044945349037699108717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962696630232691799405811 8944044945349037699108717)
    ·
      refine ⟨3354016854505889137165769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8944044945349037699108717 3354016854505889137165769)
      ·
        refine ⟨2515512640879416852874327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354016854505889137165769 2515512640879416852874327)
        ·
          refine ⟨3773268961319125279311491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515512640879416852874327 3773268961319125279311491)
          ·
            refine ⟨5659903441978687918967237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773268961319125279311491 5659903441978687918967237)
            ·
              refine ⟨1061231895371003984806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5659903441978687918967237 1061231895371003984806357)
              ·
                refine ⟨24872622547757905893899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1061231895371003984806357 24872622547757905893899)
                ·
                  rfl

theorem cell22_653930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_653930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653930 prefixEnd_653930 := by exact prefixLift 653930
  have htrace : WordTrace (prefixWord ++ tailWord_653930) baseStart_653930 baseEnd_653930 := by
    simpa [prefixWord, tailWord_653930, baseEnd_653930] using wordTrace_append hprefix tailTrace_653930
  have hstable : (prefixWord ++ tailWord_653930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653930).length < 2 ^ (prefixWord ++ tailWord_653930).sum := by decide
  have hdescent : baseEnd_653930 < baseStart_653930 := by decide
  rcases family_descends (prefixWord ++ tailWord_653930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653934 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_653934 : Nat := 118140960795 + 653934 * 2 ^ 59
def prefixEnd_653934 : Nat := 4983230072969 + 3 ^ 40 * 653934 * 2
def baseEnd_653934 : Nat := 223854972211566475945079

theorem tailTrace_653934 : CollatzResearch.WordTrace tailWord_653934 prefixEnd_653934 223854972211566475945079 := by
  unfold tailWord_653934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981366551614534485096107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15900621608610850587179237 2981366551614534485096107)
  ·
    refine ⟨4472049827421801727644161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981366551614534485096107 4472049827421801727644161)
    ·
      refine ⟨3354037370566351295733121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4472049827421801727644161 3354037370566351295733121)
      ·
        refine ⟨2515528027924763471799841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354037370566351295733121 2515528027924763471799841)
        ·
          refine ⟨1886646020943572603849881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2515528027924763471799841 1886646020943572603849881)
          ·
            refine ⟨1414984515707679452887411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886646020943572603849881 1414984515707679452887411)
            ·
              refine ⟨2122476773561519179331117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414984515707679452887411 2122476773561519179331117)
              ·
                refine ⟨795928790085569692249169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122476773561519179331117 795928790085569692249169)
                ·
                  refine ⟨596946592564177269186877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795928790085569692249169 596946592564177269186877)
                  ·
                    refine ⟨223854972211566475945079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596946592564177269186877 223854972211566475945079)
                    ·
                      rfl

theorem cell22_653934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_653934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_653934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_653934 prefixEnd_653934 := by exact prefixLift 653934
  have htrace : WordTrace (prefixWord ++ tailWord_653934) baseStart_653934 baseEnd_653934 := by
    simpa [prefixWord, tailWord_653934, baseEnd_653934] using wordTrace_append hprefix tailTrace_653934
  have hstable : (prefixWord ++ tailWord_653934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653934).length < 2 ^ (prefixWord ++ tailWord_653934).sum := by decide
  have hdescent : baseEnd_653934 < baseStart_653934 := by decide
  rcases family_descends (prefixWord ++ tailWord_653934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654052 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_654052 : Nat := 118140960795 + 654052 * 2 ^ 59
def prefixEnd_654052 : Nat := 4983230072969 + 3 ^ 40 * 654052 * 2
def baseEnd_654052 : Nat := 223895366023053501494717

theorem tailTrace_654052 : CollatzResearch.WordTrace tailWord_654052 prefixEnd_654052 223895366023053501494717 := by
  unfold tailWord_654052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927618113244391016782205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15903490817659188022376273 11927618113244391016782205)
  ·
    refine ⟨4472856792466646631293327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11927618113244391016782205 4472856792466646631293327)
    ·
      refine ⟨6709285188699969946939991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472856792466646631293327 6709285188699969946939991)
      ·
        refine ⟨10063927783049954920409987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709285188699969946939991 10063927783049954920409987)
        ·
          refine ⟨15095891674574932380614981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10063927783049954920409987 15095891674574932380614981)
          ·
            refine ⟨2830479688982799821365309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15095891674574932380614981 2830479688982799821365309)
            ·
              refine ⟨1061429883368549933011991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2830479688982799821365309 1061429883368549933011991)
              ·
                refine ⟨1592144825052824899517987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061429883368549933011991 1592144825052824899517987)
                ·
                  refine ⟨2388217237579237349276981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592144825052824899517987 2388217237579237349276981)
                  ·
                    refine ⟨223895366023053501494717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2388217237579237349276981 223895366023053501494717)
                    ·
                      rfl

theorem cell22_654052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_654052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654052 prefixEnd_654052 := by exact prefixLift 654052
  have htrace : WordTrace (prefixWord ++ tailWord_654052) baseStart_654052 baseEnd_654052 := by
    simpa [prefixWord, tailWord_654052, baseEnd_654052] using wordTrace_append hprefix tailTrace_654052
  have hstable : (prefixWord ++ tailWord_654052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654052).length < 2 ^ (prefixWord ++ tailWord_654052).sum := by decide
  have hdescent : baseEnd_654052 < baseStart_654052 := by decide
  rcases family_descends (prefixWord ++ tailWord_654052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654065 : List Nat := [1, 2, 2, 2, 2, 2, 3, 8]
def baseStart_654065 : Nat := 118140960795 + 654065 * 2 ^ 59
def prefixEnd_654065 : Nat := 4983230072969 + 3 ^ 40 * 654065 * 2
def baseEnd_654065 : Nat := 24877757354302866768853

theorem tailTrace_654065 : CollatzResearch.WordTrace tailWord_654065 prefixEnd_654065 24877757354302866768853 := by
  unfold tailWord_654065
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855710375441685253787649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15903806916961123502525099 23855710375441685253787649)
  ·
    refine ⟨17891782781581263940340737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23855710375441685253787649 17891782781581263940340737)
    ·
      refine ⟨13418837086185947955255553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17891782781581263940340737 13418837086185947955255553)
      ·
        refine ⟨10064127814639460966441665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13418837086185947955255553 10064127814639460966441665)
        ·
          refine ⟨7548095860979595724831249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10064127814639460966441665 7548095860979595724831249)
          ·
            refine ⟨5661071895734696793623437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548095860979595724831249 5661071895734696793623437)
            ·
              refine ⟨2122901960900511297608789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661071895734696793623437 2122901960900511297608789)
              ·
                refine ⟨24877757354302866768853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2122901960900511297608789 24877757354302866768853)
                ·
                  rfl

theorem cell22_654065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 8].length) (baseStart_654065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654065 prefixEnd_654065 := by exact prefixLift 654065
  have htrace : WordTrace (prefixWord ++ tailWord_654065) baseStart_654065 baseEnd_654065 := by
    simpa [prefixWord, tailWord_654065, baseEnd_654065] using wordTrace_append hprefix tailTrace_654065
  have hstable : (prefixWord ++ tailWord_654065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654065).length < 2 ^ (prefixWord ++ tailWord_654065).sum := by decide
  have hdescent : baseEnd_654065 < baseStart_654065 := by decide
  rcases family_descends (prefixWord ++ tailWord_654065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654082 : List Nat := [3, 4, 1, 1, 1, 2, 10]
def baseStart_654082 : Nat := 118140960795 + 654082 * 2 ^ 59
def prefixEnd_654082 : Nat := 4983230072969 + 3 ^ 40 * 654082 * 2
def baseEnd_654082 : Nat := 8292801319857163823875

theorem tailTrace_654082 : CollatzResearch.WordTrace tailWord_654082 prefixEnd_654082 8292801319857163823875 := by
  unfold tailWord_654082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964082604095024289289125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15904220277586731438104333 5964082604095024289289125)
  ·
    refine ⟨1118265488267817054241711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5964082604095024289289125 1118265488267817054241711)
    ·
      refine ⟨1677398232401725581362567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118265488267817054241711 1677398232401725581362567)
      ·
        refine ⟨2516097348602588372043851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677398232401725581362567 2516097348602588372043851)
        ·
          refine ⟨3774146022903882558065777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516097348602588372043851 3774146022903882558065777)
          ·
            refine ⟨2830609517177911918549333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774146022903882558065777 2830609517177911918549333)
            ·
              refine ⟨8292801319857163823875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2830609517177911918549333 8292801319857163823875)
              ·
                rfl

theorem cell22_654082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 10].length) (baseStart_654082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654082 prefixEnd_654082 := by exact prefixLift 654082
  have htrace : WordTrace (prefixWord ++ tailWord_654082) baseStart_654082 baseEnd_654082 := by
    simpa [prefixWord, tailWord_654082, baseEnd_654082] using wordTrace_append hprefix tailTrace_654082
  have hstable : (prefixWord ++ tailWord_654082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654082).length < 2 ^ (prefixWord ++ tailWord_654082).sum := by decide
  have hdescent : baseEnd_654082 < baseStart_654082 := by decide
  rcases family_descends (prefixWord ++ tailWord_654082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654095 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_654095 : Nat := 118140960795 + 654095 * 2 ^ 59
def prefixEnd_654095 : Nat := 4983230072969 + 3 ^ 40 * 654095 * 2
def baseEnd_654095 : Nat := 223910085801815722669585

theorem tailTrace_654095 : CollatzResearch.WordTrace tailWord_654095 prefixEnd_654095 223910085801815722669585 := by
  unfold tailWord_654095
  simp only [CollatzResearch.WordTrace]
  refine ⟨23856804565333000377379739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15904536376888666918253159 23856804565333000377379739)
  ·
    refine ⟨35785206847999500566069609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23856804565333000377379739 35785206847999500566069609)
    ·
      refine ⟨26838905135999625424552207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35785206847999500566069609 26838905135999625424552207)
      ·
        refine ⟨40258357703999438136828311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26838905135999625424552207 40258357703999438136828311)
        ·
          refine ⟨60387536555999157205242467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40258357703999438136828311 60387536555999157205242467)
          ·
            refine ⟨90581304833998735807863701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60387536555999157205242467 90581304833998735807863701)
            ·
              refine ⟨4245998664093690740993611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90581304833998735807863701 4245998664093690740993611)
              ·
                refine ⟨6368997996140536111490417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245998664093690740993611 6368997996140536111490417)
                ·
                  refine ⟨4776748497105402083617813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368997996140536111490417 4776748497105402083617813)
                  ·
                    refine ⟨223910085801815722669585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4776748497105402083617813 223910085801815722669585)
                    ·
                      rfl

theorem cell22_654095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_654095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654095 prefixEnd_654095 := by exact prefixLift 654095
  have htrace : WordTrace (prefixWord ++ tailWord_654095) baseStart_654095 baseEnd_654095 := by
    simpa [prefixWord, tailWord_654095, baseEnd_654095] using wordTrace_append hprefix tailTrace_654095
  have hstable : (prefixWord ++ tailWord_654095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654095).length < 2 ^ (prefixWord ++ tailWord_654095).sum := by decide
  have hdescent : baseEnd_654095 < baseStart_654095 := by decide
  rcases family_descends (prefixWord ++ tailWord_654095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654103 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 2, 3]
def baseStart_654103 : Nat := 118140960795 + 654103 * 2 ^ 59
def prefixEnd_654103 : Nat := 4983230072969 + 3 ^ 40 * 654103 * 2
def baseEnd_654103 : Nat := 223912824365306368469561

theorem tailTrace_654103 : CollatzResearch.WordTrace tailWord_654103 prefixEnd_654103 223912824365306368469561 := by
  unfold tailWord_654103
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857096349304017743670963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15904730899536011829113975 23857096349304017743670963)
  ·
    refine ⟨35785644523956026615506445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857096349304017743670963 35785644523956026615506445)
    ·
      refine ⟨13419616696483509980814917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35785644523956026615506445 13419616696483509980814917)
      ·
        refine ⟨2516178130590658121402797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13419616696483509980814917 2516178130590658121402797)
        ·
          refine ⟨943566798971496795526049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2516178130590658121402797 943566798971496795526049)
          ·
            refine ⟨707675099228622596644537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943566798971496795526049 707675099228622596644537)
            ·
              refine ⟨530756324421466947483403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707675099228622596644537 530756324421466947483403)
              ·
                refine ⟨796134486632200421225105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530756324421466947483403 796134486632200421225105)
                ·
                  refine ⟨597100864974150315918829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796134486632200421225105 597100864974150315918829)
                  ·
                    refine ⟨223912824365306368469561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597100864974150315918829 223912824365306368469561)
                    ·
                      rfl

theorem cell22_654103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_654103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654103 prefixEnd_654103 := by exact prefixLift 654103
  have htrace : WordTrace (prefixWord ++ tailWord_654103) baseStart_654103 baseEnd_654103 := by
    simpa [prefixWord, tailWord_654103, baseEnd_654103] using wordTrace_append hprefix tailTrace_654103
  have hstable : (prefixWord ++ tailWord_654103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654103).length < 2 ^ (prefixWord ++ tailWord_654103).sum := by decide
  have hdescent : baseEnd_654103 < baseStart_654103 := by decide
  rcases family_descends (prefixWord ++ tailWord_654103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654155 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 12]
def baseStart_654155 : Nat := 118140960795 + 654155 * 2 ^ 59
def prefixEnd_654155 : Nat := 4983230072969 + 3 ^ 40 * 654155 * 2
def baseEnd_654155 : Nat := 74643541675998522056467

theorem tailTrace_654155 : CollatzResearch.WordTrace tailWord_654155 prefixEnd_654155 74643541675998522056467 := by
  unfold tailWord_654155
  simp only [CollatzResearch.WordTrace]
  refine ⟨23858992945115630624563919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15905995296743753749709279 23858992945115630624563919)
  ·
    refine ⟨35788489417673445936845879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23858992945115630624563919 35788489417673445936845879)
    ·
      refine ⟨53682734126510168905268819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35788489417673445936845879 53682734126510168905268819)
      ·
        refine ⟨80524101189765253357903229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53682734126510168905268819 80524101189765253357903229)
        ·
          refine ⟨30196537946161970009213711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80524101189765253357903229 30196537946161970009213711)
          ·
            refine ⟨45294806919242955013820567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30196537946161970009213711 45294806919242955013820567)
            ·
              refine ⟨67942210378864432520730851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45294806919242955013820567 67942210378864432520730851)
              ·
                refine ⟨101913315568296648781096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67942210378864432520730851 101913315568296648781096277)
                ·
                  refine ⟨74643541675998522056467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 101913315568296648781096277 74643541675998522056467)
                  ·
                    rfl

theorem cell22_654155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_654155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654155 prefixEnd_654155 := by exact prefixLift 654155
  have htrace : WordTrace (prefixWord ++ tailWord_654155) baseStart_654155 baseEnd_654155 := by
    simpa [prefixWord, tailWord_654155, baseEnd_654155] using wordTrace_append hprefix tailTrace_654155
  have hstable : (prefixWord ++ tailWord_654155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654155).length < 2 ^ (prefixWord ++ tailWord_654155).sum := by decide
  have hdescent : baseEnd_654155 < baseStart_654155 := by decide
  rcases family_descends (prefixWord ++ tailWord_654155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654187 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_654187 : Nat := 118140960795 + 654187 * 2 ^ 59
def prefixEnd_654187 : Nat := 4983230072969 + 3 ^ 40 * 654187 * 2
def baseEnd_654187 : Nat := 223941579281958149369303

theorem tailTrace_654187 : CollatzResearch.WordTrace tailWord_654187 prefixEnd_654187 223941579281958149369303 := by
  unfold tailWord_654187
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860160080999700089728815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15906773387333133393152543 23860160080999700089728815)
  ·
    refine ⟨35790240121499550134593223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23860160080999700089728815 35790240121499550134593223)
    ·
      refine ⟨53685360182249325201889835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35790240121499550134593223 53685360182249325201889835)
      ·
        refine ⟨80528040273373987802834753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53685360182249325201889835 80528040273373987802834753)
        ·
          refine ⟨60396030205030490852126065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80528040273373987802834753 60396030205030490852126065)
          ·
            refine ⟨45297022653772868139094549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60396030205030490852126065 45297022653772868139094549)
            ·
              refine ⟨2123297936895603194020057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45297022653772868139094549 2123297936895603194020057)
              ·
                refine ⟨1592473452671702395515043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123297936895603194020057 1592473452671702395515043)
                ·
                  refine ⟨2388710179007553593272565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592473452671702395515043 2388710179007553593272565)
                  ·
                    refine ⟨223941579281958149369303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2388710179007553593272565 223941579281958149369303)
                    ·
                      rfl

theorem cell22_654187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_654187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654187 prefixEnd_654187 := by exact prefixLift 654187
  have htrace : WordTrace (prefixWord ++ tailWord_654187) baseStart_654187 baseEnd_654187 := by
    simpa [prefixWord, tailWord_654187, baseEnd_654187] using wordTrace_append hprefix tailTrace_654187
  have hstable : (prefixWord ++ tailWord_654187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654187).length < 2 ^ (prefixWord ++ tailWord_654187).sum := by decide
  have hdescent : baseEnd_654187 < baseStart_654187 := by decide
  rcases family_descends (prefixWord ++ tailWord_654187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654202 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_654202 : Nat := 118140960795 + 654202 * 2 ^ 59
def prefixEnd_654202 : Nat := 4983230072969 + 3 ^ 40 * 654202 * 2
def baseEnd_654202 : Nat := 223946714088503110244257

theorem tailTrace_654202 : CollatzResearch.WordTrace tailWord_654202 prefixEnd_654202 223946714088503110244257 := by
  unfold tailWord_654202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965176793986339412881215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15907138117296905101016573 5965176793986339412881215)
  ·
    refine ⟨8947765190979509119321823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5965176793986339412881215 8947765190979509119321823)
    ·
      refine ⟨13421647786469263678982735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8947765190979509119321823 13421647786469263678982735)
      ·
        refine ⟨20132471679703895518474103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13421647786469263678982735 20132471679703895518474103)
        ·
          refine ⟨30198707519555843277711155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20132471679703895518474103 30198707519555843277711155)
          ·
            refine ⟨45298061279333764916566733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30198707519555843277711155 45298061279333764916566733)
            ·
              refine ⟨16986772979750161843712525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45298061279333764916566733 16986772979750161843712525)
              ·
                refine ⟨6370039867406310691392197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16986772979750161843712525 6370039867406310691392197)
                ·
                  refine ⟨1194382475138683254636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6370039867406310691392197 1194382475138683254636037)
                  ·
                    refine ⟨223946714088503110244257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194382475138683254636037 223946714088503110244257)
                    ·
                      rfl

theorem cell22_654202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_654202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654202 prefixEnd_654202 := by exact prefixLift 654202
  have htrace : WordTrace (prefixWord ++ tailWord_654202) baseStart_654202 baseEnd_654202 := by
    simpa [prefixWord, tailWord_654202, baseEnd_654202] using wordTrace_append hprefix tailTrace_654202
  have hstable : (prefixWord ++ tailWord_654202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654202).length < 2 ^ (prefixWord ++ tailWord_654202).sum := by decide
  have hdescent : baseEnd_654202 < baseStart_654202 := by decide
  rcases family_descends (prefixWord ++ tailWord_654202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654234 : List Nat := [3, 1, 1, 4, 3, 1, 1, 8]
def baseStart_654234 : Nat := 118140960795 + 654234 * 2 ^ 59
def prefixEnd_654234 : Nat := 4983230072969 + 3 ^ 40 * 654234 * 2
def baseEnd_654234 : Nat := 24884185371385077049351

theorem tailTrace_654234 : CollatzResearch.WordTrace tailWord_654234 prefixEnd_654234 24884185371385077049351 := by
  unfold tailWord_654234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965468577957356779172439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15907916207886284744459837 5965468577957356779172439)
  ·
    refine ⟨8948202866936035168758659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5965468577957356779172439 8948202866936035168758659)
    ·
      refine ⟨13422304300404052753137989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8948202866936035168758659 13422304300404052753137989)
      ·
        refine ⟨2516682056325759891213373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13422304300404052753137989 2516682056325759891213373)
        ·
          refine ⟨943755771122159959205015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2516682056325759891213373 943755771122159959205015)
          ·
            refine ⟨1415633656683239938807523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943755771122159959205015 1415633656683239938807523)
            ·
              refine ⟨2123450485024859908211285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415633656683239938807523 2123450485024859908211285)
              ·
                refine ⟨24884185371385077049351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2123450485024859908211285 24884185371385077049351)
                ·
                  rfl

theorem cell22_654234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_654234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654234 prefixEnd_654234 := by exact prefixLift 654234
  have htrace : WordTrace (prefixWord ++ tailWord_654234) baseStart_654234 baseEnd_654234 := by
    simpa [prefixWord, tailWord_654234, baseEnd_654234] using wordTrace_append hprefix tailTrace_654234
  have hstable : (prefixWord ++ tailWord_654234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654234).length < 2 ^ (prefixWord ++ tailWord_654234).sum := by decide
  have hdescent : baseEnd_654234 < baseStart_654234 := by decide
  rcases family_descends (prefixWord ++ tailWord_654234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654253 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_654253 : Nat := 118140960795 + 654253 * 2 ^ 59
def prefixEnd_654253 : Nat := 4983230072969 + 3 ^ 40 * 654253 * 2
def baseEnd_654253 : Nat := 223964172430755977219101

theorem tailTrace_654253 : CollatzResearch.WordTrace tailWord_654253 prefixEnd_654253 223964172430755977219101 := by
  unfold tailWord_654253
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862567298760593361631413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15908378199173728907754275 23862567298760593361631413)
  ·
    refine ⟨2237115684258805627652945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23862567298760593361631413 2237115684258805627652945)
    ·
      refine ⟨1677836763194104220739709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237115684258805627652945 1677836763194104220739709)
      ·
        refine ⟨629188786197789082777391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1677836763194104220739709 629188786197789082777391)
        ·
          refine ⟨943783179296683624166087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629188786197789082777391 943783179296683624166087)
          ·
            refine ⟨1415674768945025436249131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943783179296683624166087 1415674768945025436249131)
            ·
              refine ⟨2123512153417538154373697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415674768945025436249131 2123512153417538154373697)
              ·
                refine ⟨1592634115063153615780273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123512153417538154373697 1592634115063153615780273)
                ·
                  refine ⟨1194475586297365211835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1592634115063153615780273 1194475586297365211835205)
                  ·
                    refine ⟨223964172430755977219101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194475586297365211835205 223964172430755977219101)
                    ·
                      rfl

theorem cell22_654253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_654253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654253 prefixEnd_654253 := by exact prefixLift 654253
  have htrace : WordTrace (prefixWord ++ tailWord_654253) baseStart_654253 baseEnd_654253 := by
    simpa [prefixWord, tailWord_654253, baseEnd_654253] using wordTrace_append hprefix tailTrace_654253
  have hstable : (prefixWord ++ tailWord_654253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654253).length < 2 ^ (prefixWord ++ tailWord_654253).sum := by decide
  have hdescent : baseEnd_654253 < baseStart_654253 := by decide
  rcases family_descends (prefixWord ++ tailWord_654253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654277 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_654277 : Nat := 118140960795 + 654277 * 2 ^ 59
def prefixEnd_654277 : Nat := 4983230072969 + 3 ^ 40 * 654277 * 2
def baseEnd_654277 : Nat := 223972388121227914619027

theorem tailTrace_654277 : CollatzResearch.WordTrace tailWord_654277 prefixEnd_654277 223972388121227914619027 := by
  unfold tailWord_654277
  simp only [CollatzResearch.WordTrace]
  refine ⟨23863442650673645460505085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15908961767115763640336723 23863442650673645460505085)
  ·
    refine ⟨8948790994002617047689407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23863442650673645460505085 8948790994002617047689407)
    ·
      refine ⟨13423186491003925571534111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8948790994002617047689407 13423186491003925571534111)
      ·
        refine ⟨20134779736505888357301167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423186491003925571534111 20134779736505888357301167)
        ·
          refine ⟨30202169604758832535951751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20134779736505888357301167 30202169604758832535951751)
          ·
            refine ⟨45303254407138248803927627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30202169604758832535951751 45303254407138248803927627)
            ·
              refine ⟨67954881610707373205891441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45303254407138248803927627 67954881610707373205891441)
              ·
                refine ⟨50966161208030529904418581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67954881610707373205891441 50966161208030529904418581)
                ·
                  refine ⟨2389038806626431089269621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50966161208030529904418581 2389038806626431089269621)
                  ·
                    refine ⟨223972388121227914619027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2389038806626431089269621 223972388121227914619027)
                    ·
                      rfl

theorem cell22_654277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_654277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654277 prefixEnd_654277 := by exact prefixLift 654277
  have htrace : WordTrace (prefixWord ++ tailWord_654277) baseStart_654277 baseEnd_654277 := by
    simpa [prefixWord, tailWord_654277, baseEnd_654277] using wordTrace_append hprefix tailTrace_654277
  have hstable : (prefixWord ++ tailWord_654277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654277).length < 2 ^ (prefixWord ++ tailWord_654277).sum := by decide
  have hdescent : baseEnd_654277 < baseStart_654277 := by decide
  rcases family_descends (prefixWord ++ tailWord_654277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654326 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_654326 : Nat := 118140960795 + 654326 * 2 ^ 59
def prefixEnd_654326 : Nat := 4983230072969 + 3 ^ 40 * 654326 * 2
def baseEnd_654326 : Nat := 223989161822608120143877

theorem tailTrace_654326 : CollatzResearch.WordTrace tailWord_654326 prefixEnd_654326 223989161822608120143877 := by
  unfold tailWord_654326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491576864218507926814927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15910153218330751219359221 1491576864218507926814927)
  ·
    refine ⟨2237365296327761890222391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1491576864218507926814927 2237365296327761890222391)
    ·
      refine ⟨3356047944491642835333587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237365296327761890222391 3356047944491642835333587)
      ·
        refine ⟨5034071916737464253000381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356047944491642835333587 5034071916737464253000381)
        ·
          refine ⟨1887776968776549094875143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5034071916737464253000381 1887776968776549094875143)
          ·
            refine ⟨2831665453164823642312715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887776968776549094875143 2831665453164823642312715)
            ·
              refine ⟨4247498179747235463469073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831665453164823642312715 4247498179747235463469073)
              ·
                refine ⟨3185623634810426597601805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247498179747235463469073 3185623634810426597601805)
                ·
                  refine ⟨1194608863053909974100677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3185623634810426597601805 1194608863053909974100677)
                  ·
                    refine ⟨223989161822608120143877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194608863053909974100677 223989161822608120143877)
                    ·
                      rfl

theorem cell22_654326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_654326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654326 prefixEnd_654326 := by exact prefixLift 654326
  have htrace : WordTrace (prefixWord ++ tailWord_654326) baseStart_654326 baseEnd_654326 := by
    simpa [prefixWord, tailWord_654326, baseEnd_654326] using wordTrace_append hprefix tailTrace_654326
  have hstable : (prefixWord ++ tailWord_654326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654326).length < 2 ^ (prefixWord ++ tailWord_654326).sum := by decide
  have hdescent : baseEnd_654326 < baseStart_654326 := by decide
  rcases family_descends (prefixWord ++ tailWord_654326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654339 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 8, 3]
def baseStart_654339 : Nat := 118140960795 + 654339 * 2 ^ 59
def prefixEnd_654339 : Nat := 4983230072969 + 3 ^ 40 * 654339 * 2
def baseEnd_654339 : Nat := 223993611988280419568837

theorem tailTrace_654339 : CollatzResearch.WordTrace tailWord_654339 prefixEnd_654339 223993611988280419568837 := by
  unfold tailWord_654339
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865703976449030049262071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15910469317632686699508047 23865703976449030049262071)
  ·
    refine ⟨35798555964673545073893107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23865703976449030049262071 35798555964673545073893107)
    ·
      refine ⟨53697833947010317610839661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35798555964673545073893107 53697833947010317610839661)
      ·
        refine ⟨20136687730128869104064873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53697833947010317610839661 20136687730128869104064873)
        ·
          refine ⟨15102515797596651828048655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20136687730128869104064873 15102515797596651828048655)
          ·
            refine ⟨22653773696394977742072983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15102515797596651828048655 22653773696394977742072983)
            ·
              refine ⟨33980660544592466613109475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22653773696394977742072983 33980660544592466613109475)
              ·
                refine ⟨50970990816888699919664213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33980660544592466613109475 50970990816888699919664213)
                ·
                  refine ⟨597316298635414452183565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 50970990816888699919664213 597316298635414452183565)
                  ·
                    refine ⟨223993611988280419568837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597316298635414452183565 223993611988280419568837)
                    ·
                      rfl

theorem cell22_654339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].length) (baseStart_654339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654339 prefixEnd_654339 := by exact prefixLift 654339
  have htrace : WordTrace (prefixWord ++ tailWord_654339) baseStart_654339 baseEnd_654339 := by
    simpa [prefixWord, tailWord_654339, baseEnd_654339] using wordTrace_append hprefix tailTrace_654339
  have hstable : (prefixWord ++ tailWord_654339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654339).length < 2 ^ (prefixWord ++ tailWord_654339).sum := by decide
  have hdescent : baseEnd_654339 < baseStart_654339 := by decide
  rcases family_descends (prefixWord ++ tailWord_654339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654369 : List Nat := [1, 2, 3, 2, 3, 2, 9]
def baseStart_654369 : Nat := 118140960795 + 654369 * 2 ^ 59
def prefixEnd_654369 : Nat := 4983230072969 + 3 ^ 40 * 654369 * 2
def baseEnd_654369 : Nat := 8296440059310012641435

theorem tailTrace_654369 : CollatzResearch.WordTrace tailWord_654369 prefixEnd_654369 8296440059310012641435 := by
  unfold tailWord_654369
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866798166340345172854161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15911198777560230115236107 23866798166340345172854161)
  ·
    refine ⟨17900098624755258879640621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23866798166340345172854161 17900098624755258879640621)
    ·
      refine ⟨6712536984283222079865233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17900098624755258879640621 6712536984283222079865233)
      ·
        refine ⟨5034402738212416559898925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6712536984283222079865233 5034402738212416559898925)
        ·
          refine ⟨1887901026829656209962097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5034402738212416559898925 1887901026829656209962097)
          ·
            refine ⟨1415925770122242157471573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887901026829656209962097 1415925770122242157471573)
            ·
              refine ⟨8296440059310012641435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1415925770122242157471573 8296440059310012641435)
              ·
                rfl

theorem cell22_654369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 9].length) (baseStart_654369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654369 prefixEnd_654369 := by exact prefixLift 654369
  have htrace : WordTrace (prefixWord ++ tailWord_654369) baseStart_654369 baseEnd_654369 := by
    simpa [prefixWord, tailWord_654369, baseEnd_654369] using wordTrace_append hprefix tailTrace_654369
  have hstable : (prefixWord ++ tailWord_654369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654369).length < 2 ^ (prefixWord ++ tailWord_654369).sum := by decide
  have hdescent : baseEnd_654369 < baseStart_654369 := by decide
  rcases family_descends (prefixWord ++ tailWord_654369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654414 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_654414 : Nat := 118140960795 + 654414 * 2 ^ 59
def prefixEnd_654414 : Nat := 4983230072969 + 3 ^ 40 * 654414 * 2
def baseEnd_654414 : Nat := 74673095340335074647869

theorem tailTrace_654414 : CollatzResearch.WordTrace tailWord_654414 prefixEnd_654414 74673095340335074647869 := by
  unfold tailWord_654414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983554931397164732280287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15912292967451545238828197 2983554931397164732280287)
  ·
    refine ⟨4475332397095747098420431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2983554931397164732280287 4475332397095747098420431)
    ·
      refine ⟨6712998595643620647630647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475332397095747098420431 6712998595643620647630647)
      ·
        refine ⟨10069497893465430971445971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712998595643620647630647 10069497893465430971445971)
        ·
          refine ⟨15104246840198146457168957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069497893465430971445971 15104246840198146457168957)
          ·
            refine ⟨5664092565074304921438359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15104246840198146457168957 5664092565074304921438359)
            ·
              refine ⟨8496138847611457382157539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664092565074304921438359 8496138847611457382157539)
              ·
                refine ⟨12744208271417186073236309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496138847611457382157539 12744208271417186073236309)
                ·
                  refine ⟨74673095340335074647869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12744208271417186073236309 74673095340335074647869)
                  ·
                    rfl

theorem cell22_654414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_654414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654414 prefixEnd_654414 := by exact prefixLift 654414
  have htrace : WordTrace (prefixWord ++ tailWord_654414) baseStart_654414 baseEnd_654414 := by
    simpa [prefixWord, tailWord_654414, baseEnd_654414] using wordTrace_append hprefix tailTrace_654414
  have hstable : (prefixWord ++ tailWord_654414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654414).length < 2 ^ (prefixWord ++ tailWord_654414).sum := by decide
  have hdescent : baseEnd_654414 < baseStart_654414 := by decide
  rcases family_descends (prefixWord ++ tailWord_654414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654459 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 6]
def baseStart_654459 : Nat := 118140960795 + 654459 * 2 ^ 59
def prefixEnd_654459 : Nat := 4983230072969 + 3 ^ 40 * 654459 * 2
def baseEnd_654459 : Nat := 74678230146880035522823

theorem tailTrace_654459 : CollatzResearch.WordTrace tailWord_654459 prefixEnd_654459 74678230146880035522823 := by
  unfold tailWord_654459
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870080736014290543630431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15913387157342860362420287 23870080736014290543630431)
  ·
    refine ⟨35805121104021435815445647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870080736014290543630431 35805121104021435815445647)
    ·
      refine ⟨53707681656032153723168471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35805121104021435815445647 53707681656032153723168471)
      ·
        refine ⟨80561522484048230584752707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53707681656032153723168471 80561522484048230584752707)
        ·
          refine ⟨120842283726072345877129061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80561522484048230584752707 120842283726072345877129061)
          ·
            refine ⟨22657928198638564851961699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120842283726072345877129061 22657928198638564851961699)
            ·
              refine ⟨33986892297957847277942549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22657928198638564851961699 33986892297957847277942549)
              ·
                refine ⟨1593135576466774091153557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33986892297957847277942549 1593135576466774091153557)
                ·
                  refine ⟨74678230146880035522823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1593135576466774091153557 74678230146880035522823)
                  ·
                    rfl

theorem cell22_654459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_654459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654459 prefixEnd_654459 := by exact prefixLift 654459
  have htrace : WordTrace (prefixWord ++ tailWord_654459) baseStart_654459 baseEnd_654459 := by
    simpa [prefixWord, tailWord_654459, baseEnd_654459] using wordTrace_append hprefix tailTrace_654459
  have hstable : (prefixWord ++ tailWord_654459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654459).length < 2 ^ (prefixWord ++ tailWord_654459).sum := by decide
  have hdescent : baseEnd_654459 < baseStart_654459 := by decide
  rcases family_descends (prefixWord ++ tailWord_654459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654461 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_654461 : Nat := 118140960795 + 654461 * 2 ^ 59
def prefixEnd_654461 : Nat := 4983230072969 + 3 ^ 40 * 654461 * 2
def baseEnd_654461 : Nat := 224035375081512768018463

theorem tailTrace_654461 : CollatzResearch.WordTrace tailWord_654461 prefixEnd_654461 224035375081512768018463 := by
  unfold tailWord_654461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870153682007044885203237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15913435788004696590135491 23870153682007044885203237)
  ·
    refine ⟨4475653815376320915975607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23870153682007044885203237 4475653815376320915975607)
    ·
      refine ⟨6713480723064481373963411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475653815376320915975607 6713480723064481373963411)
      ·
        refine ⟨10070221084596722060945117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713480723064481373963411 10070221084596722060945117)
        ·
          refine ⟨3776332906723770772854419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070221084596722060945117 3776332906723770772854419)
          ·
            refine ⟨5664499360085656159281629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776332906723770772854419 5664499360085656159281629)
            ·
              refine ⟨2124187260032121059730611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664499360085656159281629 2124187260032121059730611)
              ·
                refine ⟨3186280890048181589595917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124187260032121059730611 3186280890048181589595917)
                ·
                  refine ⟨1194855333768068096098469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3186280890048181589595917 1194855333768068096098469)
                  ·
                    refine ⟨224035375081512768018463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1194855333768068096098469 224035375081512768018463)
                    ·
                      rfl

theorem cell22_654461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_654461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654461 prefixEnd_654461 := by exact prefixLift 654461
  have htrace : WordTrace (prefixWord ++ tailWord_654461) baseStart_654461 baseEnd_654461 := by
    simpa [prefixWord, tailWord_654461, baseEnd_654461] using wordTrace_append hprefix tailTrace_654461
  have hstable : (prefixWord ++ tailWord_654461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654461).length < 2 ^ (prefixWord ++ tailWord_654461).sum := by decide
  have hdescent : baseEnd_654461 < baseStart_654461 := by decide
  rcases family_descends (prefixWord ++ tailWord_654461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654489 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_654489 : Nat := 118140960795 + 654489 * 2 ^ 59
def prefixEnd_654489 : Nat := 4983230072969 + 3 ^ 40 * 654489 * 2
def baseEnd_654489 : Nat := 224044960053730028318377

theorem tailTrace_654489 : CollatzResearch.WordTrace tailWord_654489 prefixEnd_654489 224044960053730028318377 := by
  unfold tailWord_654489
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871174925905605667222521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15914116617270403778148347 23871174925905605667222521)
  ·
    refine ⟨17903381194429204250416891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23871174925905605667222521 17903381194429204250416891)
    ·
      refine ⟨26855071791643806375625337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17903381194429204250416891 26855071791643806375625337)
      ·
        refine ⟨20141303843732854781719003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26855071791643806375625337 20141303843732854781719003)
        ·
          refine ⟨30211955765599282172578505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20141303843732854781719003 30211955765599282172578505)
          ·
            refine ⟨22658966824199461629433879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30211955765599282172578505 22658966824199461629433879)
            ·
              refine ⟨33988450236299192444150819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22658966824199461629433879 33988450236299192444150819)
              ·
                refine ⟨50982675354448788666226229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33988450236299192444150819 50982675354448788666226229)
                ·
                  refine ⟨4779625814479573937458709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50982675354448788666226229 4779625814479573937458709)
                  ·
                    refine ⟨224044960053730028318377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4779625814479573937458709 224044960053730028318377)
                    ·
                      rfl

theorem cell22_654489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_654489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654489 prefixEnd_654489 := by exact prefixLift 654489
  have htrace : WordTrace (prefixWord ++ tailWord_654489) baseStart_654489 baseEnd_654489 := by
    simpa [prefixWord, tailWord_654489, baseEnd_654489] using wordTrace_append hprefix tailTrace_654489
  have hstable : (prefixWord ++ tailWord_654489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654489).length < 2 ^ (prefixWord ++ tailWord_654489).sum := by decide
  have hdescent : baseEnd_654489 < baseStart_654489 := by decide
  rcases family_descends (prefixWord ++ tailWord_654489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654493 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 4]
def baseStart_654493 : Nat := 118140960795 + 654493 * 2 ^ 59
def prefixEnd_654493 : Nat := 4983230072969 + 3 ^ 40 * 654493 * 2
def baseEnd_654493 : Nat := 74682109778491783739455

theorem tailTrace_654493 : CollatzResearch.WordTrace tailWord_654493 prefixEnd_654493 74682109778491783739455 := by
  unfold tailWord_654493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871320817891114350368133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15914213878594076233578755 23871320817891114350368133)
  ·
    refine ⟨4475872653354583940694025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23871320817891114350368133 4475872653354583940694025)
    ·
      refine ⟨3356904490015937955520519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4475872653354583940694025 3356904490015937955520519)
      ·
        refine ⟨5035356735023906933280779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356904490015937955520519 5035356735023906933280779)
        ·
          refine ⟨7553035102535860399921169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035356735023906933280779 7553035102535860399921169)
          ·
            refine ⟨5664776326901895299940877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7553035102535860399921169 5664776326901895299940877)
            ·
              refine ⟨2124291122588210737477829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664776326901895299940877 2124291122588210737477829)
              ·
                refine ⟨398304585485289513277093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2124291122588210737477829 398304585485289513277093)
                ·
                  refine ⟨74682109778491783739455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398304585485289513277093 74682109778491783739455)
                  ·
                    rfl

theorem cell22_654493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_654493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654493 prefixEnd_654493 := by exact prefixLift 654493
  have htrace : WordTrace (prefixWord ++ tailWord_654493) baseStart_654493 baseEnd_654493 := by
    simpa [prefixWord, tailWord_654493, baseEnd_654493] using wordTrace_append hprefix tailTrace_654493
  have hstable : (prefixWord ++ tailWord_654493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654493).length < 2 ^ (prefixWord ++ tailWord_654493).sum := by decide
  have hdescent : baseEnd_654493 < baseStart_654493 := by decide
  rcases family_descends (prefixWord ++ tailWord_654493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654542 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_654542 : Nat := 118140960795 + 654542 * 2 ^ 59
def prefixEnd_654542 : Nat := 4983230072969 + 3 ^ 40 * 654542 * 2
def baseEnd_654542 : Nat := 224063103036855556743215

theorem tailTrace_654542 : CollatzResearch.WordTrace tailWord_654542 prefixEnd_654542 224063103036855556743215 := by
  unfold tailWord_654542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984138499339199464862735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15915405329809063812601253 2984138499339199464862735)
  ·
    refine ⟨4476207749008799197294103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984138499339199464862735 4476207749008799197294103)
    ·
      refine ⟨6714311623513198795941155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476207749008799197294103 6714311623513198795941155)
      ·
        refine ⟨10071467435269798193911733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714311623513198795941155 10071467435269798193911733)
        ·
          refine ⟨944200072056543580679225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10071467435269798193911733 944200072056543580679225)
          ·
            refine ⟨708150054042407685509419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944200072056543580679225 708150054042407685509419)
            ·
              refine ⟨1062225081063611528264129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708150054042407685509419 1062225081063611528264129)
              ·
                refine ⟨796668810797708646198097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062225081063611528264129 796668810797708646198097)
                ·
                  refine ⟨597501608098281484648573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796668810797708646198097 597501608098281484648573)
                  ·
                    refine ⟨224063103036855556743215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597501608098281484648573 224063103036855556743215)
                    ·
                      rfl

theorem cell22_654542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_654542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654542 prefixEnd_654542 := by exact prefixLift 654542
  have htrace : WordTrace (prefixWord ++ tailWord_654542) baseStart_654542 baseEnd_654542 := by
    simpa [prefixWord, tailWord_654542, baseEnd_654542] using wordTrace_append hprefix tailTrace_654542
  have hstable : (prefixWord ++ tailWord_654542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654542).length < 2 ^ (prefixWord ++ tailWord_654542).sum := by decide
  have hdescent : baseEnd_654542 < baseStart_654542 := by decide
  rcases family_descends (prefixWord ++ tailWord_654542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654643 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_654643 : Nat := 118140960795 + 654643 * 2 ^ 59
def prefixEnd_654643 : Nat := 4983230072969 + 3 ^ 40 * 654643 * 2
def baseEnd_654643 : Nat := 224097677400924959967905

theorem tailTrace_654643 : CollatzResearch.WordTrace tailWord_654643 prefixEnd_654643 224097677400924959967905 := by
  unfold tailWord_654643
  simp only [CollatzResearch.WordTrace]
  refine ⟨23876791767347689968328583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15917861178231793312219055 23876791767347689968328583)
  ·
    refine ⟨35815187651021534952492875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23876791767347689968328583 35815187651021534952492875)
    ·
      refine ⟨53722781476532302428739313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35815187651021534952492875 53722781476532302428739313)
      ·
        refine ⟨40292086107399226821554485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53722781476532302428739313 40292086107399226821554485)
        ·
          refine ⟨3777383072568677514520733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40292086107399226821554485 3777383072568677514520733)
          ·
            refine ⟨1416518652213254067945275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3777383072568677514520733 1416518652213254067945275)
            ·
              refine ⟨2124777978319881101917913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416518652213254067945275 2124777978319881101917913)
              ·
                refine ⟨1593583483739910826438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124777978319881101917913 1593583483739910826438435)
                ·
                  refine ⟨2390375225609866239657653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593583483739910826438435 2390375225609866239657653)
                  ·
                    refine ⟨224097677400924959967905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2390375225609866239657653 224097677400924959967905)
                    ·
                      rfl

theorem cell22_654643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_654643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654643 prefixEnd_654643 := by exact prefixLift 654643
  have htrace : WordTrace (prefixWord ++ tailWord_654643) baseStart_654643 baseEnd_654643 := by
    simpa [prefixWord, tailWord_654643, baseEnd_654643] using wordTrace_append hprefix tailTrace_654643
  have hstable : (prefixWord ++ tailWord_654643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654643).length < 2 ^ (prefixWord ++ tailWord_654643).sum := by decide
  have hdescent : baseEnd_654643 < baseStart_654643 := by decide
  rcases family_descends (prefixWord ++ tailWord_654643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654690 : List Nat := [3, 3, 2, 1, 1, 1, 5, 6]
def baseStart_654690 : Nat := 118140960795 + 654690 * 2 ^ 59
def prefixEnd_654690 : Nat := 4983230072969 + 3 ^ 40 * 654690 * 2
def baseEnd_654690 : Nat := 24901529606825833782529

theorem tailTrace_654690 : CollatzResearch.WordTrace tailWord_654690 prefixEnd_654690 24901529606825833782529 := by
  unfold tailWord_654690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969626499544354248822381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15919003998784944663526349 5969626499544354248822381)
  ·
    refine ⟨2238609937329132843308393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5969626499544354248822381 2238609937329132843308393)
    ·
      refine ⟨1678957452996849632481295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2238609937329132843308393 1678957452996849632481295)
      ·
        refine ⟨2518436179495274448721943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678957452996849632481295 2518436179495274448721943)
        ·
          refine ⟨3777654269242911673082915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518436179495274448721943 3777654269242911673082915)
          ·
            refine ⟨5666481403864367509624373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777654269242911673082915 5666481403864367509624373)
            ·
              refine ⟨531232631612284454027285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5666481403864367509624373 531232631612284454027285)
              ·
                refine ⟨24901529606825833782529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 531232631612284454027285 24901529606825833782529)
                ·
                  rfl

theorem cell22_654690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_654690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654690 prefixEnd_654690 := by exact prefixLift 654690
  have htrace : WordTrace (prefixWord ++ tailWord_654690) baseStart_654690 baseEnd_654690 := by
    simpa [prefixWord, tailWord_654690, baseEnd_654690] using wordTrace_append hprefix tailTrace_654690
  have hstable : (prefixWord ++ tailWord_654690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654690).length < 2 ^ (prefixWord ++ tailWord_654690).sum := by decide
  have hdescent : baseEnd_654690 < baseStart_654690 := by decide
  rcases family_descends (prefixWord ++ tailWord_654690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654793 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_654793 : Nat := 118140960795 + 654793 * 2 ^ 59
def prefixEnd_654793 : Nat := 4983230072969 + 3 ^ 40 * 654793 * 2
def baseEnd_654793 : Nat := 224149025466374568717445

theorem tailTrace_654793 : CollatzResearch.WordTrace tailWord_654793 prefixEnd_654793 224149025466374568717445 := by
  unfold tailWord_654793
  simp only [CollatzResearch.WordTrace]
  refine ⟨23882262716804265586289033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15921508477869510390859355 23882262716804265586289033)
  ·
    refine ⟨17911697037603199189716775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23882262716804265586289033 17911697037603199189716775)
    ·
      refine ⟨26867545556404798784575163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911697037603199189716775 26867545556404798784575163)
      ·
        refine ⟨40301318334607198176862745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26867545556404798784575163 40301318334607198176862745)
        ·
          refine ⟨30225988750955398632647059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40301318334607198176862745 30225988750955398632647059)
          ·
            refine ⟨45338983126433097948970589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30225988750955398632647059 45338983126433097948970589)
            ·
              refine ⟨17002118672412411730863971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45338983126433097948970589 17002118672412411730863971)
              ·
                refine ⟨25503178008618617596295957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17002118672412411730863971 25503178008618617596295957)
                ·
                  refine ⟨1195461469153997699826373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25503178008618617596295957 1195461469153997699826373)
                  ·
                    refine ⟨224149025466374568717445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195461469153997699826373 224149025466374568717445)
                    ·
                      rfl

theorem cell22_654793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_654793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654793 prefixEnd_654793 := by exact prefixLift 654793
  have htrace : WordTrace (prefixWord ++ tailWord_654793) baseStart_654793 baseEnd_654793 := by
    simpa [prefixWord, tailWord_654793, baseEnd_654793] using wordTrace_append hprefix tailTrace_654793
  have hstable : (prefixWord ++ tailWord_654793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654793).length < 2 ^ (prefixWord ++ tailWord_654793).sum := by decide
  have hdescent : baseEnd_654793 < baseStart_654793 := by decide
  rcases family_descends (prefixWord ++ tailWord_654793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654808 : List Nat := [2, 1, 2, 2, 2, 1, 4, 8]
def baseStart_654808 : Nat := 118140960795 + 654808 * 2 ^ 59
def prefixEnd_654808 : Nat := 4983230072969 + 3 ^ 40 * 654808 * 2
def baseEnd_654808 : Nat := 24906017808102169954711

theorem tailTrace_654808 : CollatzResearch.WordTrace tailWord_654808 prefixEnd_654808 24906017808102169954711 := by
  unfold tailWord_654808
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941404905874961574042539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15921873207833282098723385 11941404905874961574042539)
  ·
    refine ⟨17912107358812442361063809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941404905874961574042539 17912107358812442361063809)
    ·
      refine ⟨13434080519109331770797857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17912107358812442361063809 13434080519109331770797857)
      ·
        refine ⟨10075560389331998828098393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13434080519109331770797857 10075560389331998828098393)
        ·
          refine ⟨7556670291998999121073795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10075560389331998828098393 7556670291998999121073795)
          ·
            refine ⟨11335005437998498681610693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556670291998999121073795 11335005437998498681610693)
            ·
              refine ⟨2125313519624718502802005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11335005437998498681610693 2125313519624718502802005)
              ·
                refine ⟨24906017808102169954711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2125313519624718502802005 24906017808102169954711)
                ·
                  rfl

theorem cell22_654808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_654808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654808 prefixEnd_654808 := by exact prefixLift 654808
  have htrace : WordTrace (prefixWord ++ tailWord_654808) baseStart_654808 baseEnd_654808 := by
    simpa [prefixWord, tailWord_654808, baseEnd_654808] using wordTrace_append hprefix tailTrace_654808
  have hstable : (prefixWord ++ tailWord_654808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654808).length < 2 ^ (prefixWord ++ tailWord_654808).sum := by decide
  have hdescent : baseEnd_654808 < baseStart_654808 := by decide
  rcases family_descends (prefixWord ++ tailWord_654808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654810 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_654810 : Nat := 118140960795 + 654810 * 2 ^ 59
def prefixEnd_654810 : Nat := 4983230072969 + 3 ^ 40 * 654810 * 2
def baseEnd_654810 : Nat := 224154844913792191042393

theorem tailTrace_654810 : CollatzResearch.WordTrace tailWord_654810 prefixEnd_654810 224154844913792191042393 := by
  unfold tailWord_654810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970720689435669372414471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15921921838495118326438589 5970720689435669372414471)
  ·
    refine ⟨8956081034153504058621707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5970720689435669372414471 8956081034153504058621707)
    ·
      refine ⟨13434121551230256087932561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8956081034153504058621707 13434121551230256087932561)
      ·
        refine ⟨10075591163422692065949421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13434121551230256087932561 10075591163422692065949421)
        ·
          refine ⟨3778346686283509524731033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10075591163422692065949421 3778346686283509524731033)
          ·
            refine ⟨2833760014712632143548275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778346686283509524731033 2833760014712632143548275)
            ·
              refine ⟨4250640022068948215322413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833760014712632143548275 4250640022068948215322413)
              ·
                refine ⟨1593990008275855580745905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250640022068948215322413 1593990008275855580745905)
                ·
                  refine ⟨1195492506206891685559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593990008275855580745905 1195492506206891685559429)
                  ·
                    refine ⟨224154844913792191042393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195492506206891685559429 224154844913792191042393)
                    ·
                      rfl

theorem cell22_654810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_654810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654810 prefixEnd_654810 := by exact prefixLift 654810
  have htrace : WordTrace (prefixWord ++ tailWord_654810) baseStart_654810 baseEnd_654810 := by
    simpa [prefixWord, tailWord_654810, baseEnd_654810] using wordTrace_append hprefix tailTrace_654810
  have hstable : (prefixWord ++ tailWord_654810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654810).length < 2 ^ (prefixWord ++ tailWord_654810).sum := by decide
  have hdescent : baseEnd_654810 < baseStart_654810 := by decide
  rcases family_descends (prefixWord ++ tailWord_654810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654853 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 9]
def baseStart_654853 : Nat := 118140960795 + 654853 * 2 ^ 59
def prefixEnd_654853 : Nat := 4983230072969 + 3 ^ 40 * 654853 * 2
def baseEnd_654853 : Nat := 74723188230851470739087

theorem tailTrace_654853 : CollatzResearch.WordTrace tailWord_654853 prefixEnd_654853 74723188230851470739087 := by
  unfold tailWord_654853
  simp only [CollatzResearch.WordTrace]
  refine ⟨23884451096586895833473213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15922967397724597222315475 23884451096586895833473213)
  ·
    refine ⟨8956669161220085937552455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23884451096586895833473213 8956669161220085937552455)
    ·
      refine ⟨13435003741830128906328683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8956669161220085937552455 13435003741830128906328683)
      ·
        refine ⟨20152505612745193359493025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13435003741830128906328683 20152505612745193359493025)
        ·
          refine ⟨15114379209558895019619769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20152505612745193359493025 15114379209558895019619769)
          ·
            refine ⟨11335784407169171264714827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15114379209558895019619769 11335784407169171264714827)
            ·
              refine ⟨17003676610753756897072241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11335784407169171264714827 17003676610753756897072241)
              ·
                refine ⟨12752757458065317672804181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17003676610753756897072241 12752757458065317672804181)
                ·
                  refine ⟨74723188230851470739087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12752757458065317672804181 74723188230851470739087)
                  ·
                    rfl

theorem cell22_654853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_654853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654853 prefixEnd_654853 := by exact prefixLift 654853
  have htrace : WordTrace (prefixWord ++ tailWord_654853) baseStart_654853 baseEnd_654853 := by
    simpa [prefixWord, tailWord_654853, baseEnd_654853] using wordTrace_append hprefix tailTrace_654853
  have hstable : (prefixWord ++ tailWord_654853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654853).length < 2 ^ (prefixWord ++ tailWord_654853).sum := by decide
  have hdescent : baseEnd_654853 < baseStart_654853 := by decide
  rcases family_descends (prefixWord ++ tailWord_654853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654917 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_654917 : Nat := 118140960795 + 654917 * 2 ^ 59
def prefixEnd_654917 : Nat := 4983230072969 + 3 ^ 40 * 654917 * 2
def baseEnd_654917 : Nat := 224191473200479578617065

theorem tailTrace_654917 : CollatzResearch.WordTrace tailWord_654917 prefixEnd_654917 224191473200479578617065 := by
  unfold tailWord_654917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23886785368355034763803005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15924523578903356509202003 23886785368355034763803005)
  ·
    refine ⟨8957544513133138036426127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23886785368355034763803005 8957544513133138036426127)
    ·
      refine ⟨13436316769699707054639191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8957544513133138036426127 13436316769699707054639191)
      ·
        refine ⟨20154475154549560581958787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436316769699707054639191 20154475154549560581958787)
        ·
          refine ⟨30231712731824340872938181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20154475154549560581958787 30231712731824340872938181)
          ·
            refine ⟨5668446137217063913675909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30231712731824340872938181 5668446137217063913675909)
            ·
              refine ⟨1062833650728199483814233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5668446137217063913675909 1062833650728199483814233)
              ·
                refine ⟨797125238046149612860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062833650728199483814233 797125238046149612860675)
                ·
                  refine ⟨1195687857069224419291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797125238046149612860675 1195687857069224419291013)
                  ·
                    refine ⟨224191473200479578617065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1195687857069224419291013 224191473200479578617065)
                    ·
                      rfl

theorem cell22_654917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_654917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654917 prefixEnd_654917 := by exact prefixLift 654917
  have htrace : WordTrace (prefixWord ++ tailWord_654917) baseStart_654917 baseEnd_654917 := by
    simpa [prefixWord, tailWord_654917, baseEnd_654917] using wordTrace_append hprefix tailTrace_654917
  have hstable : (prefixWord ++ tailWord_654917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654917).length < 2 ^ (prefixWord ++ tailWord_654917).sum := by decide
  have hdescent : baseEnd_654917 < baseStart_654917 := by decide
  rcases family_descends (prefixWord ++ tailWord_654917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654925 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_654925 : Nat := 118140960795 + 654925 * 2 ^ 59
def prefixEnd_654925 : Nat := 4983230072969 + 3 ^ 40 * 654925 * 2
def baseEnd_654925 : Nat := 224194211763970224417041

theorem tailTrace_654925 : CollatzResearch.WordTrace tailWord_654925 prefixEnd_654925 224194211763970224417041 := by
  unfold tailWord_654925
  simp only [CollatzResearch.WordTrace]
  refine ⟨23887077152326052130094229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15924718101550701420062819 23887077152326052130094229)
  ·
    refine ⟨1119706741515283693598167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23887077152326052130094229 1119706741515283693598167)
    ·
      refine ⟨1679560112272925540397251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119706741515283693598167 1679560112272925540397251)
      ·
        refine ⟨2519340168409388310595877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679560112272925540397251 2519340168409388310595877)
        ·
          refine ⟨472376281576760308236727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2519340168409388310595877 472376281576760308236727)
          ·
            refine ⟨708564422365140462355091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472376281576760308236727 708564422365140462355091)
            ·
              refine ⟨1062846633547710693532637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708564422365140462355091 1062846633547710693532637)
              ·
                refine ⟨398567487580391510074739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062846633547710693532637 398567487580391510074739)
                ·
                  refine ⟨597851231370587265112109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398567487580391510074739 597851231370587265112109)
                  ·
                    refine ⟨224194211763970224417041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597851231370587265112109 224194211763970224417041)
                    ·
                      rfl

theorem cell22_654925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_654925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654925 prefixEnd_654925 := by exact prefixLift 654925
  have htrace : WordTrace (prefixWord ++ tailWord_654925) baseStart_654925 baseEnd_654925 := by
    simpa [prefixWord, tailWord_654925, baseEnd_654925] using wordTrace_append hprefix tailTrace_654925
  have hstable : (prefixWord ++ tailWord_654925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654925).length < 2 ^ (prefixWord ++ tailWord_654925).sum := by decide
  have hdescent : baseEnd_654925 < baseStart_654925 := by decide
  rcases family_descends (prefixWord ++ tailWord_654925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654947 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 4, 3]
def baseStart_654947 : Nat := 118140960795 + 654947 * 2 ^ 59
def prefixEnd_654947 : Nat := 4983230072969 + 3 ^ 40 * 654947 * 2
def baseEnd_654947 : Nat := 224201742813569500366973

theorem tailTrace_654947 : CollatzResearch.WordTrace tailWord_654947 prefixEnd_654947 224201742813569500366973 := by
  unfold tailWord_654947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23887879558246349887395095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15925253038830899924930063 23887879558246349887395095)
  ·
    refine ⟨35831819337369524831092643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23887879558246349887395095 35831819337369524831092643)
    ·
      refine ⟨53747729006054287246638965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35831819337369524831092643 53747729006054287246638965)
      ·
        refine ⟨5038849594317589429372403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53747729006054287246638965 5038849594317589429372403)
        ·
          refine ⟨7558274391476384144058605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038849594317589429372403 7558274391476384144058605)
          ·
            refine ⟨2834352896803644054021977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7558274391476384144058605 2834352896803644054021977)
            ·
              refine ⟨2125764672602733040516483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834352896803644054021977 2125764672602733040516483)
              ·
                refine ⟨3188647008904099560774725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125764672602733040516483 3188647008904099560774725)
                ·
                  refine ⟨597871314169518667645261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3188647008904099560774725 597871314169518667645261)
                  ·
                    refine ⟨224201742813569500366973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597871314169518667645261 224201742813569500366973)
                    ·
                      rfl

theorem cell22_654947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].length) (baseStart_654947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654947 prefixEnd_654947 := by exact prefixLift 654947
  have htrace : WordTrace (prefixWord ++ tailWord_654947) baseStart_654947 baseEnd_654947 := by
    simpa [prefixWord, tailWord_654947, baseEnd_654947] using wordTrace_append hprefix tailTrace_654947
  have hstable : (prefixWord ++ tailWord_654947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654947).length < 2 ^ (prefixWord ++ tailWord_654947).sum := by decide
  have hdescent : baseEnd_654947 < baseStart_654947 := by decide
  rcases family_descends (prefixWord ++ tailWord_654947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654960 : List Nat := [2, 1, 1, 1, 6, 1, 1, 9]
def baseStart_654960 : Nat := 118140960795 + 654960 * 2 ^ 59
def prefixEnd_654960 : Nat := 4983230072969 + 3 ^ 40 * 654960 * 2
def baseEnd_654960 : Nat := 24911799219915755532437

theorem tailTrace_654960 : CollatzResearch.WordTrace tailWord_654960 prefixEnd_654960 24911799219915755532437 := by
  unfold tailWord_654960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944176853599626553809167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15925569138132835405078889 11944176853599626553809167)
  ·
    refine ⟨17916265280399439830713751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11944176853599626553809167 17916265280399439830713751)
    ·
      refine ⟨26874397920599159746070627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17916265280399439830713751 26874397920599159746070627)
      ·
        refine ⟨40311596880898739619105941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26874397920599159746070627 40311596880898739619105941)
        ·
          refine ⟨1889606103792128419645591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40311596880898739619105941 1889606103792128419645591)
          ·
            refine ⟨2834409155688192629468387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889606103792128419645591 2834409155688192629468387)
            ·
              refine ⟨4251613733532288944202581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834409155688192629468387 4251613733532288944202581)
              ·
                refine ⟨24911799219915755532437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4251613733532288944202581 24911799219915755532437)
                ·
                  rfl

theorem cell22_654960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_654960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_654960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_654960 prefixEnd_654960 := by exact prefixLift 654960
  have htrace : WordTrace (prefixWord ++ tailWord_654960) baseStart_654960 baseEnd_654960 := by
    simpa [prefixWord, tailWord_654960, baseEnd_654960] using wordTrace_append hprefix tailTrace_654960
  have hstable : (prefixWord ++ tailWord_654960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654960).length < 2 ^ (prefixWord ++ tailWord_654960).sum := by decide
  have hdescent : baseEnd_654960 < baseStart_654960 := by decide
  rcases family_descends (prefixWord ++ tailWord_654960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655114 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_655114 : Nat := 118140960795 + 655114 * 2 ^ 59
def prefixEnd_655114 : Nat := 4983230072969 + 3 ^ 40 * 655114 * 2
def baseEnd_655114 : Nat := 224258910326436731441461

theorem tailTrace_655114 : CollatzResearch.WordTrace tailWord_655114 prefixEnd_655114 224258910326436731441461 := by
  unfold tailWord_655114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973492637160334352181099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15929313699094224939149597 5973492637160334352181099)
  ·
    refine ⟨8960238955740501528271649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973492637160334352181099 8960238955740501528271649)
    ·
      refine ⟨6720179216805376146203737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8960238955740501528271649 6720179216805376146203737)
      ·
        refine ⟨5040134412604032109652803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6720179216805376146203737 5040134412604032109652803)
        ·
          refine ⟨7560201618906048164479205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040134412604032109652803 7560201618906048164479205)
          ·
            refine ⟨1417537803544884030839851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7560201618906048164479205 1417537803544884030839851)
            ·
              refine ⟨2126306705317326046259777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417537803544884030839851 2126306705317326046259777)
              ·
                refine ⟨1594730028987994534694833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126306705317326046259777 1594730028987994534694833)
                ·
                  refine ⟨1196047521740995901021125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1594730028987994534694833 1196047521740995901021125)
                  ·
                    refine ⟨224258910326436731441461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196047521740995901021125 224258910326436731441461)
                    ·
                      rfl

theorem cell22_655114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_655114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655114 prefixEnd_655114 := by exact prefixLift 655114
  have htrace : WordTrace (prefixWord ++ tailWord_655114) baseStart_655114 baseEnd_655114 := by
    simpa [prefixWord, tailWord_655114, baseEnd_655114] using wordTrace_append hprefix tailTrace_655114
  have hstable : (prefixWord ++ tailWord_655114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655114).length < 2 ^ (prefixWord ++ tailWord_655114).sum := by decide
  have hdescent : baseEnd_655114 < baseStart_655114 := by decide
  rcases family_descends (prefixWord ++ tailWord_655114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655189 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_655189 : Nat := 118140960795 + 655189 * 2 ^ 59
def prefixEnd_655189 : Nat := 4983230072969 + 3 ^ 40 * 655189 * 2
def baseEnd_655189 : Nat := 224284584359161535816231

theorem tailTrace_655189 : CollatzResearch.WordTrace tailWord_655189 prefixEnd_655189 224284584359161535816231 := by
  unfold tailWord_655189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23896706023369625217704621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15931137348913083478469747 23896706023369625217704621)
  ·
    refine ⟨8961264758763609456639233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23896706023369625217704621 8961264758763609456639233)
    ·
      refine ⟨6720948569072707092479425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8961264758763609456639233 6720948569072707092479425)
      ·
        refine ⟨5040711426804530319359569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6720948569072707092479425 5040711426804530319359569)
        ·
          refine ⟨3780533570103397739519677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5040711426804530319359569 3780533570103397739519677)
          ·
            refine ⟨1417700088788774152319879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3780533570103397739519677 1417700088788774152319879)
            ·
              refine ⟨2126550133183161228479819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417700088788774152319879 2126550133183161228479819)
              ·
                refine ⟨3189825199774741842719729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126550133183161228479819 3189825199774741842719729)
                ·
                  refine ⟨2392368899831056382039797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3189825199774741842719729 2392368899831056382039797)
                  ·
                    refine ⟨224284584359161535816231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2392368899831056382039797 224284584359161535816231)
                    ·
                      rfl

theorem cell22_655189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_655189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655189 prefixEnd_655189 := by exact prefixLift 655189
  have htrace : WordTrace (prefixWord ++ tailWord_655189) baseStart_655189 baseEnd_655189 := by
    simpa [prefixWord, tailWord_655189, baseEnd_655189] using wordTrace_append hprefix tailTrace_655189
  have hstable : (prefixWord ++ tailWord_655189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655189).length < 2 ^ (prefixWord ++ tailWord_655189).sum := by decide
  have hdescent : baseEnd_655189 < baseStart_655189 := by decide
  rcases family_descends (prefixWord ++ tailWord_655189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
