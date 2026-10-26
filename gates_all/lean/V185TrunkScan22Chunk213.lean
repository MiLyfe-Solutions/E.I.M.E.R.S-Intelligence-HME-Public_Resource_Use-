import V185TrunkScan22Chunk212

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1899710 : List Nat := [4, 2, 1, 1, 3, 11]
def baseStart_1899710 : Nat := 118140960795 + 1899710 * 2 ^ 59
def prefixEnd_1899710 : Nat := 4983230072969 + 3 ^ 40 * 1899710 * 2
def baseEnd_1899710 : Nat := 8028513038295206663279

theorem tailTrace_1899710 : CollatzResearch.WordTrace tailWord_1899710 prefixEnd_1899710 8028513038295206663279 := by
  unfold tailWord_1899710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8661014493460323685344073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46192077298455059655168389 8661014493460323685344073)
  ·
    refine ⟨6495760870095242764008055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8661014493460323685344073 6495760870095242764008055)
    ·
      refine ⟨9743641305142864146012083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495760870095242764008055 9743641305142864146012083)
      ·
        refine ⟨14615461957714296219018125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9743641305142864146012083 14615461957714296219018125)
        ·
          refine ⟨5480798234142861082131797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14615461957714296219018125 5480798234142861082131797)
          ·
            refine ⟨8028513038295206663279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5480798234142861082131797 8028513038295206663279)
            ·
              rfl

theorem cell22_1899710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 11].length) (baseStart_1899710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899710 prefixEnd_1899710 := by exact prefixLift 1899710
  have htrace : WordTrace (prefixWord ++ tailWord_1899710) baseStart_1899710 baseEnd_1899710 := by
    simpa [prefixWord, tailWord_1899710, baseEnd_1899710] using wordTrace_append hprefix tailTrace_1899710
  have hstable : (prefixWord ++ tailWord_1899710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899710).length < 2 ^ (prefixWord ++ tailWord_1899710).sum := by decide
  have hdescent : baseEnd_1899710 < baseStart_1899710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899770 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1899770 : Nat := 118140960795 + 1899770 * 2 ^ 59
def prefixEnd_1899770 : Nat := 4983230072969 + 3 ^ 40 * 1899770 * 2
def baseEnd_1899770 : Nat := 650330095328091583225415

theorem tailTrace_1899770 : CollatzResearch.WordTrace tailWord_1899770 prefixEnd_1899770 650330095328091583225415 := by
  unfold tailWord_1899770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322576081866304932484191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46193536218310146486624509 17322576081866304932484191)
  ·
    refine ⟨25983864122799457398726287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17322576081866304932484191 25983864122799457398726287)
    ·
      refine ⟨38975796184199186098089431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25983864122799457398726287 38975796184199186098089431)
      ·
        refine ⟨58463694276298779147134147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38975796184199186098089431 58463694276298779147134147)
        ·
          refine ⟨87695541414448168720701221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58463694276298779147134147 87695541414448168720701221)
          ·
            refine ⟨16442914015209031635131479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87695541414448168720701221 16442914015209031635131479)
            ·
              refine ⟨24664371022813547452697219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442914015209031635131479 24664371022813547452697219)
              ·
                refine ⟨36996556534220321179045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24664371022813547452697219 36996556534220321179045829)
                ·
                  refine ⟨6936854350166310221071093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36996556534220321179045829 6936854350166310221071093)
                  ·
                    refine ⟨650330095328091583225415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6936854350166310221071093 650330095328091583225415)
                    ·
                      rfl

theorem cell22_1899770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1899770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899770 prefixEnd_1899770 := by exact prefixLift 1899770
  have htrace : WordTrace (prefixWord ++ tailWord_1899770) baseStart_1899770 baseEnd_1899770 := by
    simpa [prefixWord, tailWord_1899770, baseEnd_1899770] using wordTrace_append hprefix tailTrace_1899770
  have hstable : (prefixWord ++ tailWord_1899770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899770).length < 2 ^ (prefixWord ++ tailWord_1899770).sum := by decide
  have hdescent : baseEnd_1899770 < baseStart_1899770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899772 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_1899772 : Nat := 118140960795 + 1899772 * 2 ^ 59
def prefixEnd_1899772 : Nat := 4983230072969 + 3 ^ 40 * 1899772 * 2
def baseEnd_1899772 : Nat := 216776926656321414891803

theorem tailTrace_1899772 : CollatzResearch.WordTrace tailWord_1899772 prefixEnd_1899772 216776926656321414891803 := by
  unfold tailWord_1899772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645188636728987035754785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46193584848971982714339713 34645188636728987035754785)
  ·
    refine ⟨25983891477546740276816089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34645188636728987035754785 25983891477546740276816089)
    ·
      refine ⟨19487918608160055207612067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25983891477546740276816089 19487918608160055207612067)
      ·
        refine ⟨29231877912240082811418101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487918608160055207612067 29231877912240082811418101)
        ·
          refine ⟨2740488554272507763570447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29231877912240082811418101 2740488554272507763570447)
          ·
            refine ⟨4110732831408761645355671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740488554272507763570447 4110732831408761645355671)
            ·
              refine ⟨6166099247113142468033507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110732831408761645355671 6166099247113142468033507)
              ·
                refine ⟨9249148870669713702050261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166099247113142468033507 9249148870669713702050261)
                ·
                  refine ⟨216776926656321414891803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9249148870669713702050261 216776926656321414891803)
                  ·
                    rfl

theorem cell22_1899772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_1899772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899772 prefixEnd_1899772 := by exact prefixLift 1899772
  have htrace : WordTrace (prefixWord ++ tailWord_1899772) baseStart_1899772 baseEnd_1899772 := by
    simpa [prefixWord, tailWord_1899772, baseEnd_1899772] using wordTrace_append hprefix tailTrace_1899772
  have hstable : (prefixWord ++ tailWord_1899772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899772).length < 2 ^ (prefixWord ++ tailWord_1899772).sum := by decide
  have hdescent : baseEnd_1899772 < baseStart_1899772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899810 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1899810 : Nat := 118140960795 + 1899810 * 2 ^ 59
def prefixEnd_1899810 : Nat := 4983230072969 + 3 ^ 40 * 1899810 * 2
def baseEnd_1899810 : Nat := 650343788145544812225293

theorem tailTrace_1899810 : CollatzResearch.WordTrace tailWord_1899810 prefixEnd_1899810 650343788145544812225293 := by
  unfold tailWord_1899810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322940811830076640348221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46194508831546871040928589 17322940811830076640348221)
  ·
    refine ⟨6496102804436278740130583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17322940811830076640348221 6496102804436278740130583)
    ·
      refine ⟨9744154206654418110195875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496102804436278740130583 9744154206654418110195875)
      ·
        refine ⟨14616231309981627165293813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9744154206654418110195875 14616231309981627165293813)
        ·
          refine ⟨1370271685310777546746295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14616231309981627165293813 1370271685310777546746295)
          ·
            refine ⟨2055407527966166320119443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370271685310777546746295 2055407527966166320119443)
            ·
              refine ⟨3083111291949249480179165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055407527966166320119443 3083111291949249480179165)
              ·
                refine ⟨1156166734480968555067187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083111291949249480179165 1156166734480968555067187)
                ·
                  refine ⟨1734250101721452832600781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156166734480968555067187 1734250101721452832600781)
                  ·
                    refine ⟨650343788145544812225293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734250101721452832600781 650343788145544812225293)
                    ·
                      rfl

theorem cell22_1899810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1899810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899810 prefixEnd_1899810 := by exact prefixLift 1899810
  have htrace : WordTrace (prefixWord ++ tailWord_1899810) baseStart_1899810 baseEnd_1899810 := by
    simpa [prefixWord, tailWord_1899810, baseEnd_1899810] using wordTrace_append hprefix tailTrace_1899810
  have hstable : (prefixWord ++ tailWord_1899810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899810).length < 2 ^ (prefixWord ++ tailWord_1899810).sum := by decide
  have hdescent : baseEnd_1899810 < baseStart_1899810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899999 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_1899999 : Nat := 118140960795 + 1899999 * 2 ^ 59
def prefixEnd_1899999 : Nat := 4983230072969 + 3 ^ 40 * 1899999 * 2
def baseEnd_1899999 : Nat := 650408486708011319249713

theorem tailTrace_1899999 : CollatzResearch.WordTrace tailWord_1899999 prefixEnd_1899999 650408486708011319249713 := by
  unfold tailWord_1899999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298656643635591840023051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199104429090394560015367 69298656643635591840023051)
  ·
    refine ⟨103947984965453387760034577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69298656643635591840023051 103947984965453387760034577)
    ·
      refine ⟨77960988724090040820025933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103947984965453387760034577 77960988724090040820025933)
      ·
        refine ⟨29235370771533765307509725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77960988724090040820025933 29235370771533765307509725)
        ·
          refine ⟨10963264039325161990316147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29235370771533765307509725 10963264039325161990316147)
          ·
            refine ⟨16444896058987742985474221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963264039325161990316147 16444896058987742985474221)
            ·
              refine ⟨6166836022120403619552833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16444896058987742985474221 6166836022120403619552833)
              ·
                refine ⟨4625127016590302714664625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166836022120403619552833 4625127016590302714664625)
                ·
                  refine ⟨3468845262442727035998469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625127016590302714664625 3468845262442727035998469)
                  ·
                    refine ⟨650408486708011319249713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468845262442727035998469 650408486708011319249713)
                    ·
                      rfl

theorem cell22_1899999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_1899999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899999 prefixEnd_1899999 := by exact prefixLift 1899999
  have htrace : WordTrace (prefixWord ++ tailWord_1899999) baseStart_1899999 baseEnd_1899999 := by
    simpa [prefixWord, tailWord_1899999, baseEnd_1899999] using wordTrace_append hprefix tailTrace_1899999
  have hstable : (prefixWord ++ tailWord_1899999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899999).length < 2 ^ (prefixWord ++ tailWord_1899999).sum := by decide
  have hdescent : baseEnd_1899999 < baseStart_1899999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900003 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 4]
def baseStart_1900003 : Nat := 118140960795 + 1900003 * 2 ^ 59
def prefixEnd_1900003 : Nat := 4983230072969 + 3 ^ 40 * 1900003 * 2
def baseEnd_1900003 : Nat := 216803285329918880716567

theorem tailTrace_1900003 : CollatzResearch.WordTrace tailWord_1900003 prefixEnd_1900003 216803285329918880716567 := by
  unfold tailWord_1900003
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298802535621100523168663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199201690414067015445775 69298802535621100523168663)
  ·
    refine ⟨103948203803431650784752995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69298802535621100523168663 103948203803431650784752995)
    ·
      refine ⟨155922305705147476177129493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103948203803431650784752995 155922305705147476177129493)
      ·
        refine ⟨7308858079928787945802945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155922305705147476177129493 7308858079928787945802945)
        ·
          refine ⟨5481643559946590959352209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7308858079928787945802945 5481643559946590959352209)
          ·
            refine ⟨4111232669959943219514157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481643559946590959352209 4111232669959943219514157)
            ·
              refine ⟨1541712251234978707317809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4111232669959943219514157 1541712251234978707317809)
              ·
                refine ⟨1156284188426234030488357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541712251234978707317809 1156284188426234030488357)
                ·
                  refine ⟨216803285329918880716567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156284188426234030488357 216803285329918880716567)
                  ·
                    rfl

theorem cell22_1900003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 4].length) (baseStart_1900003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900003 prefixEnd_1900003 := by exact prefixLift 1900003
  have htrace : WordTrace (prefixWord ++ tailWord_1900003) baseStart_1900003 baseEnd_1900003 := by
    simpa [prefixWord, tailWord_1900003, baseEnd_1900003] using wordTrace_append hprefix tailTrace_1900003
  have hstable : (prefixWord ++ tailWord_1900003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900003).length < 2 ^ (prefixWord ++ tailWord_1900003).sum := by decide
  have hdescent : baseEnd_1900003 < baseStart_1900003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1900012 : Nat := 118140960795 + 1900012 * 2 ^ 59
def prefixEnd_1900012 : Nat := 4983230072969 + 3 ^ 40 * 1900012 * 2
def baseEnd_1900012 : Nat := 650412936873683618674673

theorem tailTrace_1900012 : CollatzResearch.WordTrace tailWord_1900012 prefixEnd_1900012 650412936873683618674673 := by
  unfold tailWord_1900012
  simp only [CollatzResearch.WordTrace]
  refine ⟨34649565396294247530123145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46199420528392330040164193 34649565396294247530123145)
  ·
    refine ⟨25987174047220685647592359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34649565396294247530123145 25987174047220685647592359)
    ·
      refine ⟨38980761070831028471388539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25987174047220685647592359 38980761070831028471388539)
      ·
        refine ⟨58471141606246542707082809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38980761070831028471388539 58471141606246542707082809)
        ·
          refine ⟨43853356204684907030312107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58471141606246542707082809 43853356204684907030312107)
          ·
            refine ⟨65780034307027360545468161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43853356204684907030312107 65780034307027360545468161)
            ·
              refine ⟨49335025730270520409101121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65780034307027360545468161 49335025730270520409101121)
              ·
                refine ⟨37001269297702890306825841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49335025730270520409101121 37001269297702890306825841)
                ·
                  refine ⟨27750951973277167730119381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37001269297702890306825841 27750951973277167730119381)
                  ·
                    refine ⟨650412936873683618674673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27750951973277167730119381 650412936873683618674673)
                    ·
                      rfl

theorem cell22_1900012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1900012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900012 prefixEnd_1900012 := by exact prefixLift 1900012
  have htrace : WordTrace (prefixWord ++ tailWord_1900012) baseStart_1900012 baseEnd_1900012 := by
    simpa [prefixWord, tailWord_1900012, baseEnd_1900012] using wordTrace_append hprefix tailTrace_1900012
  have hstable : (prefixWord ++ tailWord_1900012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900012).length < 2 ^ (prefixWord ++ tailWord_1900012).sum := by decide
  have hdescent : baseEnd_1900012 < baseStart_1900012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900014 : List Nat := [4, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1900014 : Nat := 118140960795 + 1900014 * 2 ^ 59
def prefixEnd_1900014 : Nat := 4983230072969 + 3 ^ 40 * 1900014 * 2
def baseEnd_1900014 : Nat := 72268180168284031124963

theorem tailTrace_1900014 : CollatzResearch.WordTrace tailWord_1900014 prefixEnd_1900014 72268180168284031124963 := by
  unfold tailWord_1900014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662400467322656175227387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46199469159054166267879397 8662400467322656175227387)
  ·
    refine ⟨12993600700983984262841081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8662400467322656175227387 12993600700983984262841081)
    ·
      refine ⟨9745200525737988197130811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12993600700983984262841081 9745200525737988197130811)
      ·
        refine ⟨14617800788606982295696217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745200525737988197130811 14617800788606982295696217)
        ·
          refine ⟨10963350591455236721772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14617800788606982295696217 10963350591455236721772163)
          ·
            refine ⟨16445025887182855082658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963350591455236721772163 16445025887182855082658245)
            ·
              refine ⟨3083442353846785327998421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16445025887182855082658245 3083442353846785327998421)
              ·
                refine ⟨72268180168284031124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3083442353846785327998421 72268180168284031124963)
                ·
                  rfl

theorem cell22_1900014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1900014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900014 prefixEnd_1900014 := by exact prefixLift 1900014
  have htrace : WordTrace (prefixWord ++ tailWord_1900014) baseStart_1900014 baseEnd_1900014 := by
    simpa [prefixWord, tailWord_1900014, baseEnd_1900014] using wordTrace_append hprefix tailTrace_1900014
  have hstable : (prefixWord ++ tailWord_1900014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900014).length < 2 ^ (prefixWord ++ tailWord_1900014).sum := by decide
  have hdescent : baseEnd_1900014 < baseStart_1900014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900018 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1900018 : Nat := 118140960795 + 1900018 * 2 ^ 59
def prefixEnd_1900018 : Nat := 4983230072969 + 3 ^ 40 * 1900018 * 2
def baseEnd_1900018 : Nat := 650414990796301603024655

theorem tailTrace_1900018 : CollatzResearch.WordTrace tailWord_1900018 prefixEnd_1900018 650414990796301603024655 := by
  unfold tailWord_1900018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17324837407641689521241177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46199566420377838723309805 17324837407641689521241177)
  ·
    refine ⟨12993628055731267140930883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17324837407641689521241177 12993628055731267140930883)
    ·
      refine ⟨19490442083596900711396325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993628055731267140930883 19490442083596900711396325)
      ·
        refine ⟨3654457890674418883386811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19490442083596900711396325 3654457890674418883386811)
        ·
          refine ⟨5481686836011628325080217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654457890674418883386811 5481686836011628325080217)
          ·
            refine ⟨4111265127008721243810163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481686836011628325080217 4111265127008721243810163)
            ·
              refine ⟨6166897690513081865715245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111265127008721243810163 6166897690513081865715245)
              ·
                refine ⟨2312586633942405699643217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6166897690513081865715245 2312586633942405699643217)
                ·
                  refine ⟨1734439975456804274732413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312586633942405699643217 1734439975456804274732413)
                  ·
                    refine ⟨650414990796301603024655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734439975456804274732413 650414990796301603024655)
                    ·
                      rfl

theorem cell22_1900018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1900018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900018 prefixEnd_1900018 := by exact prefixLift 1900018
  have htrace : WordTrace (prefixWord ++ tailWord_1900018) baseStart_1900018 baseEnd_1900018 := by
    simpa [prefixWord, tailWord_1900018, baseEnd_1900018] using wordTrace_append hprefix tailTrace_1900018
  have hstable : (prefixWord ++ tailWord_1900018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900018).length < 2 ^ (prefixWord ++ tailWord_1900018).sum := by decide
  have hdescent : baseEnd_1900018 < baseStart_1900018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900027 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_1900027 : Nat := 118140960795 + 1900027 * 2 ^ 59
def prefixEnd_1900027 : Nat := 4983230072969 + 3 ^ 40 * 1900027 * 2
def baseEnd_1900027 : Nat := 650418071680228579549627

theorem tailTrace_1900027 : CollatzResearch.WordTrace tailWord_1900027 prefixEnd_1900027 650418071680228579549627 := by
  unfold tailWord_1900027
  simp only [CollatzResearch.WordTrace]
  refine ⟨69299677887534152622042335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199785258356101748028223 69299677887534152622042335)
  ·
    refine ⟨103949516831301228933063503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69299677887534152622042335 103949516831301228933063503)
    ·
      refine ⟨155924275246951843399595255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103949516831301228933063503 155924275246951843399595255)
      ·
        refine ⟨233886412870427765099392883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155924275246951843399595255 233886412870427765099392883)
        ·
          refine ⟨350829619305641647649089325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233886412870427765099392883 350829619305641647649089325)
          ·
            refine ⟨131561107239615617868408497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350829619305641647649089325 131561107239615617868408497)
            ·
              refine ⟨98670830429711713401306373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131561107239615617868408497 98670830429711713401306373)
              ·
                refine ⟨18500780705570946262744945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98670830429711713401306373 18500780705570946262744945)
                ·
                  refine ⟨13875585529178209697058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18500780705570946262744945 13875585529178209697058709)
                  ·
                    refine ⟨650418071680228579549627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13875585529178209697058709 650418071680228579549627)
                    ·
                      rfl

theorem cell22_1900027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_1900027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900027 prefixEnd_1900027 := by exact prefixLift 1900027
  have htrace : WordTrace (prefixWord ++ tailWord_1900027) baseStart_1900027 baseEnd_1900027 := by
    simpa [prefixWord, tailWord_1900027, baseEnd_1900027] using wordTrace_append hprefix tailTrace_1900027
  have hstable : (prefixWord ++ tailWord_1900027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900027).length < 2 ^ (prefixWord ++ tailWord_1900027).sum := by decide
  have hdescent : baseEnd_1900027 < baseStart_1900027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900106 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1900106 : Nat := 118140960795 + 1900106 * 2 ^ 59
def prefixEnd_1900106 : Nat := 4983230072969 + 3 ^ 40 * 1900106 * 2
def baseEnd_1900106 : Nat := 650445114994698706824385

theorem tailTrace_1900106 : CollatzResearch.WordTrace tailWord_1900106 prefixEnd_1900106 650445114994698706824385 := by
  unfold tailWord_1900106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325639813561987278542043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46201706169498632742778781 17325639813561987278542043)
  ·
    refine ⟨25988459720342980917813065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325639813561987278542043 25988459720342980917813065)
    ·
      refine ⟨19491344790257235688359799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25988459720342980917813065 19491344790257235688359799)
      ·
        refine ⟨29237017185385853532539699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19491344790257235688359799 29237017185385853532539699)
        ·
          refine ⟨43855525778078780298809549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29237017185385853532539699 43855525778078780298809549)
          ·
            refine ⟨16445822166779542612053581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43855525778078780298809549 16445822166779542612053581)
            ·
              refine ⟨6167183312542328479520093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16445822166779542612053581 6167183312542328479520093)
              ·
                refine ⟨2312693742203373179820035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6167183312542328479520093 2312693742203373179820035)
                ·
                  refine ⟨3469040613305059769730053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312693742203373179820035 3469040613305059769730053)
                  ·
                    refine ⟨650445114994698706824385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469040613305059769730053 650445114994698706824385)
                    ·
                      rfl

theorem cell22_1900106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1900106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900106 prefixEnd_1900106 := by exact prefixLift 1900106
  have htrace : WordTrace (prefixWord ++ tailWord_1900106) baseStart_1900106 baseEnd_1900106 := by
    simpa [prefixWord, tailWord_1900106, baseEnd_1900106] using wordTrace_append hprefix tailTrace_1900106
  have hstable : (prefixWord ++ tailWord_1900106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900106).length < 2 ^ (prefixWord ++ tailWord_1900106).sum := by decide
  have hdescent : baseEnd_1900106 < baseStart_1900106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900228 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1900228 : Nat := 118140960795 + 1900228 * 2 ^ 59
def prefixEnd_1900228 : Nat := 4983230072969 + 3 ^ 40 * 1900228 * 2
def baseEnd_1900228 : Nat := 216828959362643685091337

theorem tailTrace_1900228 : CollatzResearch.WordTrace tailWord_1900228 prefixEnd_1900228 216828959362643685091337 := by
  unfold tailWord_1900228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653504479902981975054669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46204672639870642633406225 34653504479902981975054669)
  ·
    refine ⟨12995064179963618240645501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34653504479902981975054669 12995064179963618240645501)
    ·
      refine ⟨4873149067486356840242063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12995064179963618240645501 4873149067486356840242063)
      ·
        refine ⟨7309723601229535260363095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873149067486356840242063 7309723601229535260363095)
        ·
          refine ⟨10964585401844302890544643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309723601229535260363095 10964585401844302890544643)
          ·
            refine ⟨16446878102766454335816965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964585401844302890544643 16446878102766454335816965)
            ·
              refine ⟨3083789644268710187965681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16446878102766454335816965 3083789644268710187965681)
              ·
                refine ⟨2312842233201532640974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083789644268710187965681 2312842233201532640974261)
                ·
                  refine ⟨216828959362643685091337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2312842233201532640974261 216828959362643685091337)
                  ·
                    rfl

theorem cell22_1900228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1900228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900228 prefixEnd_1900228 := by exact prefixLift 1900228
  have htrace : WordTrace (prefixWord ++ tailWord_1900228) baseStart_1900228 baseEnd_1900228 := by
    simpa [prefixWord, tailWord_1900228, baseEnd_1900228] using wordTrace_append hprefix tailTrace_1900228
  have hstable : (prefixWord ++ tailWord_1900228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900228).length < 2 ^ (prefixWord ++ tailWord_1900228).sum := by decide
  have hdescent : baseEnd_1900228 < baseStart_1900228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900230 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1900230 : Nat := 118140960795 + 1900230 * 2 ^ 59
def prefixEnd_1900230 : Nat := 4983230072969 + 3 ^ 40 * 1900230 * 2
def baseEnd_1900230 : Nat := 650487562728803716724005

theorem tailTrace_1900230 : CollatzResearch.WordTrace tailWord_1900230 prefixEnd_1900230 650487562728803716724005 := by
  unfold tailWord_1900230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165846309556209946615067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46204721270532478861121429 2165846309556209946615067)
  ·
    refine ⟨3248769464334314919922601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2165846309556209946615067 3248769464334314919922601)
    ·
      refine ⟨2436577098250736189941951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3248769464334314919922601 2436577098250736189941951)
      ·
        refine ⟨3654865647376104284912927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436577098250736189941951 3654865647376104284912927)
        ·
          refine ⟨5482298471064156427369391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654865647376104284912927 5482298471064156427369391)
          ·
            refine ⟨8223447706596234641054087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482298471064156427369391 8223447706596234641054087)
            ·
              refine ⟨12335171559894351961581131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8223447706596234641054087 12335171559894351961581131)
              ·
                refine ⟨18502757339841527942371697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12335171559894351961581131 18502757339841527942371697)
                ·
                  refine ⟨13877068004881145956778773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18502757339841527942371697 13877068004881145956778773)
                  ·
                    refine ⟨650487562728803716724005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13877068004881145956778773 650487562728803716724005)
                    ·
                      rfl

theorem cell22_1900230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1900230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900230 prefixEnd_1900230 := by exact prefixLift 1900230
  have htrace : WordTrace (prefixWord ++ tailWord_1900230) baseStart_1900230 baseEnd_1900230 := by
    simpa [prefixWord, tailWord_1900230, baseEnd_1900230] using wordTrace_append hprefix tailTrace_1900230
  have hstable : (prefixWord ++ tailWord_1900230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900230).length < 2 ^ (prefixWord ++ tailWord_1900230).sum := by decide
  have hdescent : baseEnd_1900230 < baseStart_1900230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900239 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 10]
def baseStart_1900239 : Nat := 118140960795 + 1900239 * 2 ^ 59
def prefixEnd_1900239 : Nat := 4983230072969 + 3 ^ 40 * 1900239 * 2
def baseEnd_1900239 : Nat := 216830214537576897749659

theorem tailTrace_1900239 : CollatzResearch.WordTrace tailWord_1900239 prefixEnd_1900239 216830214537576897749659 := by
  unfold tailWord_1900239
  simp only [CollatzResearch.WordTrace]
  refine ⟨69307410162766112828759771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46204940108510741885839847 69307410162766112828759771)
  ·
    refine ⟨103961115244149169243139657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69307410162766112828759771 103961115244149169243139657)
    ·
      refine ⟨77970836433111876932354743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103961115244149169243139657 77970836433111876932354743)
      ·
        refine ⟨116956254649667815398532115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77970836433111876932354743 116956254649667815398532115)
        ·
          refine ⟨175434381974501723097798173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116956254649667815398532115 175434381974501723097798173)
          ·
            refine ⟨65787893240438146161674315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175434381974501723097798173 65787893240438146161674315)
            ·
              refine ⟨98681839860657219242511473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65787893240438146161674315 98681839860657219242511473)
              ·
                refine ⟨74011379895492914431883605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98681839860657219242511473 74011379895492914431883605)
                ·
                  refine ⟨216830214537576897749659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74011379895492914431883605 216830214537576897749659)
                  ·
                    rfl

theorem cell22_1900239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_1900239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900239 prefixEnd_1900239 := by exact prefixLift 1900239
  have htrace : WordTrace (prefixWord ++ tailWord_1900239) baseStart_1900239 baseEnd_1900239 := by
    simpa [prefixWord, tailWord_1900239, baseEnd_1900239] using wordTrace_append hprefix tailTrace_1900239
  have hstable : (prefixWord ++ tailWord_1900239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900239).length < 2 ^ (prefixWord ++ tailWord_1900239).sum := by decide
  have hdescent : baseEnd_1900239 < baseStart_1900239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900241 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1900241 : Nat := 118140960795 + 1900241 * 2 ^ 59
def prefixEnd_1900241 : Nat := 4983230072969 + 3 ^ 40 * 1900241 * 2
def baseEnd_1900241 : Nat := 650491328253603354698971

theorem tailTrace_1900241 : CollatzResearch.WordTrace tailWord_1900241 prefixEnd_1900241 650491328253603354698971 := by
  unfold tailWord_1900241
  simp only [CollatzResearch.WordTrace]
  refine ⟨69307483108758867170332577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46204988739172578113555051 69307483108758867170332577)
  ·
    refine ⟨51980612331569150377749433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69307483108758867170332577 51980612331569150377749433)
    ·
      refine ⟨38985459248676862783312075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51980612331569150377749433 38985459248676862783312075)
      ·
        refine ⟨58478188873015294174968113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38985459248676862783312075 58478188873015294174968113)
        ·
          refine ⟨43858641654761470631226085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58478188873015294174968113 43858641654761470631226085)
          ·
            refine ⟨8223495310267775743354891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43858641654761470631226085 8223495310267775743354891)
            ·
              refine ⟨12335242965401663615032337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8223495310267775743354891 12335242965401663615032337)
              ·
                refine ⟨9251432224051247711274253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12335242965401663615032337 9251432224051247711274253)
                ·
                  refine ⟨3469287084019217891727845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9251432224051247711274253 3469287084019217891727845)
                  ·
                    refine ⟨650491328253603354698971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469287084019217891727845 650491328253603354698971)
                    ·
                      rfl

theorem cell22_1900241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1900241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900241 prefixEnd_1900241 := by exact prefixLift 1900241
  have htrace : WordTrace (prefixWord ++ tailWord_1900241) baseStart_1900241 baseEnd_1900241 := by
    simpa [prefixWord, tailWord_1900241, baseEnd_1900241] using wordTrace_append hprefix tailTrace_1900241
  have hstable : (prefixWord ++ tailWord_1900241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900241).length < 2 ^ (prefixWord ++ tailWord_1900241).sum := by decide
  have hdescent : baseEnd_1900241 < baseStart_1900241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900271 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1900271 : Nat := 118140960795 + 1900271 * 2 ^ 59
def prefixEnd_1900271 : Nat := 4983230072969 + 3 ^ 40 * 1900271 * 2
def baseEnd_1900271 : Nat := 650501597866693276448879

theorem tailTrace_1900271 : CollatzResearch.WordTrace tailWord_1900271 prefixEnd_1900271 650501597866693276448879 := by
  unfold tailWord_1900271
  simp only [CollatzResearch.WordTrace]
  refine ⟨69308577298650182293924667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46205718199100121529283111 69308577298650182293924667)
  ·
    refine ⟨103962865947975273440887001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69308577298650182293924667 103962865947975273440887001)
    ·
      refine ⟨77972149460981455080665251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103962865947975273440887001 77972149460981455080665251)
      ·
        refine ⟨116958224191472182620997877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77972149460981455080665251 116958224191472182620997877)
        ·
          refine ⟨10964833517950517120718551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116958224191472182620997877 10964833517950517120718551)
          ·
            refine ⟨16447250276925775681077827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964833517950517120718551 16447250276925775681077827)
            ·
              refine ⟨24670875415388663521616741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447250276925775681077827 24670875415388663521616741)
              ·
                refine ⟨4625789140385374410303139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24670875415388663521616741 4625789140385374410303139)
                ·
                  refine ⟨6938683710578061615454709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625789140385374410303139 6938683710578061615454709)
                  ·
                    refine ⟨650501597866693276448879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6938683710578061615454709 650501597866693276448879)
                    ·
                      rfl

theorem cell22_1900271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1900271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900271 prefixEnd_1900271 := by exact prefixLift 1900271
  have htrace : WordTrace (prefixWord ++ tailWord_1900271) baseStart_1900271 baseEnd_1900271 := by
    simpa [prefixWord, tailWord_1900271, baseEnd_1900271] using wordTrace_append hprefix tailTrace_1900271
  have hstable : (prefixWord ++ tailWord_1900271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900271).length < 2 ^ (prefixWord ++ tailWord_1900271).sum := by decide
  have hdescent : baseEnd_1900271 < baseStart_1900271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900273 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 4]
def baseStart_1900273 : Nat := 118140960795 + 1900273 * 2 ^ 59
def prefixEnd_1900273 : Nat := 4983230072969 + 3 ^ 40 * 1900273 * 2
def baseEnd_1900273 : Nat := 216834094169188645966291

theorem tailTrace_1900273 : CollatzResearch.WordTrace tailWord_1900273 prefixEnd_1900273 216834094169188645966291 := by
  unfold tailWord_1900273
  simp only [CollatzResearch.WordTrace]
  refine ⟨69308650244642936635497473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46205766829761957756998315 69308650244642936635497473)
  ·
    refine ⟨51981487683482202476623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69308650244642936635497473 51981487683482202476623105)
    ·
      refine ⟨38986115762611651857467329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51981487683482202476623105 38986115762611651857467329)
      ·
        refine ⟨29239586821958738893100497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38986115762611651857467329 29239586821958738893100497)
        ·
          refine ⟨21929690116469054169825373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29239586821958738893100497 21929690116469054169825373)
          ·
            refine ⟨8223633793675895313684515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21929690116469054169825373 8223633793675895313684515)
            ·
              refine ⟨12335450690513842970526773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8223633793675895313684515 12335450690513842970526773)
              ·
                refine ⟨1156448502235672778486885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12335450690513842970526773 1156448502235672778486885)
                ·
                  refine ⟨216834094169188645966291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156448502235672778486885 216834094169188645966291)
                  ·
                    rfl

theorem cell22_1900273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_1900273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900273 prefixEnd_1900273 := by exact prefixLift 1900273
  have htrace : WordTrace (prefixWord ++ tailWord_1900273) baseStart_1900273 baseEnd_1900273 := by
    simpa [prefixWord, tailWord_1900273, baseEnd_1900273] using wordTrace_append hprefix tailTrace_1900273
  have hstable : (prefixWord ++ tailWord_1900273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900273).length < 2 ^ (prefixWord ++ tailWord_1900273).sum := by decide
  have hdescent : baseEnd_1900273 < baseStart_1900273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900290 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1900290 : Nat := 118140960795 + 1900290 * 2 ^ 59
def prefixEnd_1900290 : Nat := 4983230072969 + 3 ^ 40 * 1900290 * 2
def baseEnd_1900290 : Nat := 216836033984994520074607

theorem tailTrace_1900290 : CollatzResearch.WordTrace tailWord_1900290 prefixEnd_1900290 216836033984994520074607 := by
  unfold tailWord_1900290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17327317571395337134716581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46206180190387565692577549 17327317571395337134716581)
  ·
    refine ⟨3248872044636625712759359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17327317571395337134716581 3248872044636625712759359)
    ·
      refine ⟨4873308066954938569139039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248872044636625712759359 4873308066954938569139039)
      ·
        refine ⟨7309962100432407853708559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873308066954938569139039 7309962100432407853708559)
        ·
          refine ⟨10964943150648611780562839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309962100432407853708559 10964943150648611780562839)
          ·
            refine ⟨16447414725972917670844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964943150648611780562839 16447414725972917670844259)
            ·
              refine ⟨24671122088959376506266389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447414725972917670844259 24671122088959376506266389)
              ·
                refine ⟨1156458847919970773731237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24671122088959376506266389 1156458847919970773731237)
                ·
                  refine ⟨216836033984994520074607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156458847919970773731237 216836033984994520074607)
                  ·
                    rfl

theorem cell22_1900290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1900290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900290 prefixEnd_1900290 := by exact prefixLift 1900290
  have htrace : WordTrace (prefixWord ++ tailWord_1900290) baseStart_1900290 baseEnd_1900290 := by
    simpa [prefixWord, tailWord_1900290, baseEnd_1900290] using wordTrace_append hprefix tailTrace_1900290
  have hstable : (prefixWord ++ tailWord_1900290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900290).length < 2 ^ (prefixWord ++ tailWord_1900290).sum := by decide
  have hdescent : baseEnd_1900290 < baseStart_1900290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900316 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1900316 : Nat := 118140960795 + 1900316 * 2 ^ 59
def prefixEnd_1900316 : Nat := 4983230072969 + 3 ^ 40 * 1900316 * 2
def baseEnd_1900316 : Nat := 650517002286328159073741

theorem tailTrace_1900316 : CollatzResearch.WordTrace tailWord_1900316 prefixEnd_1900316 650517002286328159073741 := by
  unfold tailWord_1900316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34655109291743577489656401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46206812388991436652875201 34655109291743577489656401)
  ·
    refine ⟨25991331968807683117242301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34655109291743577489656401 25991331968807683117242301)
    ·
      refine ⟨9746749488302881168965863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25991331968807683117242301 9746749488302881168965863)
      ·
        refine ⟨14620124232454321753448795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746749488302881168965863 14620124232454321753448795)
        ·
          refine ⟨21930186348681482630173193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14620124232454321753448795 21930186348681482630173193)
          ·
            refine ⟨16447639761511111972629895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21930186348681482630173193 16447639761511111972629895)
            ·
              refine ⟨24671459642266667958944843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447639761511111972629895 24671459642266667958944843)
              ·
                refine ⟨37007189463400001938417265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24671459642266667958944843 37007189463400001938417265)
                ·
                  refine ⟨27755392097550001453812949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37007189463400001938417265 27755392097550001453812949)
                  ·
                    refine ⟨650517002286328159073741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27755392097550001453812949 650517002286328159073741)
                    ·
                      rfl

theorem cell22_1900316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1900316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900316 prefixEnd_1900316 := by exact prefixLift 1900316
  have htrace : WordTrace (prefixWord ++ tailWord_1900316) baseStart_1900316 baseEnd_1900316 := by
    simpa [prefixWord, tailWord_1900316, baseEnd_1900316] using wordTrace_append hprefix tailTrace_1900316
  have hstable : (prefixWord ++ tailWord_1900316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900316).length < 2 ^ (prefixWord ++ tailWord_1900316).sum := by decide
  have hdescent : baseEnd_1900316 < baseStart_1900316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900361 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_1900361 : Nat := 118140960795 + 1900361 * 2 ^ 59
def prefixEnd_1900361 : Nat := 4983230072969 + 3 ^ 40 * 1900361 * 2
def baseEnd_1900361 : Nat := 650532406705963041698603

theorem tailTrace_1900361 : CollatzResearch.WordTrace tailWord_1900361 prefixEnd_1900361 650532406705963041698603 := by
  unfold tailWord_1900361
  simp only [CollatzResearch.WordTrace]
  refine ⟨69311859868324127664700937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46207906578882751776467291 69311859868324127664700937)
  ·
    refine ⟨51983894901243095748525703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69311859868324127664700937 51983894901243095748525703)
    ·
      refine ⟨77975842351864643622788555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51983894901243095748525703 77975842351864643622788555)
      ·
        refine ⟨116963763527796965434182833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77975842351864643622788555 116963763527796965434182833)
        ·
          refine ⟨87722822645847724075637125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116963763527796965434182833 87722822645847724075637125)
          ·
            refine ⟨16448029246096448264181961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87722822645847724075637125 16448029246096448264181961)
            ·
              refine ⟨12336021934572336198136471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16448029246096448264181961 12336021934572336198136471)
              ·
                refine ⟨18504032901858504297204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336021934572336198136471 18504032901858504297204707)
                ·
                  refine ⟨27756049352787756445807061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504032901858504297204707 27756049352787756445807061)
                  ·
                    refine ⟨650532406705963041698603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27756049352787756445807061 650532406705963041698603)
                    ·
                      rfl

theorem cell22_1900361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_1900361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900361 prefixEnd_1900361 := by exact prefixLift 1900361
  have htrace : WordTrace (prefixWord ++ tailWord_1900361) baseStart_1900361 baseEnd_1900361 := by
    simpa [prefixWord, tailWord_1900361, baseEnd_1900361] using wordTrace_append hprefix tailTrace_1900361
  have hstable : (prefixWord ++ tailWord_1900361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900361).length < 2 ^ (prefixWord ++ tailWord_1900361).sum := by decide
  have hdescent : baseEnd_1900361 < baseStart_1900361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900393 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1900393 : Nat := 118140960795 + 1900393 * 2 ^ 59
def prefixEnd_1900393 : Nat := 4983230072969 + 3 ^ 40 * 1900393 * 2
def baseEnd_1900393 : Nat := 650543360959925624898505

theorem tailTrace_1900393 : CollatzResearch.WordTrace tailWord_1900393 prefixEnd_1900393 650543360959925624898505 := by
  unfold tailWord_1900393
  simp only [CollatzResearch.WordTrace]
  refine ⟨69313027004208197129865833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46208684669472131419910555 69313027004208197129865833)
  ·
    refine ⟨51984770253156147847399375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69313027004208197129865833 51984770253156147847399375)
    ·
      refine ⟨77977155379734221771099063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51984770253156147847399375 77977155379734221771099063)
      ·
        refine ⟨116965733069601332656648595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77977155379734221771099063 116965733069601332656648595)
        ·
          refine ⟨175448599604401998984972893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116965733069601332656648595 175448599604401998984972893)
          ·
            refine ⟨65793224851650749619364835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175448599604401998984972893 65793224851650749619364835)
            ·
              refine ⟨98689837277476124429047253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65793224851650749619364835 98689837277476124429047253)
              ·
                refine ⟨2313043061190846666305795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98689837277476124429047253 2313043061190846666305795)
                ·
                  refine ⟨3469564591786269999458693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313043061190846666305795 3469564591786269999458693)
                  ·
                    refine ⟨650543360959925624898505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469564591786269999458693 650543360959925624898505)
                    ·
                      rfl

theorem cell22_1900393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1900393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900393 prefixEnd_1900393 := by exact prefixLift 1900393
  have htrace : WordTrace (prefixWord ++ tailWord_1900393) baseStart_1900393 baseEnd_1900393 := by
    simpa [prefixWord, tailWord_1900393, baseEnd_1900393] using wordTrace_append hprefix tailTrace_1900393
  have hstable : (prefixWord ++ tailWord_1900393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900393).length < 2 ^ (prefixWord ++ tailWord_1900393).sum := by decide
  have hdescent : baseEnd_1900393 < baseStart_1900393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900442 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1900442 : Nat := 118140960795 + 1900442 * 2 ^ 59
def prefixEnd_1900442 : Nat := 4983230072969 + 3 ^ 40 * 1900442 * 2
def baseEnd_1900442 : Nat := 216853378220435276807785

theorem tailTrace_1900442 : CollatzResearch.WordTrace tailWord_1900442 prefixEnd_1900442 216853378220435276807785 := by
  unfold tailWord_1900442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17328703545257669624599895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46209876120687118998933053 17328703545257669624599895)
  ·
    refine ⟨25993055317886504436899843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17328703545257669624599895 25993055317886504436899843)
    ·
      refine ⟨38989582976829756655349765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25993055317886504436899843 38989582976829756655349765)
      ·
        refine ⟨7310546808155579372878081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38989582976829756655349765 7310546808155579372878081)
        ·
          refine ⟨5482910106116684529658561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7310546808155579372878081 5482910106116684529658561)
          ·
            refine ⟨4112182579587513397243921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5482910106116684529658561 4112182579587513397243921)
            ·
              refine ⟨3084136934690635047932941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112182579587513397243921 3084136934690635047932941)
              ·
                refine ⟨1156551350508988142974853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084136934690635047932941 1156551350508988142974853)
                ·
                  refine ⟨216853378220435276807785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156551350508988142974853 216853378220435276807785)
                  ·
                    rfl

theorem cell22_1900442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1900442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900442 prefixEnd_1900442 := by exact prefixLift 1900442
  have htrace : WordTrace (prefixWord ++ tailWord_1900442) baseStart_1900442 baseEnd_1900442 := by
    simpa [prefixWord, tailWord_1900442, baseEnd_1900442] using wordTrace_append hprefix tailTrace_1900442
  have hstable : (prefixWord ++ tailWord_1900442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900442).length < 2 ^ (prefixWord ++ tailWord_1900442).sum := by decide
  have hdescent : baseEnd_1900442 < baseStart_1900442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900444 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_1900444 : Nat := 118140960795 + 1900444 * 2 ^ 59
def prefixEnd_1900444 : Nat := 4983230072969 + 3 ^ 40 * 1900444 * 2
def baseEnd_1900444 : Nat := 650560819302178491873349

theorem tailTrace_1900444 : CollatzResearch.WordTrace tailWord_1900444 prefixEnd_1900444 650560819302178491873349 := by
  unfold tailWord_1900444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34657443563511716419986193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46209924751348955226648257 34657443563511716419986193)
  ·
    refine ⟨25993082672633787314989645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34657443563511716419986193 25993082672633787314989645)
    ·
      refine ⟨9747406002237670243121117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25993082672633787314989645 9747406002237670243121117)
      ·
        refine ⟨3655277250839126341170419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9747406002237670243121117 3655277250839126341170419)
        ·
          refine ⟨5482915876258689511755629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655277250839126341170419 5482915876258689511755629)
          ·
            refine ⟨2056093453597008566908361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5482915876258689511755629 2056093453597008566908361)
            ·
              refine ⟨1542070090197756425181271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056093453597008566908361 1542070090197756425181271)
              ·
                refine ⟨2313105135296634637771907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542070090197756425181271 2313105135296634637771907)
                ·
                  refine ⟨3469657702944951956657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313105135296634637771907 3469657702944951956657861)
                  ·
                    refine ⟨650560819302178491873349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469657702944951956657861 650560819302178491873349)
                    ·
                      rfl

theorem cell22_1900444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_1900444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900444 prefixEnd_1900444 := by exact prefixLift 1900444
  have htrace : WordTrace (prefixWord ++ tailWord_1900444) baseStart_1900444 baseEnd_1900444 := by
    simpa [prefixWord, tailWord_1900444, baseEnd_1900444] using wordTrace_append hprefix tailTrace_1900444
  have hstable : (prefixWord ++ tailWord_1900444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900444).length < 2 ^ (prefixWord ++ tailWord_1900444).sum := by decide
  have hdescent : baseEnd_1900444 < baseStart_1900444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900513 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1900513 : Nat := 118140960795 + 1900513 * 2 ^ 59
def prefixEnd_1900513 : Nat := 4983230072969 + 3 ^ 40 * 1900513 * 2
def baseEnd_1900513 : Nat := 650584439412285311898137

theorem tailTrace_1900513 : CollatzResearch.WordTrace tailWord_1900513 prefixEnd_1900513 650584439412285311898137 := by
  unfold tailWord_1900513
  simp only [CollatzResearch.WordTrace]
  refine ⟨69317403763773457624234193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46211602509182305082822795 69317403763773457624234193)
  ·
    refine ⟨51988052822830093218175645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69317403763773457624234193 51988052822830093218175645)
    ·
      refine ⟨19495519808561284956815867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51988052822830093218175645 19495519808561284956815867)
      ·
        refine ⟨29243279712841927435223801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19495519808561284956815867 29243279712841927435223801)
        ·
          refine ⟨21932459784631445576417851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29243279712841927435223801 21932459784631445576417851)
          ·
            refine ⟨32898689676947168364626777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21932459784631445576417851 32898689676947168364626777)
            ·
              refine ⟨24674017257710376273470083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32898689676947168364626777 24674017257710376273470083)
              ·
                refine ⟨37011025886565564410205125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24674017257710376273470083 37011025886565564410205125)
                ·
                  refine ⟨6939567353731043326913461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37011025886565564410205125 6939567353731043326913461)
                  ·
                    refine ⟨650584439412285311898137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6939567353731043326913461 650584439412285311898137)
                    ·
                      rfl

theorem cell22_1900513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1900513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900513 prefixEnd_1900513 := by exact prefixLift 1900513
  have htrace : WordTrace (prefixWord ++ tailWord_1900513) baseStart_1900513 baseEnd_1900513 := by
    simpa [prefixWord, tailWord_1900513, baseEnd_1900513] using wordTrace_append hprefix tailTrace_1900513
  have hstable : (prefixWord ++ tailWord_1900513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900513).length < 2 ^ (prefixWord ++ tailWord_1900513).sum := by decide
  have hdescent : baseEnd_1900513 < baseStart_1900513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900519 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1900519 : Nat := 118140960795 + 1900519 * 2 ^ 59
def prefixEnd_1900519 : Nat := 4983230072969 + 3 ^ 40 * 1900519 * 2
def baseEnd_1900519 : Nat := 650586493334903296248119

theorem tailTrace_1900519 : CollatzResearch.WordTrace tailWord_1900519 prefixEnd_1900519 650586493334903296248119 := by
  unfold tailWord_1900519
  simp only [CollatzResearch.WordTrace]
  refine ⟨69317622601751720648952611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46211748401167813765968407 69317622601751720648952611)
  ·
    refine ⟨103976433902627580973428917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69317622601751720648952611 103976433902627580973428917)
    ·
      refine ⟨9747790678371335716258961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103976433902627580973428917 9747790678371335716258961)
      ·
        refine ⟨7310843008778501787194221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9747790678371335716258961 7310843008778501787194221)
        ·
          refine ⟨2741566128291938170197833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7310843008778501787194221 2741566128291938170197833)
          ·
            refine ⟨2056174596218953627648375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741566128291938170197833 2056174596218953627648375)
            ·
              refine ⟨3084261894328430441472563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056174596218953627648375 3084261894328430441472563)
              ·
                refine ⟨4626392841492645662208845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084261894328430441472563 4626392841492645662208845)
                ·
                  refine ⟨1734897315559742123328317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4626392841492645662208845 1734897315559742123328317)
                  ·
                    refine ⟨650586493334903296248119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734897315559742123328317 650586493334903296248119)
                    ·
                      rfl

theorem cell22_1900519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1900519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900519 prefixEnd_1900519 := by exact prefixLift 1900519
  have htrace : WordTrace (prefixWord ++ tailWord_1900519) baseStart_1900519 baseEnd_1900519 := by
    simpa [prefixWord, tailWord_1900519, baseEnd_1900519] using wordTrace_append hprefix tailTrace_1900519
  have hstable : (prefixWord ++ tailWord_1900519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900519).length < 2 ^ (prefixWord ++ tailWord_1900519).sum := by decide
  have hdescent : baseEnd_1900519 < baseStart_1900519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900543 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 6]
def baseStart_1900543 : Nat := 118140960795 + 1900543 * 2 ^ 59
def prefixEnd_1900543 : Nat := 4983230072969 + 3 ^ 40 * 1900543 * 2
def baseEnd_1900543 : Nat := 216864903008458411216015

theorem tailTrace_1900543 : CollatzResearch.WordTrace tailWord_1900543 prefixEnd_1900543 216864903008458411216015 := by
  unfold tailWord_1900543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318497953664772747826283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46212331969109848498550855 69318497953664772747826283)
  ·
    refine ⟨103977746930497159121739425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69318497953664772747826283 103977746930497159121739425)
    ·
      refine ⟨77983310197872869341304569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103977746930497159121739425 77983310197872869341304569)
      ·
        refine ⟨58487482648404652005978427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77983310197872869341304569 58487482648404652005978427)
        ·
          refine ⟨87731223972606978008967641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58487482648404652005978427 87731223972606978008967641)
          ·
            refine ⟨65798417979455233506725731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87731223972606978008967641 65798417979455233506725731)
            ·
              refine ⟨98697626969182850260088597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65798417979455233506725731 98697626969182850260088597)
              ·
                refine ⟨4626451264180446105941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98697626969182850260088597 4626451264180446105941653)
                ·
                  refine ⟨216864903008458411216015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4626451264180446105941653 216864903008458411216015)
                  ·
                    rfl

theorem cell22_1900543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_1900543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900543 prefixEnd_1900543 := by exact prefixLift 1900543
  have htrace : WordTrace (prefixWord ++ tailWord_1900543) baseStart_1900543 baseEnd_1900543 := by
    simpa [prefixWord, tailWord_1900543, baseEnd_1900543] using wordTrace_append hprefix tailTrace_1900543
  have hstable : (prefixWord ++ tailWord_1900543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900543).length < 2 ^ (prefixWord ++ tailWord_1900543).sum := by decide
  have hdescent : baseEnd_1900543 < baseStart_1900543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900545 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1900545 : Nat := 118140960795 + 1900545 * 2 ^ 59
def prefixEnd_1900545 : Nat := 4983230072969 + 3 ^ 40 * 1900545 * 2
def baseEnd_1900545 : Nat := 650595393666247895098039

theorem tailTrace_1900545 : CollatzResearch.WordTrace tailWord_1900545 prefixEnd_1900545 650595393666247895098039 := by
  unfold tailWord_1900545
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318570899657527089399089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46212380599771684726266059 69318570899657527089399089)
  ·
    refine ⟨51988928174743145317049317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69318570899657527089399089 51988928174743145317049317)
    ·
      refine ⟨9747924032764339746946747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51988928174743145317049317 9747924032764339746946747)
      ·
        refine ⟨14621886049146509620420121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747924032764339746946747 14621886049146509620420121)
        ·
          refine ⟨10966414536859882215315091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14621886049146509620420121 10966414536859882215315091)
          ·
            refine ⟨16449621805289823322972637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966414536859882215315091 16449621805289823322972637)
            ·
              refine ⟨6168608176983683746114739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16449621805289823322972637 6168608176983683746114739)
              ·
                refine ⟨9252912265475525619172109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6168608176983683746114739 9252912265475525619172109)
                ·
                  refine ⟨3469842099553322107189541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9252912265475525619172109 3469842099553322107189541)
                  ·
                    refine ⟨650595393666247895098039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469842099553322107189541 650595393666247895098039)
                    ·
                      rfl

theorem cell22_1900545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1900545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900545 prefixEnd_1900545 := by exact prefixLift 1900545
  have htrace : WordTrace (prefixWord ++ tailWord_1900545) baseStart_1900545 baseEnd_1900545 := by
    simpa [prefixWord, tailWord_1900545, baseEnd_1900545] using wordTrace_append hprefix tailTrace_1900545
  have hstable : (prefixWord ++ tailWord_1900545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900545).length < 2 ^ (prefixWord ++ tailWord_1900545).sum := by decide
  have hdescent : baseEnd_1900545 < baseStart_1900545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900588 : List Nat := [2, 2, 1, 1, 1, 2, 2, 11]
def baseStart_1900588 : Nat := 118140960795 + 1900588 * 2 ^ 59
def prefixEnd_1900588 : Nat := 4983230072969 + 3 ^ 40 * 1900588 * 2
def baseEnd_1900588 : Nat := 72290012605001124030323

theorem tailTrace_1900588 : CollatzResearch.WordTrace tailWord_1900588 prefixEnd_1900588 72290012605001124030323 := by
  unfold tailWord_1900588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34660069619250872716607209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46213426159001163622142945 34660069619250872716607209)
  ·
    refine ⟨25995052214438154537455407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34660069619250872716607209 25995052214438154537455407)
    ·
      refine ⟨38992578321657231806183111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25995052214438154537455407 38992578321657231806183111)
      ·
        refine ⟨58488867482485847709274667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38992578321657231806183111 58488867482485847709274667)
        ·
          refine ⟨87733301223728771563912001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58488867482485847709274667 87733301223728771563912001)
          ·
            refine ⟨65799975917796578672934001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87733301223728771563912001 65799975917796578672934001)
            ·
              refine ⟨49349981938347434004700501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65799975917796578672934001 49349981938347434004700501)
              ·
                refine ⟨72290012605001124030323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49349981938347434004700501 72290012605001124030323)
                ·
                  rfl

theorem cell22_1900588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_1900588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900588 prefixEnd_1900588 := by exact prefixLift 1900588
  have htrace : WordTrace (prefixWord ++ tailWord_1900588) baseStart_1900588 baseEnd_1900588 := by
    simpa [prefixWord, tailWord_1900588, baseEnd_1900588] using wordTrace_append hprefix tailTrace_1900588
  have hstable : (prefixWord ++ tailWord_1900588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900588).length < 2 ^ (prefixWord ++ tailWord_1900588).sum := by decide
  have hdescent : baseEnd_1900588 < baseStart_1900588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900592 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_1900592 : Nat := 118140960795 + 1900592 * 2 ^ 59
def prefixEnd_1900592 : Nat := 4983230072969 + 3 ^ 40 * 1900592 * 2
def baseEnd_1900592 : Nat := 650611482726755439172895

theorem tailTrace_1900592 : CollatzResearch.WordTrace tailWord_1900592 prefixEnd_1900592 650611482726755439172895 := by
  unfold tailWord_1900592
  simp only [CollatzResearch.WordTrace]
  refine ⟨34660142565243627058180015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46213523420324836077573353 34660142565243627058180015)
  ·
    refine ⟨51990213847865440587270023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34660142565243627058180015 51990213847865440587270023)
    ·
      refine ⟨77985320771798160880905035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51990213847865440587270023 77985320771798160880905035)
      ·
        refine ⟨116977981157697241321357553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77985320771798160880905035 116977981157697241321357553)
        ·
          refine ⟨87733485868272930991018165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116977981157697241321357553 87733485868272930991018165)
          ·
            refine ⟨8225014300150587280407953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87733485868272930991018165 8225014300150587280407953)
            ·
              refine ⟨6168760725112940460305965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225014300150587280407953 6168760725112940460305965)
              ·
                refine ⟨2313285271917352672614737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6168760725112940460305965 2313285271917352672614737)
                ·
                  refine ⟨1734963953938014504461053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313285271917352672614737 1734963953938014504461053)
                  ·
                    refine ⟨650611482726755439172895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734963953938014504461053 650611482726755439172895)
                    ·
                      rfl

theorem cell22_1900592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_1900592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900592 prefixEnd_1900592 := by exact prefixLift 1900592
  have htrace : WordTrace (prefixWord ++ tailWord_1900592) baseStart_1900592 baseEnd_1900592 := by
    simpa [prefixWord, tailWord_1900592, baseEnd_1900592] using wordTrace_append hprefix tailTrace_1900592
  have hstable : (prefixWord ++ tailWord_1900592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900592).length < 2 ^ (prefixWord ++ tailWord_1900592).sum := by decide
  have hdescent : baseEnd_1900592 < baseStart_1900592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_1900603 : Nat := 118140960795 + 1900603 * 2 ^ 59
def prefixEnd_1900603 : Nat := 4983230072969 + 3 ^ 40 * 1900603 * 2
def baseEnd_1900603 : Nat := 650615248251555077147861

theorem tailTrace_1900603 : CollatzResearch.WordTrace tailWord_1900603 prefixEnd_1900603 650615248251555077147861 := by
  unfold tailWord_1900603
  simp only [CollatzResearch.WordTrace]
  refine ⟨69320686333447402995010463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46213790888964935330006975 69320686333447402995010463)
  ·
    refine ⟨103981029500171104492515695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69320686333447402995010463 103981029500171104492515695)
    ·
      refine ⟨155971544250256656738773543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103981029500171104492515695 155971544250256656738773543)
      ·
        refine ⟨233957316375384985108160315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155971544250256656738773543 233957316375384985108160315)
        ·
          refine ⟨350935974563077477662240473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233957316375384985108160315 350935974563077477662240473)
          ·
            refine ⟨263201980922308108246680355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350935974563077477662240473 263201980922308108246680355)
            ·
              refine ⟨394802971383462162370020533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263201980922308108246680355 394802971383462162370020533)
              ·
                refine ⟨37012778567199577722189425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394802971383462162370020533 37012778567199577722189425)
                ·
                  refine ⟨27759583925399683291642069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37012778567199577722189425 27759583925399683291642069)
                  ·
                    refine ⟨650615248251555077147861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27759583925399683291642069 650615248251555077147861)
                    ·
                      rfl

theorem cell22_1900603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_1900603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900603 prefixEnd_1900603 := by exact prefixLift 1900603
  have htrace : WordTrace (prefixWord ++ tailWord_1900603) baseStart_1900603 baseEnd_1900603 := by
    simpa [prefixWord, tailWord_1900603, baseEnd_1900603] using wordTrace_append hprefix tailTrace_1900603
  have hstable : (prefixWord ++ tailWord_1900603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900603).length < 2 ^ (prefixWord ++ tailWord_1900603).sum := by decide
  have hdescent : baseEnd_1900603 < baseStart_1900603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900626 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1900626 : Nat := 118140960795 + 1900626 * 2 ^ 59
def prefixEnd_1900626 : Nat := 4983230072969 + 3 ^ 40 * 1900626 * 2
def baseEnd_1900626 : Nat := 650623121621590683822791

theorem tailTrace_1900626 : CollatzResearch.WordTrace tailWord_1900626 prefixEnd_1900626 650623121621590683822791 := by
  unfold tailWord_1900626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330381303091019480774433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46214350141576051948731821 17330381303091019480774433)
  ·
    refine ⟨12997785977318264610580825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17330381303091019480774433 12997785977318264610580825)
    ·
      refine ⟨9748339482988698457935619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12997785977318264610580825 9748339482988698457935619)
      ·
        refine ⟨14622509224483047686903429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748339482988698457935619 14622509224483047686903429)
        ·
          refine ⟨2741720479590571441294393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14622509224483047686903429 2741720479590571441294393)
          ·
            refine ⟨2056290359692928580970795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741720479590571441294393 2056290359692928580970795)
            ·
              refine ⟨3084435539539392871456193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056290359692928580970795 3084435539539392871456193)
              ·
                refine ⟨2313326654654544653592145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084435539539392871456193 2313326654654544653592145)
                ·
                  refine ⟨1734994990990908490194109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313326654654544653592145 1734994990990908490194109)
                  ·
                    refine ⟨650623121621590683822791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734994990990908490194109 650623121621590683822791)
                    ·
                      rfl

theorem cell22_1900626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1900626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900626 prefixEnd_1900626 := by exact prefixLift 1900626
  have htrace : WordTrace (prefixWord ++ tailWord_1900626) baseStart_1900626 baseEnd_1900626 := by
    simpa [prefixWord, tailWord_1900626, baseEnd_1900626] using wordTrace_append hprefix tailTrace_1900626
  have hstable : (prefixWord ++ tailWord_1900626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900626).length < 2 ^ (prefixWord ++ tailWord_1900626).sum := by decide
  have hdescent : baseEnd_1900626 < baseStart_1900626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900694 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1900694 : Nat := 118140960795 + 1900694 * 2 ^ 59
def prefixEnd_1900694 : Nat := 4983230072969 + 3 ^ 40 * 1900694 * 2
def baseEnd_1900694 : Nat := 650646399411261173122583

theorem tailTrace_1900694 : CollatzResearch.WordTrace tailWord_1900694 prefixEnd_1900694 650646399411261173122583 := by
  unfold tailWord_1900694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332750336007357846035821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46216003584078483691048757 4332750336007357846035821)
  ·
    refine ⟨1624781376002759192263433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4332750336007357846035821 1624781376002759192263433)
    ·
      refine ⟨1218586032002069394197575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1624781376002759192263433 1218586032002069394197575)
      ·
        refine ⟨1827879048003104091296363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218586032002069394197575 1827879048003104091296363)
        ·
          refine ⟨2741818572004656136944545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827879048003104091296363 2741818572004656136944545)
          ·
            refine ⟨2056363929003492102708409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741818572004656136944545 2056363929003492102708409)
            ·
              refine ⟨1542272946752619077031307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056363929003492102708409 1542272946752619077031307)
              ·
                refine ⟨2313409420128928615546961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542272946752619077031307 2313409420128928615546961)
                ·
                  refine ⟨1735057065096696461660221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313409420128928615546961 1735057065096696461660221)
                  ·
                    refine ⟨650646399411261173122583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735057065096696461660221 650646399411261173122583)
                    ·
                      rfl

theorem cell22_1900694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1900694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900694 prefixEnd_1900694 := by exact prefixLift 1900694
  have htrace : WordTrace (prefixWord ++ tailWord_1900694) baseStart_1900694 baseEnd_1900694 := by
    simpa [prefixWord, tailWord_1900694, baseEnd_1900694] using wordTrace_append hprefix tailTrace_1900694
  have hstable : (prefixWord ++ tailWord_1900694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900694).length < 2 ^ (prefixWord ++ tailWord_1900694).sum := by decide
  have hdescent : baseEnd_1900694 < baseStart_1900694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900727 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1900727 : Nat := 118140960795 + 1900727 * 2 ^ 59
def prefixEnd_1900727 : Nat := 4983230072969 + 3 ^ 40 * 1900727 * 2
def baseEnd_1900727 : Nat := 650657695985660087047481

theorem tailTrace_1900727 : CollatzResearch.WordTrace tailWord_1900727 prefixEnd_1900727 650657695985660087047481 := by
  unfold tailWord_1900727
  simp only [CollatzResearch.WordTrace]
  refine ⟨69325208984998172172524435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46216805989998781448349623 69325208984998172172524435)
  ·
    refine ⟨103987813477497258258786653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69325208984998172172524435 103987813477497258258786653)
    ·
      refine ⟨38995430054061471847044995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103987813477497258258786653 38995430054061471847044995)
      ·
        refine ⟨58493145081092207770567493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38995430054061471847044995 58493145081092207770567493)
        ·
          refine ⟨10967464702704788956981405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58493145081092207770567493 10967464702704788956981405)
          ·
            refine ⟨4112799263514295858868027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10967464702704788956981405 4112799263514295858868027)
            ·
              refine ⟨6169198895271443788302041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112799263514295858868027 6169198895271443788302041)
              ·
                refine ⟨4626899171453582841226531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169198895271443788302041 4626899171453582841226531)
                ·
                  refine ⟨6940348757180374261839797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626899171453582841226531 6940348757180374261839797)
                  ·
                    refine ⟨650657695985660087047481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6940348757180374261839797 650657695985660087047481)
                    ·
                      rfl

theorem cell22_1900727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1900727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900727 prefixEnd_1900727 := by exact prefixLift 1900727
  have htrace : WordTrace (prefixWord ++ tailWord_1900727) baseStart_1900727 baseEnd_1900727 := by
    simpa [prefixWord, tailWord_1900727, baseEnd_1900727] using wordTrace_append hprefix tailTrace_1900727
  have hstable : (prefixWord ++ tailWord_1900727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900727).length < 2 ^ (prefixWord ++ tailWord_1900727).sum := by decide
  have hdescent : baseEnd_1900727 < baseStart_1900727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900817 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1900817 : Nat := 118140960795 + 1900817 * 2 ^ 59
def prefixEnd_1900817 : Nat := 4983230072969 + 3 ^ 40 * 1900817 * 2
def baseEnd_1900817 : Nat := 650688504824929852297205

theorem tailTrace_1900817 : CollatzResearch.WordTrace tailWord_1900817 prefixEnd_1900817 650688504824929852297205 := by
  unfold tailWord_1900817
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328491554672117543300705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46218994369781411695533803 69328491554672117543300705)
  ·
    refine ⟨51996368666004088157475529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69328491554672117543300705 51996368666004088157475529)
    ·
      refine ⟨38997276499503066118106647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51996368666004088157475529 38997276499503066118106647)
      ·
        refine ⟨58495914749254599177159971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38997276499503066118106647 58495914749254599177159971)
        ·
          refine ⟨87743872123881898765739957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58495914749254599177159971 87743872123881898765739957)
          ·
            refine ⟨8225988011613928009288121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87743872123881898765739957 8225988011613928009288121)
            ·
              refine ⟨6169491008710446006966091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225988011613928009288121 6169491008710446006966091)
              ·
                refine ⟨9254236513065669010449137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169491008710446006966091 9254236513065669010449137)
                ·
                  refine ⟨6940677384799251757836853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9254236513065669010449137 6940677384799251757836853)
                  ·
                    refine ⟨650688504824929852297205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6940677384799251757836853 650688504824929852297205)
                    ·
                      rfl

theorem cell22_1900817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1900817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900817 prefixEnd_1900817 := by exact prefixLift 1900817
  have htrace : WordTrace (prefixWord ++ tailWord_1900817) baseStart_1900817 baseEnd_1900817 := by
    simpa [prefixWord, tailWord_1900817, baseEnd_1900817] using wordTrace_append hprefix tailTrace_1900817
  have hstable : (prefixWord ++ tailWord_1900817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900817).length < 2 ^ (prefixWord ++ tailWord_1900817).sum := by decide
  have hdescent : baseEnd_1900817 < baseStart_1900817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900840 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1900840 : Nat := 118140960795 + 1900840 * 2 ^ 59
def prefixEnd_1900840 : Nat := 4983230072969 + 3 ^ 40 * 1900840 * 2
def baseEnd_1900840 : Nat := 650696378194965458972135

theorem tailTrace_1900840 : CollatzResearch.WordTrace tailWord_1900840 prefixEnd_1900840 650696378194965458972135 := by
  unfold tailWord_1900840
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664665216794396235693987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46219553622392528314258649 34664665216794396235693987)
  ·
    refine ⟨51996997825191594353540981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34664665216794396235693987 51996997825191594353540981)
    ·
      refine ⟨4874718546111711970644467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51996997825191594353540981 4874718546111711970644467)
      ·
        refine ⟨7312077819167567955966701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874718546111711970644467 7312077819167567955966701)
        ·
          refine ⟨2742029182187837983487513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7312077819167567955966701 2742029182187837983487513)
          ·
            refine ⟨2056521886640878487615635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742029182187837983487513 2056521886640878487615635)
            ·
              refine ⟨3084782829961317731423453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056521886640878487615635 3084782829961317731423453)
              ·
                refine ⟨1156793561235494149283795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084782829961317731423453 1156793561235494149283795)
                ·
                  refine ⟨1735190341853241223925693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156793561235494149283795 1735190341853241223925693)
                  ·
                    refine ⟨650696378194965458972135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735190341853241223925693 650696378194965458972135)
                    ·
                      rfl

theorem cell22_1900840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1900840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900840 prefixEnd_1900840 := by exact prefixLift 1900840
  have htrace : WordTrace (prefixWord ++ tailWord_1900840) baseStart_1900840 baseEnd_1900840 := by
    simpa [prefixWord, tailWord_1900840, baseEnd_1900840] using wordTrace_append hprefix tailTrace_1900840
  have hstable : (prefixWord ++ tailWord_1900840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900840).length < 2 ^ (prefixWord ++ tailWord_1900840).sum := by decide
  have hdescent : baseEnd_1900840 < baseStart_1900840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900988 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1900988 : Nat := 118140960795 + 1900988 * 2 ^ 59
def prefixEnd_1900988 : Nat := 4983230072969 + 3 ^ 40 * 1900988 * 2
def baseEnd_1900988 : Nat := 216915680539847468757227

theorem tailTrace_1900988 : CollatzResearch.WordTrace tailWord_1900988 prefixEnd_1900988 216915680539847468757227 := by
  unfold tailWord_1900988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34667364218526306873887809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46223152291368409165183745 34667364218526306873887809)
  ·
    refine ⟨26000523163894730155415857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34667364218526306873887809 26000523163894730155415857)
    ·
      refine ⟨19500392372921047616561893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26000523163894730155415857 19500392372921047616561893)
      ·
        refine ⟨3656323569922696428105355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19500392372921047616561893 3656323569922696428105355)
        ·
          refine ⟨5484485354884044642158033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656323569922696428105355 5484485354884044642158033)
          ·
            refine ⟨4113364016163033481618525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484485354884044642158033 4113364016163033481618525)
            ·
              refine ⟨1542511506061137555606947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4113364016163033481618525 1542511506061137555606947)
              ·
                refine ⟨2313767259091706333410421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542511506061137555606947 2313767259091706333410421)
                ·
                  refine ⟨216915680539847468757227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313767259091706333410421 216915680539847468757227)
                  ·
                    rfl

theorem cell22_1900988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1900988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900988 prefixEnd_1900988 := by exact prefixLift 1900988
  have htrace : WordTrace (prefixWord ++ tailWord_1900988) baseStart_1900988 baseEnd_1900988 := by
    simpa [prefixWord, tailWord_1900988, baseEnd_1900988] using wordTrace_append hprefix tailTrace_1900988
  have hstable : (prefixWord ++ tailWord_1900988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900988).length < 2 ^ (prefixWord ++ tailWord_1900988).sum := by decide
  have hdescent : baseEnd_1900988 < baseStart_1900988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900999 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 6]
def baseStart_1900999 : Nat := 118140960795 + 1900999 * 2 ^ 59
def prefixEnd_1900999 : Nat := 4983230072969 + 3 ^ 40 * 1900999 * 2
def baseEnd_1900999 : Nat := 216916935714780681415549

theorem tailTrace_1900999 : CollatzResearch.WordTrace tailWord_1900999 prefixEnd_1900999 216916935714780681415549 := by
  unfold tailWord_1900999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69335129640012762626426051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46223419760008508417617367 69335129640012762626426051)
  ·
    refine ⟨104002694460019143939639077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69335129640012762626426051 104002694460019143939639077)
    ·
      refine ⟨19500505211253589488682327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104002694460019143939639077 19500505211253589488682327)
      ·
        refine ⟨29250757816880384233023491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19500505211253589488682327 29250757816880384233023491)
        ·
          refine ⟨43876136725320576349535237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29250757816880384233023491 43876136725320576349535237)
          ·
            refine ⟨8226775635997608065537857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43876136725320576349535237 8226775635997608065537857)
            ·
              refine ⟨6170081726998206049153393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226775635997608065537857 6170081726998206049153393)
              ·
                refine ⟨4627561295248654536865045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170081726998206049153393 4627561295248654536865045)
                ·
                  refine ⟨216916935714780681415549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4627561295248654536865045 216916935714780681415549)
                  ·
                    rfl

theorem cell22_1900999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_1900999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1900999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1900999 prefixEnd_1900999 := by exact prefixLift 1900999
  have htrace : WordTrace (prefixWord ++ tailWord_1900999) baseStart_1900999 baseEnd_1900999 := by
    simpa [prefixWord, tailWord_1900999, baseEnd_1900999] using wordTrace_append hprefix tailTrace_1900999
  have hstable : (prefixWord ++ tailWord_1900999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900999).length < 2 ^ (prefixWord ++ tailWord_1900999).sum := by decide
  have hdescent : baseEnd_1900999 < baseStart_1900999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901031 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1901031 : Nat := 118140960795 + 1901031 * 2 ^ 59
def prefixEnd_1901031 : Nat := 4983230072969 + 3 ^ 40 * 1901031 * 2
def baseEnd_1901031 : Nat := 650761761398304627446549

theorem tailTrace_1901031 : CollatzResearch.WordTrace tailWord_1901031 prefixEnd_1901031 650761761398304627446549 := by
  unfold tailWord_1901031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69336296775896832091590947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46224197850597888061060631 69336296775896832091590947)
  ·
    refine ⟨104004445163845248137386421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69336296775896832091590947 104004445163845248137386421)
    ·
      refine ⟨9750416734110492012879977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104004445163845248137386421 9750416734110492012879977)
      ·
        refine ⟨7312812550582869009659983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750416734110492012879977 7312812550582869009659983)
        ·
          refine ⟨10969218825874303514489975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312812550582869009659983 10969218825874303514489975)
          ·
            refine ⟨16453828238811455271734963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969218825874303514489975 16453828238811455271734963)
            ·
              refine ⟨24680742358217182907602445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16453828238811455271734963 24680742358217182907602445)
              ·
                refine ⟨9255278384331443590350917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24680742358217182907602445 9255278384331443590350917)
                ·
                  refine ⟨1735364697062145673190797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9255278384331443590350917 1735364697062145673190797)
                  ·
                    refine ⟨650761761398304627446549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735364697062145673190797 650761761398304627446549)
                    ·
                      rfl

theorem cell22_1901031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1901031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901031 prefixEnd_1901031 := by exact prefixLift 1901031
  have htrace : WordTrace (prefixWord ++ tailWord_1901031) baseStart_1901031 baseEnd_1901031 := by
    simpa [prefixWord, tailWord_1901031, baseEnd_1901031] using wordTrace_append hprefix tailTrace_1901031
  have hstable : (prefixWord ++ tailWord_1901031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901031).length < 2 ^ (prefixWord ++ tailWord_1901031).sum := by decide
  have hdescent : baseEnd_1901031 < baseStart_1901031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901046 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1901046 : Nat := 118140960795 + 1901046 * 2 ^ 59
def prefixEnd_1901046 : Nat := 4983230072969 + 3 ^ 40 * 1901046 * 2
def baseEnd_1901046 : Nat := 650766896204849588321503

theorem tailTrace_1901046 : CollatzResearch.WordTrace tailWord_1901046 prefixEnd_1901046 650766896204849588321503 := by
  unfold tailWord_1901046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333552741927655603336687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46224562580561659768924661 4333552741927655603336687)
  ·
    refine ⟨6500329112891483405005031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333552741927655603336687 6500329112891483405005031)
    ·
      refine ⟨9750493669337225107507547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500329112891483405005031 9750493669337225107507547)
      ·
        refine ⟨14625740504005837661261321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750493669337225107507547 14625740504005837661261321)
        ·
          refine ⟨10969305378004378245945991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14625740504005837661261321 10969305378004378245945991)
          ·
            refine ⟨16453958067006567368918987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969305378004378245945991 16453958067006567368918987)
            ·
              refine ⟨24680937100509851053378481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16453958067006567368918987 24680937100509851053378481)
              ·
                refine ⟨18510702825382388290033861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24680937100509851053378481 18510702825382388290033861)
                ·
                  refine ⟨3470756779759197804381349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18510702825382388290033861 3470756779759197804381349)
                  ·
                    refine ⟨650766896204849588321503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470756779759197804381349 650766896204849588321503)
                    ·
                      rfl

theorem cell22_1901046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1901046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901046 prefixEnd_1901046 := by exact prefixLift 1901046
  have htrace : WordTrace (prefixWord ++ tailWord_1901046) baseStart_1901046 baseEnd_1901046 := by
    simpa [prefixWord, tailWord_1901046, baseEnd_1901046] using wordTrace_append hprefix tailTrace_1901046
  have hstable : (prefixWord ++ tailWord_1901046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901046).length < 2 ^ (prefixWord ++ tailWord_1901046).sum := by decide
  have hdescent : baseEnd_1901046 < baseStart_1901046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901063 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1901063 : Nat := 118140960795 + 1901063 * 2 ^ 59
def prefixEnd_1901063 : Nat := 4983230072969 + 3 ^ 40 * 1901063 * 2
def baseEnd_1901063 : Nat := 650772715652267210646451

theorem tailTrace_1901063 : CollatzResearch.WordTrace tailWord_1901063 prefixEnd_1901063 650772715652267210646451 := by
  unfold tailWord_1901063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69337463911780901556755843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46224975941187267704503895 69337463911780901556755843)
  ·
    refine ⟨104006195867671352335133765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69337463911780901556755843 104006195867671352335133765)
    ·
      refine ⟨19501161725188378562837581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104006195867671352335133765 19501161725188378562837581)
      ·
        refine ⟨7312935646945641961064093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19501161725188378562837581 7312935646945641961064093)
        ·
          refine ⟨2742350867604615735399035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7312935646945641961064093 2742350867604615735399035)
          ·
            refine ⟨4113526301406923603098553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742350867604615735399035 4113526301406923603098553)
            ·
              refine ⟨3085144726055192702323915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113526301406923603098553 3085144726055192702323915)
              ·
                refine ⟨4627717089082789053485873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085144726055192702323915 4627717089082789053485873)
                ·
                  refine ⟨3470787816812091790114405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627717089082789053485873 3470787816812091790114405)
                  ·
                    refine ⟨650772715652267210646451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470787816812091790114405 650772715652267210646451)
                    ·
                      rfl

theorem cell22_1901063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1901063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901063 prefixEnd_1901063 := by exact prefixLift 1901063
  have htrace : WordTrace (prefixWord ++ tailWord_1901063) baseStart_1901063 baseEnd_1901063 := by
    simpa [prefixWord, tailWord_1901063, baseEnd_1901063] using wordTrace_append hprefix tailTrace_1901063
  have hstable : (prefixWord ++ tailWord_1901063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901063).length < 2 ^ (prefixWord ++ tailWord_1901063).sum := by decide
  have hdescent : baseEnd_1901063 < baseStart_1901063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901095 : List Nat := [1, 1, 7, 2, 1, 2, 1, 7]
def baseStart_1901095 : Nat := 118140960795 + 1901095 * 2 ^ 59
def prefixEnd_1901095 : Nat := 4983230072969 + 3 ^ 40 * 1901095 * 2
def baseEnd_1901095 : Nat := 72309296656247754871817

theorem tailTrace_1901095 : CollatzResearch.WordTrace tailWord_1901095 prefixEnd_1901095 72309296656247754871817 := by
  unfold tailWord_1901095
  simp only [CollatzResearch.WordTrace]
  refine ⟨69338631047664971021920739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46225754031776647347947159 69338631047664971021920739)
  ·
    refine ⟨104007946571497456532881109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69338631047664971021920739 104007946571497456532881109)
    ·
      refine ⟨2437686247769471637489401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104007946571497456532881109 2437686247769471637489401)
      ·
        refine ⟨1828264685827103728117051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437686247769471637489401 1828264685827103728117051)
        ·
          refine ⟨2742397028740655592175577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828264685827103728117051 2742397028740655592175577)
          ·
            refine ⟨2056797771555491694131683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742397028740655592175577 2056797771555491694131683)
            ·
              refine ⟨3085196657333237541197525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056797771555491694131683 3085196657333237541197525)
              ·
                refine ⟨72309296656247754871817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3085196657333237541197525 72309296656247754871817)
                ·
                  rfl

theorem cell22_1901095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 7].length) (baseStart_1901095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901095 prefixEnd_1901095 := by exact prefixLift 1901095
  have htrace : WordTrace (prefixWord ++ tailWord_1901095) baseStart_1901095 baseEnd_1901095 := by
    simpa [prefixWord, tailWord_1901095, baseEnd_1901095] using wordTrace_append hprefix tailTrace_1901095
  have hstable : (prefixWord ++ tailWord_1901095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901095).length < 2 ^ (prefixWord ++ tailWord_1901095).sum := by decide
  have hdescent : baseEnd_1901095 < baseStart_1901095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901104 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_1901104 : Nat := 118140960795 + 1901104 * 2 ^ 59
def prefixEnd_1901104 : Nat := 4983230072969 + 3 ^ 40 * 1901104 * 2
def baseEnd_1901104 : Nat := 650786750790156770371325

theorem tailTrace_1901104 : CollatzResearch.WordTrace tailWord_1901104 prefixEnd_1901104 650786750790156770371325 := by
  unfold tailWord_1901104
  simp only [CollatzResearch.WordTrace]
  refine ⟨34669479652316182779499183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46225972869754910372665577 34669479652316182779499183)
  ·
    refine ⟨52004219478474274169248775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34669479652316182779499183 52004219478474274169248775)
    ·
      refine ⟨78006329217711411253873163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52004219478474274169248775 78006329217711411253873163)
      ·
        refine ⟨117009493826567116880809745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78006329217711411253873163 117009493826567116880809745)
        ·
          refine ⟨87757120369925337660607309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117009493826567116880809745 87757120369925337660607309)
          ·
            refine ⟨32908920138722001622727741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87757120369925337660607309 32908920138722001622727741)
            ·
              refine ⟨12340845052020750608522903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32908920138722001622727741 12340845052020750608522903)
              ·
                refine ⟨18511267578031125912784355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12340845052020750608522903 18511267578031125912784355)
                ·
                  refine ⟨27766901367046688869176533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18511267578031125912784355 27766901367046688869176533)
                  ·
                    refine ⟨650786750790156770371325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27766901367046688869176533 650786750790156770371325)
                    ·
                      rfl

theorem cell22_1901104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_1901104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901104 prefixEnd_1901104 := by exact prefixLift 1901104
  have htrace : WordTrace (prefixWord ++ tailWord_1901104) baseStart_1901104 baseEnd_1901104 := by
    simpa [prefixWord, tailWord_1901104, baseEnd_1901104] using wordTrace_append hprefix tailTrace_1901104
  have hstable : (prefixWord ++ tailWord_1901104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901104).length < 2 ^ (prefixWord ++ tailWord_1901104).sum := by decide
  have hdescent : baseEnd_1901104 < baseStart_1901104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901106 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1901106 : Nat := 118140960795 + 1901106 * 2 ^ 59
def prefixEnd_1901106 : Nat := 4983230072969 + 3 ^ 40 * 1901106 * 2
def baseEnd_1901106 : Nat := 216929145143676477273773

theorem tailTrace_1901106 : CollatzResearch.WordTrace tailWord_1901106 prefixEnd_1901106 216929145143676477273773 := by
  unfold tailWord_1901106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334758062656279975142793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46226021500416746600380781 17334758062656279975142793)
  ·
    refine ⟨13001068546992209981357095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17334758062656279975142793 13001068546992209981357095)
    ·
      refine ⟨19501602820488314972035643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001068546992209981357095 19501602820488314972035643)
      ·
        refine ⟨29252404230732472458053465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19501602820488314972035643 29252404230732472458053465)
        ·
          refine ⟨21939303173049354343540099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29252404230732472458053465 21939303173049354343540099)
          ·
            refine ⟨32908954759574031515310149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939303173049354343540099 32908954759574031515310149)
            ·
              refine ⟨6170429017420130909120653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32908954759574031515310149 6170429017420130909120653)
              ·
                refine ⟨2313910881532549090920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6170429017420130909120653 2313910881532549090920245)
                ·
                  refine ⟨216929145143676477273773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313910881532549090920245 216929145143676477273773)
                  ·
                    rfl

theorem cell22_1901106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1901106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901106 prefixEnd_1901106 := by exact prefixLift 1901106
  have htrace : WordTrace (prefixWord ++ tailWord_1901106) baseStart_1901106 baseEnd_1901106 := by
    simpa [prefixWord, tailWord_1901106, baseEnd_1901106] using wordTrace_append hprefix tailTrace_1901106
  have hstable : (prefixWord ++ tailWord_1901106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901106).length < 2 ^ (prefixWord ++ tailWord_1901106).sum := by decide
  have hdescent : baseEnd_1901106 < baseStart_1901106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901110 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1901110 : Nat := 118140960795 + 1901110 * 2 ^ 59
def prefixEnd_1901110 : Nat := 4983230072969 + 3 ^ 40 * 1901110 * 2
def baseEnd_1901110 : Nat := 650788804712774754721307

theorem tailTrace_1901110 : CollatzResearch.WordTrace tailWord_1901110 prefixEnd_1901110 650788804712774754721307 := by
  unfold tailWord_1901110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333698633913164286482299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46226118761740419055811189 4333698633913164286482299)
  ·
    refine ⟨6500547950869746429723449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333698633913164286482299 6500547950869746429723449)
    ·
      refine ⟨4875410963152309822292587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500547950869746429723449 4875410963152309822292587)
      ·
        refine ⟨7313116444728464733438881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875410963152309822292587 7313116444728464733438881)
        ·
          refine ⟨5484837333546348550079161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313116444728464733438881 5484837333546348550079161)
          ·
            refine ⟨4113628000159761412559371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484837333546348550079161 4113628000159761412559371)
            ·
              refine ⟨6170442000239642118839057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113628000159761412559371 6170442000239642118839057)
              ·
                refine ⟨4627831500179731589129293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170442000239642118839057 4627831500179731589129293)
                ·
                  refine ⟨1735436812567399345923485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4627831500179731589129293 1735436812567399345923485)
                  ·
                    refine ⟨650788804712774754721307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735436812567399345923485 650788804712774754721307)
                    ·
                      rfl

theorem cell22_1901110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1901110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901110 prefixEnd_1901110 := by exact prefixLift 1901110
  have htrace : WordTrace (prefixWord ++ tailWord_1901110) baseStart_1901110 baseEnd_1901110 := by
    simpa [prefixWord, tailWord_1901110, baseEnd_1901110] using wordTrace_append hprefix tailTrace_1901110
  have hstable : (prefixWord ++ tailWord_1901110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901110).length < 2 ^ (prefixWord ++ tailWord_1901110).sum := by decide
  have hdescent : baseEnd_1901110 < baseStart_1901110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901170 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1901170 : Nat := 118140960795 + 1901170 * 2 ^ 59
def prefixEnd_1901170 : Nat := 4983230072969 + 3 ^ 40 * 1901170 * 2
def baseEnd_1901170 : Nat := 650809343938954598221123

theorem tailTrace_1901170 : CollatzResearch.WordTrace tailWord_1901170 prefixEnd_1901170 650809343938954598221123 := by
  unfold tailWord_1901170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335341630598314707725241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46227577681595505887267309 17335341630598314707725241)
  ·
    refine ⟨13001506222948736030793931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335341630598314707725241 13001506222948736030793931)
    ·
      refine ⟨19502259334423104046190897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001506222948736030793931 19502259334423104046190897)
      ·
        refine ⟨14626694500817328034643173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19502259334423104046190897 14626694500817328034643173)
        ·
          refine ⟨2742505218903249006495595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14626694500817328034643173 2742505218903249006495595)
          ·
            refine ⟨4113757828354873509743393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742505218903249006495595 4113757828354873509743393)
            ·
              refine ⟨3085318371266155132307545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113757828354873509743393 3085318371266155132307545)
              ·
                refine ⟨2313988778449616349230659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085318371266155132307545 2313988778449616349230659)
                ·
                  refine ⟨3470983167674424523845989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313988778449616349230659 3470983167674424523845989)
                  ·
                    refine ⟨650809343938954598221123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470983167674424523845989 650809343938954598221123)
                    ·
                      rfl

theorem cell22_1901170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1901170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901170 prefixEnd_1901170 := by exact prefixLift 1901170
  have htrace : WordTrace (prefixWord ++ tailWord_1901170) baseStart_1901170 baseEnd_1901170 := by
    simpa [prefixWord, tailWord_1901170, baseEnd_1901170] using wordTrace_append hprefix tailTrace_1901170
  have hstable : (prefixWord ++ tailWord_1901170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901170).length < 2 ^ (prefixWord ++ tailWord_1901170).sum := by decide
  have hdescent : baseEnd_1901170 < baseStart_1901170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901198 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1901198 : Nat := 118140960795 + 1901198 * 2 ^ 59
def prefixEnd_1901198 : Nat := 4983230072969 + 3 ^ 40 * 1901198 * 2
def baseEnd_1901198 : Nat := 650818928911171858521037

theorem tailTrace_1901198 : CollatzResearch.WordTrace tailWord_1901198 prefixEnd_1901198 650818928911171858521037 := by
  unfold tailWord_1901198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667798470786477451615031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46228258510861213075280165 8667798470786477451615031)
  ·
    refine ⟨13001697706179716177422547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8667798470786477451615031 13001697706179716177422547)
    ·
      refine ⟨19502546559269574266133821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001697706179716177422547 19502546559269574266133821)
      ·
        refine ⟨7313454959726090349800183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19502546559269574266133821 7313454959726090349800183)
        ·
          refine ⟨10970182439589135524700275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313454959726090349800183 10970182439589135524700275)
          ·
            refine ⟨16455273659383703287050413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970182439589135524700275 16455273659383703287050413)
            ·
              refine ⟨6170727622268888732643905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455273659383703287050413 6170727622268888732643905)
              ·
                refine ⟨4628045716701666549482929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170727622268888732643905 4628045716701666549482929)
                ·
                  refine ⟨3471034287526249912112197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628045716701666549482929 3471034287526249912112197)
                  ·
                    refine ⟨650818928911171858521037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471034287526249912112197 650818928911171858521037)
                    ·
                      rfl

theorem cell22_1901198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1901198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901198 prefixEnd_1901198 := by exact prefixLift 1901198
  have htrace : WordTrace (prefixWord ++ tailWord_1901198) baseStart_1901198 baseEnd_1901198 := by
    simpa [prefixWord, tailWord_1901198, baseEnd_1901198] using wordTrace_append hprefix tailTrace_1901198
  have hstable : (prefixWord ++ tailWord_1901198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901198).length < 2 ^ (prefixWord ++ tailWord_1901198).sum := by decide
  have hdescent : baseEnd_1901198 < baseStart_1901198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901202 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1901202 : Nat := 118140960795 + 1901202 * 2 ^ 59
def prefixEnd_1901202 : Nat := 4983230072969 + 3 ^ 40 * 1901202 * 2
def baseEnd_1901202 : Nat := 216940099397639060473675

theorem tailTrace_1901202 : CollatzResearch.WordTrace tailWord_1901202 prefixEnd_1901202 216940099397639060473675 := by
  unfold tailWord_1901202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335633414569332074016465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46228355772184885530710573 17335633414569332074016465)
  ·
    refine ⟨13001725060926999055512349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335633414569332074016465 13001725060926999055512349)
    ·
      refine ⟨4875646897847624645817131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13001725060926999055512349 4875646897847624645817131)
      ·
        refine ⟨7313470346771436968725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875646897847624645817131 7313470346771436968725697)
        ·
          refine ⟨5485102760078577726544273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313470346771436968725697 5485102760078577726544273)
          ·
            refine ⟨4113827070058933294908205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485102760078577726544273 4113827070058933294908205)
            ·
              refine ⟨1542685151272099985590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4113827070058933294908205 1542685151272099985590577)
              ·
                refine ⟨1157013863454074989192933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542685151272099985590577 1157013863454074989192933)
                ·
                  refine ⟨216940099397639060473675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157013863454074989192933 216940099397639060473675)
                  ·
                    rfl

theorem cell22_1901202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1901202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901202 prefixEnd_1901202 := by exact prefixLift 1901202
  have htrace : WordTrace (prefixWord ++ tailWord_1901202) baseStart_1901202 baseEnd_1901202 := by
    simpa [prefixWord, tailWord_1901202, baseEnd_1901202] using wordTrace_append hprefix tailTrace_1901202
  have hstable : (prefixWord ++ tailWord_1901202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901202).length < 2 ^ (prefixWord ++ tailWord_1901202).sum := by decide
  have hdescent : baseEnd_1901202 < baseStart_1901202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901258 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1901258 : Nat := 118140960795 + 1901258 * 2 ^ 59
def prefixEnd_1901258 : Nat := 4983230072969 + 3 ^ 40 * 1901258 * 2
def baseEnd_1901258 : Nat := 216946489379117234006951

theorem tailTrace_1901258 : CollatzResearch.WordTrace tailWord_1901258 prefixEnd_1901258 216946489379117234006951 := by
  unfold tailWord_1901258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336144036518612465026107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46229717430716299906736285 17336144036518612465026107)
  ·
    refine ⟨26004216054777918697539161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17336144036518612465026107 26004216054777918697539161)
    ·
      refine ⟨19503162041083439023154371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26004216054777918697539161 19503162041083439023154371)
      ·
        refine ⟨29254743061625158534731557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503162041083439023154371 29254743061625158534731557)
        ·
          refine ⟨5485264324054717225262167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29254743061625158534731557 5485264324054717225262167)
          ·
            refine ⟨8227896486082075837893251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485264324054717225262167 8227896486082075837893251)
            ·
              refine ⟨12341844729123113756839877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227896486082075837893251 12341844729123113756839877)
              ·
                refine ⟨2314095886710583829407477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12341844729123113756839877 2314095886710583829407477)
                ·
                  refine ⟨216946489379117234006951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2314095886710583829407477 216946489379117234006951)
                  ·
                    rfl

theorem cell22_1901258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1901258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901258 prefixEnd_1901258 := by exact prefixLift 1901258
  have htrace : WordTrace (prefixWord ++ tailWord_1901258) baseStart_1901258 baseEnd_1901258 := by
    simpa [prefixWord, tailWord_1901258, baseEnd_1901258] using wordTrace_append hprefix tailTrace_1901258
  have hstable : (prefixWord ++ tailWord_1901258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901258).length < 2 ^ (prefixWord ++ tailWord_1901258).sum := by decide
  have hdescent : baseEnd_1901258 < baseStart_1901258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901262 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_1901262 : Nat := 118140960795 + 1901262 * 2 ^ 59
def prefixEnd_1901262 : Nat := 4983230072969 + 3 ^ 40 * 1901262 * 2
def baseEnd_1901262 : Nat := 650840837419097024920841

theorem tailTrace_1901262 : CollatzResearch.WordTrace tailWord_1901262 prefixEnd_1901262 650840837419097024920841 := by
  unfold tailWord_1901262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668090254757494817906255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46229814692039972362166693 8668090254757494817906255)
  ·
    refine ⟨13002135382136242226859383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8668090254757494817906255 13002135382136242226859383)
    ·
      refine ⟨19503203073204363340289075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002135382136242226859383 19503203073204363340289075)
      ·
        refine ⟨29254804609806545010433613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503203073204363340289075 29254804609806545010433613)
        ·
          refine ⟨10970551728677454378912605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29254804609806545010433613 10970551728677454378912605)
          ·
            refine ⟨4113956898254045392092227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10970551728677454378912605 4113956898254045392092227)
            ·
              refine ⟨6170935347381068088138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113956898254045392092227 6170935347381068088138341)
              ·
                refine ⟨1157050377633950266525939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6170935347381068088138341 1157050377633950266525939)
                ·
                  refine ⟨1735575566450925399788909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157050377633950266525939 1735575566450925399788909)
                  ·
                    refine ⟨650840837419097024920841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735575566450925399788909 650840837419097024920841)
                    ·
                      rfl

theorem cell22_1901262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_1901262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901262 prefixEnd_1901262 := by exact prefixLift 1901262
  have htrace : WordTrace (prefixWord ++ tailWord_1901262) baseStart_1901262 baseEnd_1901262 := by
    simpa [prefixWord, tailWord_1901262, baseEnd_1901262] using wordTrace_append hprefix tailTrace_1901262
  have hstable : (prefixWord ++ tailWord_1901262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901262).length < 2 ^ (prefixWord ++ tailWord_1901262).sum := by decide
  have hdescent : baseEnd_1901262 < baseStart_1901262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901320 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_1901320 : Nat := 118140960795 + 1901320 * 2 ^ 59
def prefixEnd_1901320 : Nat := 4983230072969 + 3 ^ 40 * 1901320 * 2
def baseEnd_1901320 : Nat := 216953564001468068990221

theorem tailTrace_1901320 : CollatzResearch.WordTrace tailWord_1901320 prefixEnd_1901320 216953564001468068990221 := by
  unfold tailWord_1901320
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673418735924917224430707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46231224981233222965907609 34673418735924917224430707)
  ·
    refine ⟨52010128103887375836646061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34673418735924917224430707 52010128103887375836646061)
    ·
      refine ⟨19503798038957765938742273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52010128103887375836646061 19503798038957765938742273)
      ·
        refine ⟨14627848529218324454056705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503798038957765938742273 14627848529218324454056705)
        ·
          refine ⟨10970886396913743340542529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627848529218324454056705 10970886396913743340542529)
          ·
            refine ⟨8228164797685307505406897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10970886396913743340542529 8228164797685307505406897)
            ·
              refine ⟨6171123598263980629055173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228164797685307505406897 6171123598263980629055173)
              ·
                refine ⟨1157085674674496367947845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6171123598263980629055173 1157085674674496367947845)
                ·
                  refine ⟨216953564001468068990221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157085674674496367947845 216953564001468068990221)
                  ·
                    rfl

theorem cell22_1901320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_1901320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901320 prefixEnd_1901320 := by exact prefixLift 1901320
  have htrace : WordTrace (prefixWord ++ tailWord_1901320) baseStart_1901320 baseEnd_1901320 := by
    simpa [prefixWord, tailWord_1901320, baseEnd_1901320] using wordTrace_append hprefix tailTrace_1901320
  have hstable : (prefixWord ++ tailWord_1901320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901320).length < 2 ^ (prefixWord ++ tailWord_1901320).sum := by decide
  have hdescent : baseEnd_1901320 < baseStart_1901320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901331 : List Nat := [1, 1, 1, 2, 1, 3, 4, 9]
def baseStart_1901331 : Nat := 118140960795 + 1901331 * 2 ^ 59
def prefixEnd_1901331 : Nat := 4983230072969 + 3 ^ 40 * 1901331 * 2
def baseEnd_1901331 : Nat := 72318273058800427216181

theorem tailTrace_1901331 : CollatzResearch.WordTrace tailWord_1901331 prefixEnd_1901331 72318273058800427216181 := by
  unfold tailWord_1901331
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347238674809983327511847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46231492449873322218341231 69347238674809983327511847)
  ·
    refine ⟨104020858012214974991267771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69347238674809983327511847 104020858012214974991267771)
    ·
      refine ⟨156031287018322462486901657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104020858012214974991267771 156031287018322462486901657)
      ·
        refine ⟨117023465263741846865176243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156031287018322462486901657 117023465263741846865176243)
        ·
          refine ⟨175535197895612770297764365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117023465263741846865176243 175535197895612770297764365)
          ·
            refine ⟨65825699210854788861661637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175535197895612770297764365 65825699210854788861661637)
            ·
              refine ⟨12342318602035272911561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65825699210854788861661637 12342318602035272911561557)
              ·
                refine ⟨72318273058800427216181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12342318602035272911561557 72318273058800427216181)
                ·
                  rfl

theorem cell22_1901331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_1901331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901331 prefixEnd_1901331 := by exact prefixLift 1901331
  have htrace : WordTrace (prefixWord ++ tailWord_1901331) baseStart_1901331 baseEnd_1901331 := by
    simpa [prefixWord, tailWord_1901331, baseEnd_1901331] using wordTrace_append hprefix tailTrace_1901331
  have hstable : (prefixWord ++ tailWord_1901331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901331).length < 2 ^ (prefixWord ++ tailWord_1901331).sum := by decide
  have hdescent : baseEnd_1901331 < baseStart_1901331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901474 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1901474 : Nat := 118140960795 + 1901474 * 2 ^ 59
def prefixEnd_1901474 : Nat := 4983230072969 + 3 ^ 40 * 1901474 * 2
def baseEnd_1901474 : Nat := 650913409351599138620191

theorem tailTrace_1901474 : CollatzResearch.WordTrace tailWord_1901474 prefixEnd_1901474 650913409351599138620191 := by
  unfold tailWord_1901474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17338113578322979687491869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46234969542194612499978317 17338113578322979687491869)
  ·
    refine ⟨6501792591871117382809451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17338113578322979687491869 6501792591871117382809451)
    ·
      refine ⟨9752688887806676074214177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501792591871117382809451 9752688887806676074214177)
      ·
        refine ⟨7314516665855007055660633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9752688887806676074214177 7314516665855007055660633)
        ·
          refine ⟨5485887499391255291745475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7314516665855007055660633 5485887499391255291745475)
          ·
            refine ⟨8228831249086882937618213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485887499391255291745475 8228831249086882937618213)
            ·
              refine ⟨1542905859203790550803415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8228831249086882937618213 1542905859203790550803415)
              ·
                refine ⟨2314358788805685826205123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542905859203790550803415 2314358788805685826205123)
                ·
                  refine ⟨3471538183208528739307685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314358788805685826205123 3471538183208528739307685)
                  ·
                    refine ⟨650913409351599138620191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471538183208528739307685 650913409351599138620191)
                    ·
                      rfl

theorem cell22_1901474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1901474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901474 prefixEnd_1901474 := by exact prefixLift 1901474
  have htrace : WordTrace (prefixWord ++ tailWord_1901474) baseStart_1901474 baseEnd_1901474 := by
    simpa [prefixWord, tailWord_1901474, baseEnd_1901474] using wordTrace_append hprefix tailTrace_1901474
  have hstable : (prefixWord ++ tailWord_1901474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901474).length < 2 ^ (prefixWord ++ tailWord_1901474).sum := by decide
  have hdescent : baseEnd_1901474 < baseStart_1901474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901504 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_1901504 : Nat := 118140960795 + 1901504 * 2 ^ 59
def prefixEnd_1901504 : Nat := 4983230072969 + 3 ^ 40 * 1901504 * 2
def baseEnd_1901504 : Nat := 650923678964689060370099

theorem tailTrace_1901504 : CollatzResearch.WordTrace tailWord_1901504 prefixEnd_1901504 650923678964689060370099 := by
  unfold tailWord_1901504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34676774251591616936779783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46235699002122155915706377 34676774251591616936779783)
  ·
    refine ⟨52015161377387425405169675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34676774251591616936779783 52015161377387425405169675)
    ·
      refine ⟨78022742066081138107754513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52015161377387425405169675 78022742066081138107754513)
      ·
        refine ⟨58517056549560853580815885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78022742066081138107754513 58517056549560853580815885)
        ·
          refine ⟨21943896206085320092805957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58517056549560853580815885 21943896206085320092805957)
          ·
            refine ⟨4114480538640997517401117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21943896206085320092805957 4114480538640997517401117)
            ·
              refine ⟨1542930201990374069025419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4114480538640997517401117 1542930201990374069025419)
              ·
                refine ⟨2314395302985561103538129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542930201990374069025419 2314395302985561103538129)
                ·
                  refine ⟨1735796477239170827653597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314395302985561103538129 1735796477239170827653597)
                  ·
                    refine ⟨650923678964689060370099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735796477239170827653597 650923678964689060370099)
                    ·
                      rfl

theorem cell22_1901504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_1901504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901504 prefixEnd_1901504 := by exact prefixLift 1901504
  have htrace : WordTrace (prefixWord ++ tailWord_1901504) baseStart_1901504 baseEnd_1901504 := by
    simpa [prefixWord, tailWord_1901504, baseEnd_1901504] using wordTrace_append hprefix tailTrace_1901504
  have hstable : (prefixWord ++ tailWord_1901504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901504).length < 2 ^ (prefixWord ++ tailWord_1901504).sum := by decide
  have hdescent : baseEnd_1901504 < baseStart_1901504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901600 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_1901600 : Nat := 118140960795 + 1901600 * 2 ^ 59
def prefixEnd_1901600 : Nat := 4983230072969 + 3 ^ 40 * 1901600 * 2
def baseEnd_1901600 : Nat := 650956541726576809969805

theorem tailTrace_1901600 : CollatzResearch.WordTrace tailWord_1901600 prefixEnd_1901600 650956541726576809969805 := by
  unfold tailWord_1901600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678524955417721134527127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46238033273890294846036169 34678524955417721134527127)
  ·
    refine ⟨52017787433126581701790691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34678524955417721134527127 52017787433126581701790691)
    ·
      refine ⟨78026681149689872552686037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52017787433126581701790691 78026681149689872552686037)
      ·
        refine ⟨1828750339445856387953579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78026681149689872552686037 1828750339445856387953579)
        ·
          refine ⟨2743125509168784581930369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828750339445856387953579 2743125509168784581930369)
          ·
            refine ⟨2057344131876588436447777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743125509168784581930369 2057344131876588436447777)
            ·
              refine ⟨1543008098907441327335833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057344131876588436447777 1543008098907441327335833)
              ·
                refine ⟨1157256074180580995501875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543008098907441327335833 1157256074180580995501875)
                ·
                  refine ⟨1735884111270871493252813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157256074180580995501875 1735884111270871493252813)
                  ·
                    refine ⟨650956541726576809969805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735884111270871493252813 650956541726576809969805)
                    ·
                      rfl

theorem cell22_1901600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_1901600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901600 prefixEnd_1901600 := by exact prefixLift 1901600
  have htrace : WordTrace (prefixWord ++ tailWord_1901600) baseStart_1901600 baseEnd_1901600 := by
    simpa [prefixWord, tailWord_1901600, baseEnd_1901600] using wordTrace_append hprefix tailTrace_1901600
  have hstable : (prefixWord ++ tailWord_1901600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901600).length < 2 ^ (prefixWord ++ tailWord_1901600).sum := by decide
  have hdescent : baseEnd_1901600 < baseStart_1901600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901605 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1901605 : Nat := 118140960795 + 1901605 * 2 ^ 59
def prefixEnd_1901605 : Nat := 4983230072969 + 3 ^ 40 * 1901605 * 2
def baseEnd_1901605 : Nat := 650958253328758463594789

theorem tailTrace_1901605 : CollatzResearch.WordTrace tailWord_1901605 prefixEnd_1901605 650958253328758463594789 := by
  unfold tailWord_1901605
  simp only [CollatzResearch.WordTrace]
  refine ⟨69357232275817328122986269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46238154850544885415324179 69357232275817328122986269)
  ·
    refine ⟨26008962103431498046119851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69357232275817328122986269 26008962103431498046119851)
    ·
      refine ⟨39013443155147247069179777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26008962103431498046119851 39013443155147247069179777)
      ·
        refine ⟨29260082366360435301884833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39013443155147247069179777 29260082366360435301884833)
        ·
          refine ⟨21945061774770326476413625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29260082366360435301884833 21945061774770326476413625)
          ·
            refine ⟨16458796331077744857310219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21945061774770326476413625 16458796331077744857310219)
            ·
              refine ⟨24688194496616617285965329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16458796331077744857310219 24688194496616617285965329)
              ·
                refine ⟨18516145872462462964473997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24688194496616617285965329 18516145872462462964473997)
                ·
                  refine ⟨6943554702173423611677749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18516145872462462964473997 6943554702173423611677749)
                  ·
                    refine ⟨650958253328758463594789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6943554702173423611677749 650958253328758463594789)
                    ·
                      rfl

theorem cell22_1901605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1901605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901605 prefixEnd_1901605 := by exact prefixLift 1901605
  have htrace : WordTrace (prefixWord ++ tailWord_1901605) baseStart_1901605 baseEnd_1901605 := by
    simpa [prefixWord, tailWord_1901605, baseEnd_1901605] using wordTrace_append hprefix tailTrace_1901605
  have hstable : (prefixWord ++ tailWord_1901605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901605).length < 2 ^ (prefixWord ++ tailWord_1901605).sum := by decide
  have hdescent : baseEnd_1901605 < baseStart_1901605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901637 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1901637 : Nat := 118140960795 + 1901637 * 2 ^ 59
def prefixEnd_1901637 : Nat := 4983230072969 + 3 ^ 40 * 1901637 * 2
def baseEnd_1901637 : Nat := 650969207582721046794691

theorem tailTrace_1901637 : CollatzResearch.WordTrace tailWord_1901637 prefixEnd_1901637 650969207582721046794691 := by
  unfold tailWord_1901637
  simp only [CollatzResearch.WordTrace]
  refine ⟨69358399411701397588151165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46238932941134265058767443 69358399411701397588151165)
  ·
    refine ⟨26009399779388024095556687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69358399411701397588151165 26009399779388024095556687)
    ·
      refine ⟨39014099669082036143335031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26009399779388024095556687 39014099669082036143335031)
      ·
        refine ⟨58521149503623054215002547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39014099669082036143335031 58521149503623054215002547)
        ·
          refine ⟨87781724255434581322503821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58521149503623054215002547 87781724255434581322503821)
          ·
            refine ⟨32918146595787967995938933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87781724255434581322503821 32918146595787967995938933)
            ·
              refine ⟨3086076243355121999619275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32918146595787967995938933 3086076243355121999619275)
              ·
                refine ⟨4629114365032682999428913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086076243355121999619275 4629114365032682999428913)
                ·
                  refine ⟨3471835773774512249571685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629114365032682999428913 3471835773774512249571685)
                  ·
                    refine ⟨650969207582721046794691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471835773774512249571685 650969207582721046794691)
                    ·
                      rfl

theorem cell22_1901637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1901637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901637 prefixEnd_1901637 := by exact prefixLift 1901637
  have htrace : WordTrace (prefixWord ++ tailWord_1901637) baseStart_1901637 baseEnd_1901637 := by
    simpa [prefixWord, tailWord_1901637, baseEnd_1901637] using wordTrace_append hprefix tailTrace_1901637
  have hstable : (prefixWord ++ tailWord_1901637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901637).length < 2 ^ (prefixWord ++ tailWord_1901637).sum := by decide
  have hdescent : baseEnd_1901637 < baseStart_1901637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901665 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1901665 : Nat := 118140960795 + 1901665 * 2 ^ 59
def prefixEnd_1901665 : Nat := 4983230072969 + 3 ^ 40 * 1901665 * 2
def baseEnd_1901665 : Nat := 650978792554938307094605

theorem tailTrace_1901665 : CollatzResearch.WordTrace tailWord_1901665 prefixEnd_1901665 650978792554938307094605 := by
  unfold tailWord_1901665
  simp only [CollatzResearch.WordTrace]
  refine ⟨69359420655599958370170449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46239613770399972246780299 69359420655599958370170449)
  ·
    refine ⟨52019565491699968777627837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69359420655599958370170449 52019565491699968777627837)
    ·
      refine ⟨19507337059387488291610439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52019565491699968777627837 19507337059387488291610439)
      ·
        refine ⟨29261005589081232437415659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19507337059387488291610439 29261005589081232437415659)
        ·
          refine ⟨43891508383621848656123489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29261005589081232437415659 43891508383621848656123489)
          ·
            refine ⟨32918631287716386492092617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43891508383621848656123489 32918631287716386492092617)
            ·
              refine ⟨24688973465787289869069463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32918631287716386492092617 24688973465787289869069463)
              ·
                refine ⟨37033460198680934803604195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24688973465787289869069463 37033460198680934803604195)
                ·
                  refine ⟨55550190298021402205406293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37033460198680934803604195 55550190298021402205406293)
                  ·
                    refine ⟨650978792554938307094605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55550190298021402205406293 650978792554938307094605)
                    ·
                      rfl

theorem cell22_1901665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1901665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901665 prefixEnd_1901665 := by exact prefixLift 1901665
  have htrace : WordTrace (prefixWord ++ tailWord_1901665) baseStart_1901665 baseEnd_1901665 := by
    simpa [prefixWord, tailWord_1901665, baseEnd_1901665] using wordTrace_append hprefix tailTrace_1901665
  have hstable : (prefixWord ++ tailWord_1901665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901665).length < 2 ^ (prefixWord ++ tailWord_1901665).sum := by decide
  have hdescent : baseEnd_1901665 < baseStart_1901665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901697 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 7]
def baseStart_1901697 : Nat := 118140960795 + 1901697 * 2 ^ 59
def prefixEnd_1901697 : Nat := 4983230072969 + 3 ^ 40 * 1901697 * 2
def baseEnd_1901697 : Nat := 216996582269633630098169

theorem tailTrace_1901697 : CollatzResearch.WordTrace tailWord_1901697 prefixEnd_1901697 216996582269633630098169 := by
  unfold tailWord_1901697
  simp only [CollatzResearch.WordTrace]
  refine ⟨69360587791484027835335345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46240391860989351890223563 69360587791484027835335345)
  ·
    refine ⟨52020440843613020876501509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69360587791484027835335345 52020440843613020876501509)
    ·
      refine ⟨9753832658177441414344033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52020440843613020876501509 9753832658177441414344033)
      ·
        refine ⟨7315374493633081060758025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9753832658177441414344033 7315374493633081060758025)
        ·
          refine ⟨5486530870224810795568519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7315374493633081060758025 5486530870224810795568519)
          ·
            refine ⟨8229796305337216193352779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486530870224810795568519 8229796305337216193352779)
            ·
              refine ⟨12344694458005824290029169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229796305337216193352779 12344694458005824290029169)
              ·
                refine ⟨9258520843504368217521877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344694458005824290029169 9258520843504368217521877)
                ·
                  refine ⟨216996582269633630098169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9258520843504368217521877 216996582269633630098169)
                  ·
                    rfl

theorem cell22_1901697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_1901697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901697 prefixEnd_1901697 := by exact prefixLift 1901697
  have htrace : WordTrace (prefixWord ++ tailWord_1901697) baseStart_1901697 baseEnd_1901697 := by
    simpa [prefixWord, tailWord_1901697, baseEnd_1901697] using wordTrace_append hprefix tailTrace_1901697
  have hstable : (prefixWord ++ tailWord_1901697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901697).length < 2 ^ (prefixWord ++ tailWord_1901697).sum := by decide
  have hdescent : baseEnd_1901697 < baseStart_1901697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901757 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1901757 : Nat := 118140960795 + 1901757 * 2 ^ 59
def prefixEnd_1901757 : Nat := 4983230072969 + 3 ^ 40 * 1901757 * 2
def baseEnd_1901757 : Nat := 651010286035080733794323

theorem tailTrace_1901757 : CollatzResearch.WordTrace tailWord_1901757 prefixEnd_1901757 651010286035080733794323 := by
  unfold tailWord_1901757
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362776171266658082519525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46241850780844438721679683 69362776171266658082519525)
  ·
    refine ⟨13005520532112498390472411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69362776171266658082519525 13005520532112498390472411)
    ·
      refine ⟨19508280798168747585708617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005520532112498390472411 19508280798168747585708617)
      ·
        refine ⟨14631210598626560689281463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19508280798168747585708617 14631210598626560689281463)
        ·
          refine ⟨21946815897939841033922195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631210598626560689281463 21946815897939841033922195)
          ·
            refine ⟨32920223846909761550883293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946815897939841033922195 32920223846909761550883293)
            ·
              refine ⟨12345083942591160581581235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32920223846909761550883293 12345083942591160581581235)
              ·
                refine ⟨18517625913886740872371853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12345083942591160581581235 18517625913886740872371853)
                ·
                  refine ⟨6944109717707527827139445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18517625913886740872371853 6944109717707527827139445)
                  ·
                    refine ⟨651010286035080733794323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6944109717707527827139445 651010286035080733794323)
                    ·
                      rfl

theorem cell22_1901757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1901757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901757 prefixEnd_1901757 := by exact prefixLift 1901757
  have htrace : WordTrace (prefixWord ++ tailWord_1901757) baseStart_1901757 baseEnd_1901757 := by
    simpa [prefixWord, tailWord_1901757, baseEnd_1901757] using wordTrace_append hprefix tailTrace_1901757
  have hstable : (prefixWord ++ tailWord_1901757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901757).length < 2 ^ (prefixWord ++ tailWord_1901757).sum := by decide
  have hdescent : baseEnd_1901757 < baseStart_1901757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901804 : List Nat := [2, 2, 1, 1, 2, 5, 3, 6]
def baseStart_1901804 : Nat := 118140960795 + 1901804 * 2 ^ 59
def prefixEnd_1901804 : Nat := 4983230072969 + 3 ^ 40 * 1901804 * 2
def baseEnd_1901804 : Nat := 72336263899509808652131

theorem tailTrace_1901804 : CollatzResearch.WordTrace tailWord_1901804 prefixEnd_1901804 72336263899509808652131 := by
  unfold tailWord_1901804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34682245201048192554740233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46242993601397590072986977 34682245201048192554740233)
  ·
    refine ⟨26011683900786144416055175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34682245201048192554740233 26011683900786144416055175)
    ·
      refine ⟨39017525851179216624082763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26011683900786144416055175 39017525851179216624082763)
      ·
        refine ⟨58526288776768824936124145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39017525851179216624082763 58526288776768824936124145)
        ·
          refine ⟨43894716582576618702093109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58526288776768824936124145 43894716582576618702093109)
          ·
            refine ⟨4115129679616558003321229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43894716582576618702093109 4115129679616558003321229)
            ·
              refine ⟨1543173629856209251245461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4115129679616558003321229 1543173629856209251245461)
              ·
                refine ⟨72336263899509808652131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1543173629856209251245461 72336263899509808652131)
                ·
                  rfl

theorem cell22_1901804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_1901804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901804 prefixEnd_1901804 := by exact prefixLift 1901804
  have htrace : WordTrace (prefixWord ++ tailWord_1901804) baseStart_1901804 baseEnd_1901804 := by
    simpa [prefixWord, tailWord_1901804, baseEnd_1901804] using wordTrace_append hprefix tailTrace_1901804
  have hstable : (prefixWord ++ tailWord_1901804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901804).length < 2 ^ (prefixWord ++ tailWord_1901804).sum := by decide
  have hdescent : baseEnd_1901804 < baseStart_1901804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901836 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_1901836 : Nat := 118140960795 + 1901836 * 2 ^ 59
def prefixEnd_1901836 : Nat := 4983230072969 + 3 ^ 40 * 1901836 * 2
def baseEnd_1901836 : Nat := 651037329349550861069081

theorem tailTrace_1901836 : CollatzResearch.WordTrace tailWord_1901836 prefixEnd_1901836 651037329349550861069081 := by
  unfold tailWord_1901836
  simp only [CollatzResearch.WordTrace]
  refine ⟨34682828768990227287322681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46243771691986969716430241 34682828768990227287322681)
  ·
    refine ⟨26012121576742670465492011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34682828768990227287322681 26012121576742670465492011)
    ·
      refine ⟨39018182365114005698238017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012121576742670465492011 39018182365114005698238017)
      ·
        refine ⟨29263636773835504273678513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39018182365114005698238017 29263636773835504273678513)
        ·
          refine ⟨21947727580376628205258885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29263636773835504273678513 21947727580376628205258885)
          ·
            refine ⟨4115198921320617788486041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21947727580376628205258885 4115198921320617788486041)
            ·
              refine ⟨3086399190990463341364531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115198921320617788486041 3086399190990463341364531)
              ·
                refine ⟨4629598786485695012046797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086399190990463341364531 4629598786485695012046797)
                ·
                  refine ⟨1736099544932135629517549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4629598786485695012046797 1736099544932135629517549)
                  ·
                    refine ⟨651037329349550861069081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736099544932135629517549 651037329349550861069081)
                    ·
                      rfl

theorem cell22_1901836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_1901836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901836 prefixEnd_1901836 := by exact prefixLift 1901836
  have htrace : WordTrace (prefixWord ++ tailWord_1901836) baseStart_1901836 baseEnd_1901836 := by
    simpa [prefixWord, tailWord_1901836, baseEnd_1901836] using wordTrace_append hprefix tailTrace_1901836
  have hstable : (prefixWord ++ tailWord_1901836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901836).length < 2 ^ (prefixWord ++ tailWord_1901836).sum := by decide
  have hdescent : baseEnd_1901836 < baseStart_1901836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901842 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1901842 : Nat := 118140960795 + 1901842 * 2 ^ 59
def prefixEnd_1901842 : Nat := 4983230072969 + 3 ^ 40 * 1901842 * 2
def baseEnd_1901842 : Nat := 651039383272168845419063

theorem tailTrace_1901842 : CollatzResearch.WordTrace tailWord_1901842 prefixEnd_1901842 651039383272168845419063 := by
  unfold tailWord_1901842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17341469093989679399840945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46243917583972478399575853 17341469093989679399840945)
  ·
    refine ⟨13006101820492259549880709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17341469093989679399840945 13006101820492259549880709)
    ·
      refine ⟨2438644091342298665602633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13006101820492259549880709 2438644091342298665602633)
      ·
        refine ⟨1828983068506723999201975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2438644091342298665602633 1828983068506723999201975)
        ·
          refine ⟨2743474602760085998802963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828983068506723999201975 2743474602760085998802963)
          ·
            refine ⟨4115211904140128998204445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743474602760085998802963 4115211904140128998204445)
            ·
              refine ⟨1543204464052548374326667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4115211904140128998204445 1543204464052548374326667)
              ·
                refine ⟨2314806696078822561490001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543204464052548374326667 2314806696078822561490001)
                ·
                  refine ⟨1736105022059116921117501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314806696078822561490001 1736105022059116921117501)
                  ·
                    refine ⟨651039383272168845419063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736105022059116921117501 651039383272168845419063)
                    ·
                      rfl

theorem cell22_1901842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1901842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901842 prefixEnd_1901842 := by exact prefixLift 1901842
  have htrace : WordTrace (prefixWord ++ tailWord_1901842) baseStart_1901842 baseEnd_1901842 := by
    simpa [prefixWord, tailWord_1901842, baseEnd_1901842] using wordTrace_append hprefix tailTrace_1901842
  have hstable : (prefixWord ++ tailWord_1901842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901842).length < 2 ^ (prefixWord ++ tailWord_1901842).sum := by decide
  have hdescent : baseEnd_1901842 < baseStart_1901842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901930 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1901930 : Nat := 118140960795 + 1901930 * 2 ^ 59
def prefixEnd_1901930 : Nat := 4983230072969 + 3 ^ 40 * 1901930 * 2
def baseEnd_1901930 : Nat := 651069507470565949218793

theorem tailTrace_1901930 : CollatzResearch.WordTrace tailWord_1901930 prefixEnd_1901930 651069507470565949218793 := by
  unfold tailWord_1901930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342271499909977157141811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46246057333093272419044829 17342271499909977157141811)
  ·
    refine ⟨26013407249864965735712717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17342271499909977157141811 26013407249864965735712717)
    ·
      refine ⟨9755027718699362150892269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26013407249864965735712717 9755027718699362150892269)
      ·
        refine ⟨3658135394512260806584601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9755027718699362150892269 3658135394512260806584601)
        ·
          refine ⟨2743601545884195604938451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658135394512260806584601 2743601545884195604938451)
          ·
            refine ⟨4115402318826293407407677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743601545884195604938451 4115402318826293407407677)
            ·
              refine ⟨1543275869559860027777879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4115402318826293407407677 1543275869559860027777879)
              ·
                refine ⟨2314913804339790041666819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543275869559860027777879 2314913804339790041666819)
                ·
                  refine ⟨3472370706509685062500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314913804339790041666819 3472370706509685062500229)
                  ·
                    refine ⟨651069507470565949218793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472370706509685062500229 651069507470565949218793)
                    ·
                      rfl

theorem cell22_1901930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1901930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901930 prefixEnd_1901930 := by exact prefixLift 1901930
  have htrace : WordTrace (prefixWord ++ tailWord_1901930) baseStart_1901930 baseEnd_1901930 := by
    simpa [prefixWord, tailWord_1901930, baseEnd_1901930] using wordTrace_append hprefix tailTrace_1901930
  have hstable : (prefixWord ++ tailWord_1901930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901930).length < 2 ^ (prefixWord ++ tailWord_1901930).sum := by decide
  have hdescent : baseEnd_1901930 < baseStart_1901930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901956 : List Nat := [2, 3, 2, 1, 1, 5, 1, 7]
def baseStart_1901956 : Nat := 118140960795 + 1901956 * 2 ^ 59
def prefixEnd_1901956 : Nat := 4983230072969 + 3 ^ 40 * 1901956 * 2
def baseEnd_1901956 : Nat := 72342045311323394229857

theorem tailTrace_1901956 : CollatzResearch.WordTrace tailWord_1901956 prefixEnd_1901956 72342045311323394229857 := by
  unfold tailWord_1901956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685017148772857534506861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46246689531697143379342481 34685017148772857534506861)
  ·
    refine ⟨13006881430789821575440073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34685017148772857534506861 13006881430789821575440073)
    ·
      refine ⟨9755161073092366181580055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006881430789821575440073 9755161073092366181580055)
      ·
        refine ⟨14632741609638549272370083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755161073092366181580055 14632741609638549272370083)
        ·
          refine ⟨21949112414457823908555125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632741609638549272370083 21949112414457823908555125)
          ·
            refine ⟨2057729288855420991427043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21949112414457823908555125 2057729288855420991427043)
            ·
              refine ⟨3086593933283131487140565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057729288855420991427043 3086593933283131487140565)
              ·
                refine ⟨72342045311323394229857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3086593933283131487140565 72342045311323394229857)
                ·
                  rfl

theorem cell22_1901956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_1901956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901956 prefixEnd_1901956 := by exact prefixLift 1901956
  have htrace : WordTrace (prefixWord ++ tailWord_1901956) baseStart_1901956 baseEnd_1901956 := by
    simpa [prefixWord, tailWord_1901956, baseEnd_1901956] using wordTrace_append hprefix tailTrace_1901956
  have hstable : (prefixWord ++ tailWord_1901956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901956).length < 2 ^ (prefixWord ++ tailWord_1901956).sum := by decide
  have hdescent : baseEnd_1901956 < baseStart_1901956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901984 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_1901984 : Nat := 118140960795 + 1901984 * 2 ^ 59
def prefixEnd_1901984 : Nat := 4983230072969 + 3 ^ 40 * 1901984 * 2
def baseEnd_1901984 : Nat := 217029330924709269456209

theorem tailTrace_1901984 : CollatzResearch.WordTrace tailWord_1901984 prefixEnd_1901984 217029330924709269456209 := by
  unfold tailWord_1901984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685527770722137925516503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46247370360962850567355337 34685527770722137925516503)
  ·
    refine ⟨52028291656083206888274755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34685527770722137925516503 52028291656083206888274755)
    ·
      refine ⟨78042437484124810332412133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52028291656083206888274755 78042437484124810332412133)
      ·
        refine ⟨14632957028273401937327275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78042437484124810332412133 14632957028273401937327275)
        ·
          refine ⟨21949435542410102905990913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632957028273401937327275 21949435542410102905990913)
          ·
            refine ⟨16462076656807577179493185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21949435542410102905990913 16462076656807577179493185)
            ·
              refine ⟨12346557492605682884619889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16462076656807577179493185 12346557492605682884619889)
              ·
                refine ⟨9259918119454262163464917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12346557492605682884619889 9259918119454262163464917)
                ·
                  refine ⟨217029330924709269456209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9259918119454262163464917 217029330924709269456209)
                  ·
                    rfl

theorem cell22_1901984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_1901984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1901984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1901984 prefixEnd_1901984 := by exact prefixLift 1901984
  have htrace : WordTrace (prefixWord ++ tailWord_1901984) baseStart_1901984 baseEnd_1901984 := by
    simpa [prefixWord, tailWord_1901984, baseEnd_1901984] using wordTrace_append hprefix tailTrace_1901984
  have hstable : (prefixWord ++ tailWord_1901984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901984).length < 2 ^ (prefixWord ++ tailWord_1901984).sum := by decide
  have hdescent : baseEnd_1901984 < baseStart_1901984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902005 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1902005 : Nat := 118140960795 + 1902005 * 2 ^ 59
def prefixEnd_1902005 : Nat := 4983230072969 + 3 ^ 40 * 1902005 * 2
def baseEnd_1902005 : Nat := 651095181503290753593563

theorem tailTrace_1902005 : CollatzResearch.WordTrace tailWord_1902005 prefixEnd_1902005 651095181503290753593563 := by
  unfold tailWord_1902005
  simp only [CollatzResearch.WordTrace]
  refine ⟨69371821474368196437547469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46247880982912130958364979 69371821474368196437547469)
  ·
    refine ⟨26014433052888073664080301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69371821474368196437547469 26014433052888073664080301)
    ·
      refine ⟨9755412394833027624030113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26014433052888073664080301 9755412394833027624030113)
      ·
        refine ⟨7316559296124770718022585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9755412394833027624030113 7316559296124770718022585)
        ·
          refine ⟨5487419472093578038516939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7316559296124770718022585 5487419472093578038516939)
          ·
            refine ⟨8231129208140367057775409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487419472093578038516939 8231129208140367057775409)
            ·
              refine ⟨6173346906105275293331557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8231129208140367057775409 6173346906105275293331557)
              ·
                refine ⟨1157502544894739117499667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6173346906105275293331557 1157502544894739117499667)
                ·
                  refine ⟨1736253817342108676249501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157502544894739117499667 1736253817342108676249501)
                  ·
                    refine ⟨651095181503290753593563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736253817342108676249501 651095181503290753593563)
                    ·
                      rfl

theorem cell22_1902005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1902005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902005 prefixEnd_1902005 := by exact prefixLift 1902005
  have htrace : WordTrace (prefixWord ++ tailWord_1902005) baseStart_1902005 baseEnd_1902005 := by
    simpa [prefixWord, tailWord_1902005, baseEnd_1902005] using wordTrace_append hprefix tailTrace_1902005
  have hstable : (prefixWord ++ tailWord_1902005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902005).length < 2 ^ (prefixWord ++ tailWord_1902005).sum := by decide
  have hdescent : baseEnd_1902005 < baseStart_1902005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902031 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 1, 4]
def baseStart_1902031 : Nat := 118140960795 + 1902031 * 2 ^ 59
def prefixEnd_1902031 : Nat := 4983230072969 + 3 ^ 40 * 1902031 * 2
def baseEnd_1902031 : Nat := 651104081834635352443483

theorem tailTrace_1902031 : CollatzResearch.WordTrace tailWord_1902031 prefixEnd_1902031 651104081834635352443483 := by
  unfold tailWord_1902031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69372769772274002877993947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46248513181516001918662631 69372769772274002877993947)
  ·
    refine ⟨104059154658411004316990921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69372769772274002877993947 104059154658411004316990921)
    ·
      refine ⟨78044365993808253237743191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104059154658411004316990921 78044365993808253237743191)
      ·
        refine ⟨117066548990712379856614787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78044365993808253237743191 117066548990712379856614787)
        ·
          refine ⟨175599823486068569784922181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117066548990712379856614787 175599823486068569784922181)
          ·
            refine ⟨32924966903637856834672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175599823486068569784922181 32924966903637856834672909)
            ·
              refine ⟨12346862588864196313002341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32924966903637856834672909 12346862588864196313002341)
              ·
                refine ⟨2315036735412036808687939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12346862588864196313002341 2315036735412036808687939)
                ·
                  refine ⟨3472555103118055213031909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315036735412036808687939 3472555103118055213031909)
                  ·
                    refine ⟨651104081834635352443483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472555103118055213031909 651104081834635352443483)
                    ·
                      rfl

theorem cell22_1902031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_1902031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902031 prefixEnd_1902031 := by exact prefixLift 1902031
  have htrace : WordTrace (prefixWord ++ tailWord_1902031) baseStart_1902031 baseEnd_1902031 := by
    simpa [prefixWord, tailWord_1902031, baseEnd_1902031] using wordTrace_append hprefix tailTrace_1902031
  have hstable : (prefixWord ++ tailWord_1902031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902031).length < 2 ^ (prefixWord ++ tailWord_1902031).sum := by decide
  have hdescent : baseEnd_1902031 < baseStart_1902031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902059 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_1902059 : Nat := 118140960795 + 1902059 * 2 ^ 59
def prefixEnd_1902059 : Nat := 4983230072969 + 3 ^ 40 * 1902059 * 2
def baseEnd_1902059 : Nat := 651113666806852612743397

theorem tailTrace_1902059 : CollatzResearch.WordTrace tailWord_1902059 prefixEnd_1902059 651113666806852612743397 := by
  unfold tailWord_1902059
  simp only [CollatzResearch.WordTrace]
  refine ⟨69373791016172563660013231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46249194010781709106675487 69373791016172563660013231)
  ·
    refine ⟨104060686524258845490019847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69373791016172563660013231 104060686524258845490019847)
    ·
      refine ⟨156091029786388268235029771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104060686524258845490019847 156091029786388268235029771)
      ·
        refine ⟨234136544679582402352544657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156091029786388268235029771 234136544679582402352544657)
        ·
          refine ⟨175602408509686801764408493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234136544679582402352544657 175602408509686801764408493)
          ·
            refine ⟨65850903191132550661653185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175602408509686801764408493 65850903191132550661653185)
            ·
              refine ⟨49388177393349412996239889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65850903191132550661653185 49388177393349412996239889)
              ·
                refine ⟨37041133045012059747179917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49388177393349412996239889 37041133045012059747179917)
                ·
                  refine ⟨13890424891879522405192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37041133045012059747179917 13890424891879522405192469)
                  ·
                    refine ⟨651113666806852612743397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13890424891879522405192469 651113666806852612743397)
                    ·
                      rfl

theorem cell22_1902059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_1902059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902059 prefixEnd_1902059 := by exact prefixLift 1902059
  have htrace : WordTrace (prefixWord ++ tailWord_1902059) baseStart_1902059 baseEnd_1902059 := by
    simpa [prefixWord, tailWord_1902059, baseEnd_1902059] using wordTrace_append hprefix tailTrace_1902059
  have hstable : (prefixWord ++ tailWord_1902059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902059).length < 2 ^ (prefixWord ++ tailWord_1902059).sum := by decide
  have hdescent : baseEnd_1902059 < baseStart_1902059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902082 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1902082 : Nat := 118140960795 + 1902082 * 2 ^ 59
def prefixEnd_1902082 : Nat := 4983230072969 + 3 ^ 40 * 1902082 * 2
def baseEnd_1902082 : Nat := 651121540176888219418327

theorem tailTrace_1902082 : CollatzResearch.WordTrace tailWord_1902082 prefixEnd_1902082 651121540176888219418327 := by
  unfold tailWord_1902082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343657473772309647025125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46249753263392825725400333 17343657473772309647025125)
  ·
    refine ⟨3251935776332308058817211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17343657473772309647025125 3251935776332308058817211)
    ·
      refine ⟨4877903664498462088225817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3251935776332308058817211 4877903664498462088225817)
      ·
        refine ⟨3658427748373846566169363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4877903664498462088225817 3658427748373846566169363)
        ·
          refine ⟨5487641622560769849254045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658427748373846566169363 5487641622560769849254045)
          ·
            refine ⟨2057865608460288693470267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5487641622560769849254045 2057865608460288693470267)
            ·
              refine ⟨3086798412690433040205401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057865608460288693470267 3086798412690433040205401)
              ·
                refine ⟨2315098809517824780154051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086798412690433040205401 2315098809517824780154051)
                ·
                  refine ⟨3472648214276737170231077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315098809517824780154051 3472648214276737170231077)
                  ·
                    refine ⟨651121540176888219418327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472648214276737170231077 651121540176888219418327)
                    ·
                      rfl

theorem cell22_1902082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1902082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902082 prefixEnd_1902082 := by exact prefixLift 1902082
  have htrace : WordTrace (prefixWord ++ tailWord_1902082) baseStart_1902082 baseEnd_1902082 := by
    simpa [prefixWord, tailWord_1902082, baseEnd_1902082] using wordTrace_append hprefix tailTrace_1902082
  have hstable : (prefixWord ++ tailWord_1902082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902082).length < 2 ^ (prefixWord ++ tailWord_1902082).sum := by decide
  have hdescent : baseEnd_1902082 < baseStart_1902082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902140 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_1902140 : Nat := 118140960795 + 1902140 * 2 ^ 59
def prefixEnd_1902140 : Nat := 4983230072969 + 3 ^ 40 * 1902140 * 2
def baseEnd_1902140 : Nat := 651141394762195401468149

theorem tailTrace_1902140 : CollatzResearch.WordTrace tailWord_1902140 prefixEnd_1902140 651141394762195401468149 := by
  unfold tailWord_1902140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34688372664439557246855937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46251163552586076329141249 34688372664439557246855937)
  ·
    refine ⟨26016279498329667935141953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34688372664439557246855937 26016279498329667935141953)
    ·
      refine ⟨19512209623747250951356465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26016279498329667935141953 19512209623747250951356465)
      ·
        refine ⟨14634157217810438213517349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19512209623747250951356465 14634157217810438213517349)
        ·
          refine ⟨2743904478339457165034503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14634157217810438213517349 2743904478339457165034503)
          ·
            refine ⟨4115856717509185747551755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743904478339457165034503 4115856717509185747551755)
            ·
              refine ⟨6173785076263778621327633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115856717509185747551755 6173785076263778621327633)
              ·
                refine ⟨4630338807197833965995725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173785076263778621327633 4630338807197833965995725)
                ·
                  refine ⟨1736377052699187737248397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4630338807197833965995725 1736377052699187737248397)
                  ·
                    refine ⟨651141394762195401468149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736377052699187737248397 651141394762195401468149)
                    ·
                      rfl

theorem cell22_1902140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_1902140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902140 prefixEnd_1902140 := by exact prefixLift 1902140
  have htrace : WordTrace (prefixWord ++ tailWord_1902140) baseStart_1902140 baseEnd_1902140 := by
    simpa [prefixWord, tailWord_1902140, baseEnd_1902140] using wordTrace_append hprefix tailTrace_1902140
  have hstable : (prefixWord ++ tailWord_1902140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902140).length < 2 ^ (prefixWord ++ tailWord_1902140).sum := by decide
  have hdescent : baseEnd_1902140 < baseStart_1902140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902213 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_1902213 : Nat := 118140960795 + 1902213 * 2 ^ 59
def prefixEnd_1902213 : Nat := 4983230072969 + 3 ^ 40 * 1902213 * 2
def baseEnd_1902213 : Nat := 651166384154047544392925

theorem tailTrace_1902213 : CollatzResearch.WordTrace tailWord_1902213 prefixEnd_1902213 651166384154047544392925 := by
  unfold tailWord_1902213
  simp only [CollatzResearch.WordTrace]
  refine ⟨69379407857614647961119293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46252938571743098640746195 69379407857614647961119293)
  ·
    refine ⟨26017277946605492985419735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69379407857614647961119293 26017277946605492985419735)
    ·
      refine ⟨39025916919908239478129603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26017277946605492985419735 39025916919908239478129603)
      ·
        refine ⟨58538875379862359217194405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39025916919908239478129603 58538875379862359217194405)
        ·
          refine ⟨10976039133724192353223951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58538875379862359217194405 10976039133724192353223951)
          ·
            refine ⟨16464058700586288529835927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976039133724192353223951 16464058700586288529835927)
            ·
              refine ⟨24696088050879432794753891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464058700586288529835927 24696088050879432794753891)
              ·
                refine ⟨37044132076319149192130837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24696088050879432794753891 37044132076319149192130837)
                ·
                  refine ⟨1736443691077460118381133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37044132076319149192130837 1736443691077460118381133)
                  ·
                    refine ⟨651166384154047544392925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736443691077460118381133 651166384154047544392925)
                    ·
                      rfl

theorem cell22_1902213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_1902213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902213 prefixEnd_1902213 := by exact prefixLift 1902213
  have htrace : WordTrace (prefixWord ++ tailWord_1902213) baseStart_1902213 baseEnd_1902213 := by
    simpa [prefixWord, tailWord_1902213, baseEnd_1902213] using wordTrace_append hprefix tailTrace_1902213
  have hstable : (prefixWord ++ tailWord_1902213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902213).length < 2 ^ (prefixWord ++ tailWord_1902213).sum := by decide
  have hdescent : baseEnd_1902213 < baseStart_1902213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902215 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 4]
def baseStart_1902215 : Nat := 118140960795 + 1902215 * 2 ^ 59
def prefixEnd_1902215 : Nat := 4983230072969 + 3 ^ 40 * 1902215 * 2
def baseEnd_1902215 : Nat := 217055689598306735280973

theorem tailTrace_1902215 : CollatzResearch.WordTrace tailWord_1902215 prefixEnd_1902215 217055689598306735280973 := by
  unfold tailWord_1902215
  simp only [CollatzResearch.WordTrace]
  refine ⟨69379480803607402302692099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46252987202404934868461399 69379480803607402302692099)
  ·
    refine ⟨104069221205411103454038149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69379480803607402302692099 104069221205411103454038149)
    ·
      refine ⟨19512978976014581897632153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104069221205411103454038149 19512978976014581897632153)
      ·
        refine ⟨14634734232010936423224115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19512978976014581897632153 14634734232010936423224115)
        ·
          refine ⟨21952101348016404634836173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14634734232010936423224115 21952101348016404634836173)
          ·
            refine ⟨8232038005506151738063565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21952101348016404634836173 8232038005506151738063565)
            ·
              refine ⟨3087014252064806901773837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8232038005506151738063565 3087014252064806901773837)
              ·
                refine ⟨1157630344524302588165189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087014252064806901773837 1157630344524302588165189)
                ·
                  refine ⟨217055689598306735280973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157630344524302588165189 217055689598306735280973)
                  ·
                    rfl

theorem cell22_1902215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 4].length) (baseStart_1902215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902215 prefixEnd_1902215 := by exact prefixLift 1902215
  have htrace : WordTrace (prefixWord ++ tailWord_1902215) baseStart_1902215 baseEnd_1902215 := by
    simpa [prefixWord, tailWord_1902215, baseEnd_1902215] using wordTrace_append hprefix tailTrace_1902215
  have hstable : (prefixWord ++ tailWord_1902215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902215).length < 2 ^ (prefixWord ++ tailWord_1902215).sum := by decide
  have hdescent : baseEnd_1902215 < baseStart_1902215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902232 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_1902232 : Nat := 118140960795 + 1902232 * 2 ^ 59
def prefixEnd_1902232 : Nat := 4983230072969 + 3 ^ 40 * 1902232 * 2
def baseEnd_1902232 : Nat := 217057629414112609389289

theorem tailTrace_1902232 : CollatzResearch.WordTrace tailWord_1902232 prefixEnd_1902232 217057629414112609389289 := by
  unfold tailWord_1902232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690050422272907103030475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46253400563030542804040633 34690050422272907103030475)
  ·
    refine ⟨52035075633409360654545713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34690050422272907103030475 52035075633409360654545713)
    ·
      refine ⟨39026306725057020490909285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52035075633409360654545713 39026306725057020490909285)
      ·
        refine ⟨7317432510948191342045491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39026306725057020490909285 7317432510948191342045491)
        ·
          refine ⟨10976148766422287013068237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317432510948191342045491 10976148766422287013068237)
          ·
            refine ⟨4116055787408357629900589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10976148766422287013068237 4116055787408357629900589)
            ·
              refine ⟨1543520920278134111212721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4116055787408357629900589 1543520920278134111212721)
              ·
                refine ⟨1157640690208600583409541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543520920278134111212721 1157640690208600583409541)
                ·
                  refine ⟨217057629414112609389289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157640690208600583409541 217057629414112609389289)
                  ·
                    rfl

theorem cell22_1902232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_1902232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902232 prefixEnd_1902232 := by exact prefixLift 1902232
  have htrace : WordTrace (prefixWord ++ tailWord_1902232) baseStart_1902232 baseEnd_1902232 := by
    simpa [prefixWord, tailWord_1902232, baseEnd_1902232] using wordTrace_append hprefix tailTrace_1902232
  have hstable : (prefixWord ++ tailWord_1902232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902232).length < 2 ^ (prefixWord ++ tailWord_1902232).sum := by decide
  have hdescent : baseEnd_1902232 < baseStart_1902232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902262 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1902262 : Nat := 118140960795 + 1902262 * 2 ^ 59
def prefixEnd_1902262 : Nat := 4983230072969 + 3 ^ 40 * 1902262 * 2
def baseEnd_1902262 : Nat := 651183157855427749917775

theorem tailTrace_1902262 : CollatzResearch.WordTrace tailWord_1902262 prefixEnd_1902262 651183157855427749917775 := by
  unfold tailWord_1902262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336324689652320583103315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46254130022958086219768693 4336324689652320583103315)
  ·
    refine ⟨6504487034478480874654973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4336324689652320583103315 6504487034478480874654973)
    ·
      refine ⟨2439182637929430327995615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6504487034478480874654973 2439182637929430327995615)
      ·
        refine ⟨3658773956894145491993423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439182637929430327995615 3658773956894145491993423)
        ·
          refine ⟨5488160935341218237990135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658773956894145491993423 5488160935341218237990135)
          ·
            refine ⟨8232241403011827356985203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488160935341218237990135 8232241403011827356985203)
            ·
              refine ⟨12348362104517741035477805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232241403011827356985203 12348362104517741035477805)
              ·
                refine ⟨4630635789194152888304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12348362104517741035477805 4630635789194152888304177)
                ·
                  refine ⟨3472976841895614666228133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630635789194152888304177 3472976841895614666228133)
                  ·
                    refine ⟨651183157855427749917775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472976841895614666228133 651183157855427749917775)
                    ·
                      rfl

theorem cell22_1902262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1902262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902262 prefixEnd_1902262 := by exact prefixLift 1902262
  have htrace : WordTrace (prefixWord ++ tailWord_1902262) baseStart_1902262 baseEnd_1902262 := by
    simpa [prefixWord, tailWord_1902262, baseEnd_1902262] using wordTrace_append hprefix tailTrace_1902262
  have hstable : (prefixWord ++ tailWord_1902262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902262).length < 2 ^ (prefixWord ++ tailWord_1902262).sum := by decide
  have hdescent : baseEnd_1902262 < baseStart_1902262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902294 : List Nat := [5, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1902294 : Nat := 118140960795 + 1902294 * 2 ^ 59
def prefixEnd_1902294 : Nat := 4983230072969 + 3 ^ 40 * 1902294 * 2
def baseEnd_1902294 : Nat := 72354901345487814790853

theorem tailTrace_1902294 : CollatzResearch.WordTrace tailWord_1902294 prefixEnd_1902294 72354901345487814790853 := by
  unfold tailWord_1902294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336397635645074924676121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46254908113547465863211957 4336397635645074924676121)
  ·
    refine ⟨3252298226733806193507091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336397635645074924676121 3252298226733806193507091)
    ·
      refine ⟨4878447340100709290260637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252298226733806193507091 4878447340100709290260637)
      ·
        refine ⟨1829417752537765983847739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4878447340100709290260637 1829417752537765983847739)
        ·
          refine ⟨2744126628806648975771609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829417752537765983847739 2744126628806648975771609)
          ·
            refine ⟨2058094971604986731828707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744126628806648975771609 2058094971604986731828707)
            ·
              refine ⟨3087142457407480097743061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058094971604986731828707 3087142457407480097743061)
              ·
                refine ⟨72354901345487814790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3087142457407480097743061 72354901345487814790853)
                ·
                  rfl

theorem cell22_1902294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1902294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902294 prefixEnd_1902294 := by exact prefixLift 1902294
  have htrace : WordTrace (prefixWord ++ tailWord_1902294) baseStart_1902294 baseEnd_1902294 := by
    simpa [prefixWord, tailWord_1902294, baseEnd_1902294] using wordTrace_append hprefix tailTrace_1902294
  have hstable : (prefixWord ++ tailWord_1902294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902294).length < 2 ^ (prefixWord ++ tailWord_1902294).sum := by decide
  have hdescent : baseEnd_1902294 < baseStart_1902294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902303 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_1902303 : Nat := 118140960795 + 1902303 * 2 ^ 59
def prefixEnd_1902303 : Nat := 4983230072969 + 3 ^ 40 * 1902303 * 2
def baseEnd_1902303 : Nat := 651197192993317309642649

theorem tailTrace_1902303 : CollatzResearch.WordTrace tailWord_1902303 prefixEnd_1902303 651197192993317309642649 := by
  unfold tailWord_1902303
  simp only [CollatzResearch.WordTrace]
  refine ⟨69382690427288593331895563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46255126951525728887930375 69382690427288593331895563)
  ·
    refine ⟨104074035640932889997843345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69382690427288593331895563 104074035640932889997843345)
    ·
      refine ⟨78055526730699667498382509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104074035640932889997843345 78055526730699667498382509)
      ·
        refine ⟨29270822524012375311893441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78055526730699667498382509 29270822524012375311893441)
        ·
          refine ⟨21953116893009281483920081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29270822524012375311893441 21953116893009281483920081)
          ·
            refine ⟨16464837669756961112940061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21953116893009281483920081 16464837669756961112940061)
            ·
              refine ⟨6174314126158860417352523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16464837669756961112940061 6174314126158860417352523)
              ·
                refine ⟨9261471189238290626028785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174314126158860417352523 9261471189238290626028785)
                ·
                  refine ⟨6946103391928717969521589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261471189238290626028785 6946103391928717969521589)
                  ·
                    refine ⟨651197192993317309642649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946103391928717969521589 651197192993317309642649)
                    ·
                      rfl

theorem cell22_1902303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_1902303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902303 prefixEnd_1902303 := by exact prefixLift 1902303
  have htrace : WordTrace (prefixWord ++ tailWord_1902303) baseStart_1902303 baseEnd_1902303 := by
    simpa [prefixWord, tailWord_1902303, baseEnd_1902303] using wordTrace_append hprefix tailTrace_1902303
  have hstable : (prefixWord ++ tailWord_1902303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902303).length < 2 ^ (prefixWord ++ tailWord_1902303).sum := by decide
  have hdescent : baseEnd_1902303 < baseStart_1902303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902348 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1902348 : Nat := 118140960795 + 1902348 * 2 ^ 59
def prefixEnd_1902348 : Nat := 4983230072969 + 3 ^ 40 * 1902348 * 2
def baseEnd_1902348 : Nat := 651212597412952192267511

theorem tailTrace_1902348 : CollatzResearch.WordTrace tailWord_1902348 prefixEnd_1902348 651212597412952192267511 := by
  unfold tailWord_1902348
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692165856062783008641849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46256221141417044011522465 34692165856062783008641849)
  ·
    refine ⟨26019124392047087256481387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34692165856062783008641849 26019124392047087256481387)
    ·
      refine ⟨39028686588070630884722081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26019124392047087256481387 39028686588070630884722081)
      ·
        refine ⟨29271514941052973163541561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39028686588070630884722081 29271514941052973163541561)
        ·
          refine ⟨21953636205789729872656171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271514941052973163541561 21953636205789729872656171)
          ·
            refine ⟨32930454308684594808984257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953636205789729872656171 32930454308684594808984257)
            ·
              refine ⟨24697840731513446106738193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32930454308684594808984257 24697840731513446106738193)
              ·
                refine ⟨18523380548635084580053645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24697840731513446106738193 18523380548635084580053645)
                ·
                  refine ⟨6946267705738156717520117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18523380548635084580053645 6946267705738156717520117)
                  ·
                    refine ⟨651212597412952192267511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946267705738156717520117 651212597412952192267511)
                    ·
                      rfl

theorem cell22_1902348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1902348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902348 prefixEnd_1902348 := by exact prefixLift 1902348
  have htrace : WordTrace (prefixWord ++ tailWord_1902348) baseStart_1902348 baseEnd_1902348 := by
    simpa [prefixWord, tailWord_1902348, baseEnd_1902348] using wordTrace_append hprefix tailTrace_1902348
  have hstable : (prefixWord ++ tailWord_1902348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902348).length < 2 ^ (prefixWord ++ tailWord_1902348).sum := by decide
  have hdescent : baseEnd_1902348 < baseStart_1902348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902363 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_1902363 : Nat := 118140960795 + 1902363 * 2 ^ 59
def prefixEnd_1902363 : Nat := 4983230072969 + 3 ^ 40 * 1902363 * 2
def baseEnd_1902363 : Nat := 651217732219497153142465

theorem tailTrace_1902363 : CollatzResearch.WordTrace tailWord_1902363 prefixEnd_1902363 651217732219497153142465 := by
  unfold tailWord_1902363
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384878807071223579079743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46256585871380815719386495 69384878807071223579079743)
  ·
    refine ⟨104077318210606835368619615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69384878807071223579079743 104077318210606835368619615)
    ·
      refine ⟨156115977315910253052929423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104077318210606835368619615 156115977315910253052929423)
      ·
        refine ⟨234173965973865379579394135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156115977315910253052929423 234173965973865379579394135)
        ·
          refine ⟨351260948960798069369091203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234173965973865379579394135 351260948960798069369091203)
          ·
            refine ⟨526891423441197104053636805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351260948960798069369091203 526891423441197104053636805)
            ·
              refine ⟨98792141895224457010056901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526891423441197104053636805 98792141895224457010056901)
              ·
                refine ⟨18523526605354585689385669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98792141895224457010056901 18523526605354585689385669)
                ·
                  refine ⟨3473161238503984816759813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18523526605354585689385669 3473161238503984816759813)
                  ·
                    refine ⟨651217732219497153142465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473161238503984816759813 651217732219497153142465)
                    ·
                      rfl

theorem cell22_1902363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_1902363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902363 prefixEnd_1902363 := by exact prefixLift 1902363
  have htrace : WordTrace (prefixWord ++ tailWord_1902363) baseStart_1902363 baseEnd_1902363 := by
    simpa [prefixWord, tailWord_1902363, baseEnd_1902363] using wordTrace_append hprefix tailTrace_1902363
  have hstable : (prefixWord ++ tailWord_1902363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902363).length < 2 ^ (prefixWord ++ tailWord_1902363).sum := by decide
  have hdescent : baseEnd_1902363 < baseStart_1902363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902397 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1902397 : Nat := 118140960795 + 1902397 * 2 ^ 59
def prefixEnd_1902397 : Nat := 4983230072969 + 3 ^ 40 * 1902397 * 2
def baseEnd_1902397 : Nat := 651229371114332397792361

theorem tailTrace_1902397 : CollatzResearch.WordTrace tailWord_1902397 prefixEnd_1902397 651229371114332397792361 := by
  unfold tailWord_1902397
  simp only [CollatzResearch.WordTrace]
  refine ⟨69386118888948047385817445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46257412592632031590544963 69386118888948047385817445)
  ·
    refine ⟨13009897291677758884840771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69386118888948047385817445 13009897291677758884840771)
    ·
      refine ⟨19514845937516638327261157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13009897291677758884840771 19514845937516638327261157)
      ·
        refine ⟨3659033613284369686361467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19514845937516638327261157 3659033613284369686361467)
        ·
          refine ⟨5488550419926554529542201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659033613284369686361467 5488550419926554529542201)
          ·
            refine ⟨4116412814944915897156651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488550419926554529542201 4116412814944915897156651)
            ·
              refine ⟨6174619222417373845734977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116412814944915897156651 6174619222417373845734977)
              ·
                refine ⟨4630964416813030384301233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174619222417373845734977 4630964416813030384301233)
                ·
                  refine ⟨3473223312609772788225925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630964416813030384301233 3473223312609772788225925)
                  ·
                    refine ⟨651229371114332397792361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473223312609772788225925 651229371114332397792361)
                    ·
                      rfl

theorem cell22_1902397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1902397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902397 prefixEnd_1902397 := by exact prefixLift 1902397
  have htrace : WordTrace (prefixWord ++ tailWord_1902397) baseStart_1902397 baseEnd_1902397 := by
    simpa [prefixWord, tailWord_1902397, baseEnd_1902397] using wordTrace_append hprefix tailTrace_1902397
  have hstable : (prefixWord ++ tailWord_1902397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902397).length < 2 ^ (prefixWord ++ tailWord_1902397).sum := by decide
  have hdescent : baseEnd_1902397 < baseStart_1902397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902472 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_1902472 : Nat := 118140960795 + 1902472 * 2 ^ 59
def prefixEnd_1902472 : Nat := 4983230072969 + 3 ^ 40 * 1902472 * 2
def baseEnd_1902472 : Nat := 651255045147057202167131

theorem tailTrace_1902472 : CollatzResearch.WordTrace tailWord_1902472 prefixEnd_1902472 651255045147057202167131 := by
  unfold tailWord_1902472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34694427181838167597398835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46259236242450890129865113 34694427181838167597398835)
  ·
    refine ⟨52041640772757251396098253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34694427181838167597398835 52041640772757251396098253)
    ·
      refine ⟨19515615289783969273536845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52041640772757251396098253 19515615289783969273536845)
      ·
        refine ⟨7318355733668988477576317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19515615289783969273536845 7318355733668988477576317)
        ·
          refine ⟨2744383400125870679091119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7318355733668988477576317 2744383400125870679091119)
          ·
            refine ⟨4116575100188806018636679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744383400125870679091119 4116575100188806018636679)
            ·
              refine ⟨6174862650283209027955019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116575100188806018636679 6174862650283209027955019)
              ·
                refine ⟨9262293975424813541932529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174862650283209027955019 9262293975424813541932529)
                ·
                  refine ⟨6946720481568610156449397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262293975424813541932529 6946720481568610156449397)
                  ·
                    refine ⟨651255045147057202167131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946720481568610156449397 651255045147057202167131)
                    ·
                      rfl

theorem cell22_1902472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_1902472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902472 prefixEnd_1902472 := by exact prefixLift 1902472
  have htrace : WordTrace (prefixWord ++ tailWord_1902472) baseStart_1902472 baseEnd_1902472 := by
    simpa [prefixWord, tailWord_1902472, baseEnd_1902472] using wordTrace_append hprefix tailTrace_1902472
  have hstable : (prefixWord ++ tailWord_1902472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902472).length < 2 ^ (prefixWord ++ tailWord_1902472).sum := by decide
  have hdescent : baseEnd_1902472 < baseStart_1902472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902485 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 6]
def baseStart_1902485 : Nat := 118140960795 + 1902485 * 2 ^ 59
def prefixEnd_1902485 : Nat := 4983230072969 + 3 ^ 40 * 1902485 * 2
def baseEnd_1902485 : Nat := 217086498437576500530697

theorem tailTrace_1902485 : CollatzResearch.WordTrace tailWord_1902485 prefixEnd_1902485 217086498437576500530697 := by
  unfold tailWord_1902485
  simp only [CollatzResearch.WordTrace]
  refine ⟨69389328512629238415020909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46259552341752825610013939 69389328512629238415020909)
  ·
    refine ⟨26020998192235964405632841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69389328512629238415020909 26020998192235964405632841)
    ·
      refine ⟨19515748644176973304224631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26020998192235964405632841 19515748644176973304224631)
      ·
        refine ⟨29273622966265459956336947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515748644176973304224631 29273622966265459956336947)
        ·
          refine ⟨43910434449398189934505421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29273622966265459956336947 43910434449398189934505421)
          ·
            refine ⟨16466412918524321225439533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43910434449398189934505421 16466412918524321225439533)
            ·
              refine ⟨6174904844446620459539825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16466412918524321225439533 6174904844446620459539825)
              ·
                refine ⟨4631178633334965344654869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174904844446620459539825 4631178633334965344654869)
                ·
                  refine ⟨217086498437576500530697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4631178633334965344654869 217086498437576500530697)
                  ·
                    rfl

theorem cell22_1902485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_1902485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902485 prefixEnd_1902485 := by exact prefixLift 1902485
  have htrace : WordTrace (prefixWord ++ tailWord_1902485) baseStart_1902485 baseEnd_1902485 := by
    simpa [prefixWord, tailWord_1902485, baseEnd_1902485] using wordTrace_append hprefix tailTrace_1902485
  have hstable : (prefixWord ++ tailWord_1902485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902485).length < 2 ^ (prefixWord ++ tailWord_1902485).sum := by decide
  have hdescent : baseEnd_1902485 < baseStart_1902485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902515 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_1902515 : Nat := 118140960795 + 1902515 * 2 ^ 59
def prefixEnd_1902515 : Nat := 4983230072969 + 3 ^ 40 * 1902515 * 2
def baseEnd_1902515 : Nat := 651269764925819423341999

theorem tailTrace_1902515 : CollatzResearch.WordTrace tailWord_1902515 prefixEnd_1902515 651269764925819423341999 := by
  unfold tailWord_1902515
  simp only [CollatzResearch.WordTrace]
  refine ⟨69390422702520553538612999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46260281801680369025741999 69390422702520553538612999)
  ·
    refine ⟨104085634053780830307919499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69390422702520553538612999 104085634053780830307919499)
    ·
      refine ⟨156128451080671245461879249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104085634053780830307919499 156128451080671245461879249)
      ·
        refine ⟨117096338310503434096409437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156128451080671245461879249 117096338310503434096409437)
        ·
          refine ⟨43911126866438787786153539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117096338310503434096409437 43911126866438787786153539)
          ·
            refine ⟨65866690299658181679230309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43911126866438787786153539 65866690299658181679230309)
            ·
              refine ⟨12350004431185909064855683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65866690299658181679230309 12350004431185909064855683)
              ·
                refine ⟨18525006646778863597283525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350004431185909064855683 18525006646778863597283525)
                ·
                  refine ⟨3473438746271036924490661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18525006646778863597283525 3473438746271036924490661)
                  ·
                    refine ⟨651269764925819423341999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473438746271036924490661 651269764925819423341999)
                    ·
                      rfl

theorem cell22_1902515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_1902515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902515 prefixEnd_1902515 := by exact prefixLift 1902515
  have htrace : WordTrace (prefixWord ++ tailWord_1902515) baseStart_1902515 baseEnd_1902515 := by
    simpa [prefixWord, tailWord_1902515, baseEnd_1902515] using wordTrace_append hprefix tailTrace_1902515
  have hstable : (prefixWord ++ tailWord_1902515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902515).length < 2 ^ (prefixWord ++ tailWord_1902515).sum := by decide
  have hdescent : baseEnd_1902515 < baseStart_1902515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902575 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 7]
def baseStart_1902575 : Nat := 118140960795 + 1902575 * 2 ^ 59
def prefixEnd_1902575 : Nat := 4983230072969 + 3 ^ 40 * 1902575 * 2
def baseEnd_1902575 : Nat := 217096768050666422280605

theorem tailTrace_1902575 : CollatzResearch.WordTrace tailWord_1902575 prefixEnd_1902575 217096768050666422280605 := by
  unfold tailWord_1902575
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392611082303183785797179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46261740721535455857198119 69392611082303183785797179)
  ·
    refine ⟨104088916623454775678695769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69392611082303183785797179 104088916623454775678695769)
    ·
      refine ⟨78066687467591081759021827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104088916623454775678695769 78066687467591081759021827)
      ·
        refine ⟨117100031201386622638532741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78066687467591081759021827 117100031201386622638532741)
        ·
          refine ⟨21956255850259991744724889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117100031201386622638532741 21956255850259991744724889)
          ·
            refine ⟨16467191887694993808543667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21956255850259991744724889 16467191887694993808543667)
            ·
              refine ⟨24700787831542490712815501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16467191887694993808543667 24700787831542490712815501)
              ·
                refine ⟨9262795436828434017305813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24700787831542490712815501 9262795436828434017305813)
                ·
                  refine ⟨217096768050666422280605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9262795436828434017305813 217096768050666422280605)
                  ·
                    rfl

theorem cell22_1902575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_1902575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902575 prefixEnd_1902575 := by exact prefixLift 1902575
  have htrace : WordTrace (prefixWord ++ tailWord_1902575) baseStart_1902575 baseEnd_1902575 := by
    simpa [prefixWord, tailWord_1902575, baseEnd_1902575] using wordTrace_append hprefix tailTrace_1902575
  have hstable : (prefixWord ++ tailWord_1902575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902575).length < 2 ^ (prefixWord ++ tailWord_1902575).sum := by decide
  have hdescent : baseEnd_1902575 < baseStart_1902575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902579 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 1, 3]
def baseStart_1902579 : Nat := 118140960795 + 1902579 * 2 ^ 59
def prefixEnd_1902579 : Nat := 4983230072969 + 3 ^ 40 * 1902579 * 2
def baseEnd_1902579 : Nat := 651291673433744589741803

theorem tailTrace_1902579 : CollatzResearch.WordTrace tailWord_1902579 prefixEnd_1902579 651291673433744589741803 := by
  unfold tailWord_1902579
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392756974288692468942791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46261837982859128312628527 69392756974288692468942791)
  ·
    refine ⟨104089135461433038703414187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69392756974288692468942791 104089135461433038703414187)
    ·
      refine ⟨156133703192149558055121281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104089135461433038703414187 156133703192149558055121281)
      ·
        refine ⟨117100277394112168541340961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156133703192149558055121281 117100277394112168541340961)
        ·
          refine ⟨87825208045584126406005721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117100277394112168541340961 87825208045584126406005721)
          ·
            refine ⟨65868906034188094804504291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87825208045584126406005721 65868906034188094804504291)
            ·
              refine ⟨98803359051282142206756437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65868906034188094804504291 98803359051282142206756437)
              ·
                refine ⟨1157851863882212603985427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 98803359051282142206756437 1157851863882212603985427)
                ·
                  refine ⟨1736777795823318905978141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157851863882212603985427 1736777795823318905978141)
                  ·
                    refine ⟨651291673433744589741803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1736777795823318905978141 651291673433744589741803)
                    ·
                      rfl

theorem cell22_1902579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 3].length) (baseStart_1902579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902579 prefixEnd_1902579 := by exact prefixLift 1902579
  have htrace : WordTrace (prefixWord ++ tailWord_1902579) baseStart_1902579 baseEnd_1902579 := by
    simpa [prefixWord, tailWord_1902579, baseEnd_1902579] using wordTrace_append hprefix tailTrace_1902579
  have hstable : (prefixWord ++ tailWord_1902579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902579).length < 2 ^ (prefixWord ++ tailWord_1902579).sum := by decide
  have hdescent : baseEnd_1902579 < baseStart_1902579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902669 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1902669 : Nat := 118140960795 + 1902669 * 2 ^ 59
def prefixEnd_1902669 : Nat := 4983230072969 + 3 ^ 40 * 1902669 * 2
def baseEnd_1902669 : Nat := 651322482273014354991527

theorem tailTrace_1902669 : CollatzResearch.WordTrace tailWord_1902669 prefixEnd_1902669 651322482273014354991527 := by
  unfold tailWord_1902669
  simp only [CollatzResearch.WordTrace]
  refine ⟨69396039543962637839719061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46264026362641758559812707 69396039543962637839719061)
  ·
    refine ⟨3252939353623248648736831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69396039543962637839719061 3252939353623248648736831)
    ·
      refine ⟨4879409030434872973105247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252939353623248648736831 4879409030434872973105247)
      ·
        refine ⟨7319113545652309459657871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879409030434872973105247 7319113545652309459657871)
        ·
          refine ⟨10978670318478464189486807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319113545652309459657871 10978670318478464189486807)
          ·
            refine ⟨16468005477717696284230211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978670318478464189486807 16468005477717696284230211)
            ·
              refine ⟨24702008216576544426345317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468005477717696284230211 24702008216576544426345317)
              ·
                refine ⟨4631626540608102079939747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24702008216576544426345317 4631626540608102079939747)
                ·
                  refine ⟨6947439810912153119909621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631626540608102079939747 6947439810912153119909621)
                  ·
                    refine ⟨651322482273014354991527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6947439810912153119909621 651322482273014354991527)
                    ·
                      rfl

theorem cell22_1902669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1902669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902669 prefixEnd_1902669 := by exact prefixLift 1902669
  have htrace : WordTrace (prefixWord ++ tailWord_1902669) baseStart_1902669 baseEnd_1902669 := by
    simpa [prefixWord, tailWord_1902669, baseEnd_1902669] using wordTrace_append hprefix tailTrace_1902669
  have hstable : (prefixWord ++ tailWord_1902669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902669).length < 2 ^ (prefixWord ++ tailWord_1902669).sum := by decide
  have hdescent : baseEnd_1902669 < baseStart_1902669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902727 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 7]
def baseStart_1902727 : Nat := 118140960795 + 1902727 * 2 ^ 59
def prefixEnd_1902727 : Nat := 4983230072969 + 3 ^ 40 * 1902727 * 2
def baseEnd_1902727 : Nat := 217114112286107179013783

theorem tailTrace_1902727 : CollatzResearch.WordTrace tailWord_1902727 prefixEnd_1902727 217114112286107179013783 := by
  unfold tailWord_1902727
  simp only [CollatzResearch.WordTrace]
  refine ⟨69398154977752513745330435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46265436651835009163553623 69398154977752513745330435)
  ·
    refine ⟨104097232466628770617995653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69398154977752513745330435 104097232466628770617995653)
    ·
      refine ⟨19518231087492894490874185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104097232466628770617995653 19518231087492894490874185)
      ·
        refine ⟨14638673315619670868155639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19518231087492894490874185 14638673315619670868155639)
        ·
          refine ⟨21958009973429506302233459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638673315619670868155639 21958009973429506302233459)
          ·
            refine ⟨32937014960144259453350189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21958009973429506302233459 32937014960144259453350189)
            ·
              refine ⟨12351380610054097295006321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32937014960144259453350189 12351380610054097295006321)
              ·
                refine ⟨9263535457540572971254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351380610054097295006321 9263535457540572971254741)
                ·
                  refine ⟨217114112286107179013783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9263535457540572971254741 217114112286107179013783)
                  ·
                    rfl

theorem cell22_1902727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_1902727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902727 prefixEnd_1902727 := by exact prefixLift 1902727
  have htrace : WordTrace (prefixWord ++ tailWord_1902727) baseStart_1902727 baseEnd_1902727 := by
    simpa [prefixWord, tailWord_1902727, baseEnd_1902727] using wordTrace_append hprefix tailTrace_1902727
  have hstable : (prefixWord ++ tailWord_1902727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902727).length < 2 ^ (prefixWord ++ tailWord_1902727).sum := by decide
  have hdescent : baseEnd_1902727 < baseStart_1902727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902821 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1902821 : Nat := 118140960795 + 1902821 * 2 ^ 59
def prefixEnd_1902821 : Nat := 4983230072969 + 3 ^ 40 * 1902821 * 2
def baseEnd_1902821 : Nat := 651374514979336625191061

theorem tailTrace_1902821 : CollatzResearch.WordTrace tailWord_1902821 prefixEnd_1902821 651374514979336625191061 := by
  unfold tailWord_1902821
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401583439411967799252317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46267722292941311866168211 69401583439411967799252317)
  ·
    refine ⟨26025593789779487924719619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69401583439411967799252317 26025593789779487924719619)
    ·
      refine ⟨39038390684669231887079429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26025593789779487924719619 39038390684669231887079429)
      ·
        refine ⟨7319698253375480978827393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39038390684669231887079429 7319698253375480978827393)
        ·
          refine ⟨5489773690031610734120545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7319698253375480978827393 5489773690031610734120545)
          ·
            refine ⟨4117330267523708050590409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489773690031610734120545 4117330267523708050590409)
            ·
              refine ⟨3087997700642781037942807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117330267523708050590409 3087997700642781037942807)
              ·
                refine ⟨4631996550964171556914211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087997700642781037942807 4631996550964171556914211)
                ·
                  refine ⟨6947994826446257335371317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631996550964171556914211 6947994826446257335371317)
                  ·
                    refine ⟨651374514979336625191061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6947994826446257335371317 651374514979336625191061)
                    ·
                      rfl

theorem cell22_1902821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1902821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902821 prefixEnd_1902821 := by exact prefixLift 1902821
  have htrace : WordTrace (prefixWord ++ tailWord_1902821) baseStart_1902821 baseEnd_1902821 := by
    simpa [prefixWord, tailWord_1902821, baseEnd_1902821] using wordTrace_append hprefix tailTrace_1902821
  have hstable : (prefixWord ++ tailWord_1902821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902821).length < 2 ^ (prefixWord ++ tailWord_1902821).sum := by decide
  have hdescent : baseEnd_1902821 < baseStart_1902821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902971 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_1902971 : Nat := 118140960795 + 1902971 * 2 ^ 59
def prefixEnd_1902971 : Nat := 4983230072969 + 3 ^ 40 * 1902971 * 2
def baseEnd_1902971 : Nat := 651425863044786233940601

theorem tailTrace_1902971 : CollatzResearch.WordTrace tailWord_1902971 prefixEnd_1902971 651425863044786233940601 := by
  unfold tailWord_1902971
  simp only [CollatzResearch.WordTrace]
  refine ⟨69407054388868543417212767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46271369592579028944808511 69407054388868543417212767)
  ·
    refine ⟨104110581583302815125819151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69407054388868543417212767 104110581583302815125819151)
    ·
      refine ⟨156165872374954222688728727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104110581583302815125819151 156165872374954222688728727)
      ·
        refine ⟨234248808562431334033093091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156165872374954222688728727 234248808562431334033093091)
        ·
          refine ⟨351373212843647001049639637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234248808562431334033093091 351373212843647001049639637)
          ·
            refine ⟨8235309676022976587100929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 351373212843647001049639637 8235309676022976587100929)
            ·
              refine ⟨6176482257017232440325697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235309676022976587100929 6176482257017232440325697)
              ·
                refine ⟨4632361692762924330244273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176482257017232440325697 4632361692762924330244273)
                ·
                  refine ⟨3474271269572193247683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632361692762924330244273 3474271269572193247683205)
                  ·
                    refine ⟨651425863044786233940601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474271269572193247683205 651425863044786233940601)
                    ·
                      rfl

theorem cell22_1902971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_1902971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902971 prefixEnd_1902971 := by exact prefixLift 1902971
  have htrace : WordTrace (prefixWord ++ tailWord_1902971) baseStart_1902971 baseEnd_1902971 := by
    simpa [prefixWord, tailWord_1902971, baseEnd_1902971] using wordTrace_append hprefix tailTrace_1902971
  have hstable : (prefixWord ++ tailWord_1902971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902971).length < 2 ^ (prefixWord ++ tailWord_1902971).sum := by decide
  have hdescent : baseEnd_1902971 < baseStart_1902971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902973 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1902973 : Nat := 118140960795 + 1902973 * 2 ^ 59
def prefixEnd_1902973 : Nat := 4983230072969 + 3 ^ 40 * 1902973 * 2
def baseEnd_1902973 : Nat := 651426547685658895390595

theorem tailTrace_1902973 : CollatzResearch.WordTrace tailWord_1902973 prefixEnd_1902973 651426547685658895390595 := by
  unfold tailWord_1902973
  simp only [CollatzResearch.WordTrace]
  refine ⟨69407127334861297758785573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46271418223240865172523715 69407127334861297758785573)
  ·
    refine ⟨13013836375286493329772295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69407127334861297758785573 13013836375286493329772295)
    ·
      refine ⟨19520754562929739994658443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013836375286493329772295 19520754562929739994658443)
      ·
        refine ⟨29281131844394609991987665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520754562929739994658443 29281131844394609991987665)
        ·
          refine ⟨21960848883295957493990749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29281131844394609991987665 21960848883295957493990749)
          ·
            refine ⟨8235318331235984060246531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21960848883295957493990749 8235318331235984060246531)
            ·
              refine ⟨12352977496853976090369797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235318331235984060246531 12352977496853976090369797)
              ·
                refine ⟨2316183280660120516944337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12352977496853976090369797 2316183280660120516944337)
                ·
                  refine ⟨1737137460495090387708253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316183280660120516944337 1737137460495090387708253)
                  ·
                    refine ⟨651426547685658895390595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737137460495090387708253 651426547685658895390595)
                    ·
                      rfl

theorem cell22_1902973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1902973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902973 prefixEnd_1902973 := by exact prefixLift 1902973
  have htrace : WordTrace (prefixWord ++ tailWord_1902973) baseStart_1902973 baseEnd_1902973 := by
    simpa [prefixWord, tailWord_1902973, baseEnd_1902973] using wordTrace_append hprefix tailTrace_1902973
  have hstable : (prefixWord ++ tailWord_1902973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902973).length < 2 ^ (prefixWord ++ tailWord_1902973).sum := by decide
  have hdescent : baseEnd_1902973 < baseStart_1902973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902990 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1902990 : Nat := 118140960795 + 1902990 * 2 ^ 59
def prefixEnd_1902990 : Nat := 4983230072969 + 3 ^ 40 * 1902990 * 2
def baseEnd_1902990 : Nat := 651432367133076517715543

theorem tailTrace_1902990 : CollatzResearch.WordTrace tailWord_1902990 prefixEnd_1902990 651432367133076517715543 := by
  unfold tailWord_1902990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675968421974963707769303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46271831583866473108102949 8675968421974963707769303)
  ·
    refine ⟨13013952632962445561653955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8675968421974963707769303 13013952632962445561653955)
    ·
      refine ⟨19520928949443668342480933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013952632962445561653955 19520928949443668342480933)
      ·
        refine ⟨3660174178020687814215175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19520928949443668342480933 3660174178020687814215175)
        ·
          refine ⟨5490261267031031721322763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660174178020687814215175 5490261267031031721322763)
          ·
            refine ⟨8235391900546547581984145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490261267031031721322763 8235391900546547581984145)
            ·
              refine ⟨6176543925409910686488109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235391900546547581984145 6176543925409910686488109)
              ·
                refine ⟨2316203972028716507433041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6176543925409910686488109 2316203972028716507433041)
                ·
                  refine ⟨1737152979021537380574781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316203972028716507433041 1737152979021537380574781)
                  ·
                    refine ⟨651432367133076517715543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737152979021537380574781 651432367133076517715543)
                    ·
                      rfl

theorem cell22_1902990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1902990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1902990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1902990 prefixEnd_1902990 := by exact prefixLift 1902990
  have htrace : WordTrace (prefixWord ++ tailWord_1902990) baseStart_1902990 baseEnd_1902990 := by
    simpa [prefixWord, tailWord_1902990, baseEnd_1902990] using wordTrace_append hprefix tailTrace_1902990
  have hstable : (prefixWord ++ tailWord_1902990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902990).length < 2 ^ (prefixWord ++ tailWord_1902990).sum := by decide
  have hdescent : baseEnd_1902990 < baseStart_1902990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903005 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1903005 : Nat := 118140960795 + 1903005 * 2 ^ 59
def prefixEnd_1903005 : Nat := 4983230072969 + 3 ^ 40 * 1903005 * 2
def baseEnd_1903005 : Nat := 651437501939621478590497

theorem tailTrace_1903005 : CollatzResearch.WordTrace tailWord_1903005 prefixEnd_1903005 651437501939621478590497 := by
  unfold tailWord_1903005
  simp only [CollatzResearch.WordTrace]
  refine ⟨69408294470745367223950469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46272196313830244815966979 69408294470745367223950469)
  ·
    refine ⟨13014055213264756354490713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69408294470745367223950469 13014055213264756354490713)
    ·
      refine ⟨9760541409948567265868035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13014055213264756354490713 9760541409948567265868035)
      ·
        refine ⟨14640812114922850898802053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9760541409948567265868035 14640812114922850898802053)
        ·
          refine ⟨2745152271548034543525385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14640812114922850898802053 2745152271548034543525385)
          ·
            refine ⟨2058864203661025907644039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745152271548034543525385 2058864203661025907644039)
            ·
              refine ⟨3088296305491538861466059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058864203661025907644039 3088296305491538861466059)
              ·
                refine ⟨4632444458237308292199089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088296305491538861466059 4632444458237308292199089)
                ·
                  refine ⟨3474333343677981219149317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632444458237308292199089 3474333343677981219149317)
                  ·
                    refine ⟨651437501939621478590497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474333343677981219149317 651437501939621478590497)
                    ·
                      rfl

theorem cell22_1903005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1903005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903005 prefixEnd_1903005 := by exact prefixLift 1903005
  have htrace : WordTrace (prefixWord ++ tailWord_1903005) baseStart_1903005 baseEnd_1903005 := by
    simpa [prefixWord, tailWord_1903005, baseEnd_1903005] using wordTrace_append hprefix tailTrace_1903005
  have hstable : (prefixWord ++ tailWord_1903005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903005).length < 2 ^ (prefixWord ++ tailWord_1903005).sum := by decide
  have hdescent : baseEnd_1903005 < baseStart_1903005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903031 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 7]
def baseStart_1903031 : Nat := 118140960795 + 1903031 * 2 ^ 59
def prefixEnd_1903031 : Nat := 4983230072969 + 3 ^ 40 * 1903031 * 2
def baseEnd_1903031 : Nat := 217148800756988692480139

theorem tailTrace_1903031 : CollatzResearch.WordTrace tailWord_1903031 prefixEnd_1903031 217148800756988692480139 := by
  unfold tailWord_1903031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69409242768651173664396947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46272828512434115776264631 69409242768651173664396947)
  ·
    refine ⟨104113864152976760496595421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69409242768651173664396947 104113864152976760496595421)
    ·
      refine ⟨39042699057366285186223283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104113864152976760496595421 39042699057366285186223283)
      ·
        refine ⟨58564048586049427779334925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39042699057366285186223283 58564048586049427779334925)
        ·
          refine ⟨21961518219768535417250597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58564048586049427779334925 21961518219768535417250597)
          ·
            refine ⟨4117784666206600390734487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21961518219768535417250597 4117784666206600390734487)
            ·
              refine ⟨6176676999309900586101731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117784666206600390734487 6176676999309900586101731)
              ·
                refine ⟨9265015498964850879152597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176676999309900586101731 9265015498964850879152597)
                ·
                  refine ⟨217148800756988692480139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9265015498964850879152597 217148800756988692480139)
                  ·
                    rfl

theorem cell22_1903031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_1903031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903031 prefixEnd_1903031 := by exact prefixLift 1903031
  have htrace : WordTrace (prefixWord ++ tailWord_1903031) baseStart_1903031 baseEnd_1903031 := by
    simpa [prefixWord, tailWord_1903031, baseEnd_1903031] using wordTrace_append hprefix tailTrace_1903031
  have hstable : (prefixWord ++ tailWord_1903031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903031).length < 2 ^ (prefixWord ++ tailWord_1903031).sum := by decide
  have hdescent : baseEnd_1903031 < baseStart_1903031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903041 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1903041 : Nat := 118140960795 + 1903041 * 2 ^ 59
def prefixEnd_1903041 : Nat := 4983230072969 + 3 ^ 40 * 1903041 * 2
def baseEnd_1903041 : Nat := 651449825475329384690387

theorem tailTrace_1903041 : CollatzResearch.WordTrace tailWord_1903041 prefixEnd_1903041 651449825475329384690387 := by
  unfold tailWord_1903041
  simp only [CollatzResearch.WordTrace]
  refine ⟨69409607498614945372260977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46273071665743296914840651 69409607498614945372260977)
  ·
    refine ⟨52057205623961209029195733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69409607498614945372260977 52057205623961209029195733)
    ·
      refine ⟨1220090756811590836621775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52057205623961209029195733 1220090756811590836621775)
      ·
        refine ⟨1830136135217386254932663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220090756811590836621775 1830136135217386254932663)
        ·
          refine ⟨2745204202826079382398995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830136135217386254932663 2745204202826079382398995)
          ·
            refine ⟨4117806304239119073598493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745204202826079382398995 4117806304239119073598493)
            ·
              refine ⟨1544177364089669652599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4117806304239119073598493 1544177364089669652599435)
              ·
                refine ⟨2316266046134504478899153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544177364089669652599435 2316266046134504478899153)
                ·
                  refine ⟨1737199534600878359174365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316266046134504478899153 1737199534600878359174365)
                  ·
                    refine ⟨651449825475329384690387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737199534600878359174365 651449825475329384690387)
                    ·
                      rfl

theorem cell22_1903041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1903041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903041 prefixEnd_1903041 := by exact prefixLift 1903041
  have htrace : WordTrace (prefixWord ++ tailWord_1903041) baseStart_1903041 baseEnd_1903041 := by
    simpa [prefixWord, tailWord_1903041, baseEnd_1903041] using wordTrace_append hprefix tailTrace_1903041
  have hstable : (prefixWord ++ tailWord_1903041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903041).length < 2 ^ (prefixWord ++ tailWord_1903041).sum := by decide
  have hdescent : baseEnd_1903041 < baseStart_1903041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903123 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_1903123 : Nat := 118140960795 + 1903123 * 2 ^ 59
def prefixEnd_1903123 : Nat := 4983230072969 + 3 ^ 40 * 1903123 * 2
def baseEnd_1903123 : Nat := 651477895751108504140135

theorem tailTrace_1903123 : CollatzResearch.WordTrace tailWord_1903123 prefixEnd_1903123 651477895751108504140135 := by
  unfold tailWord_1903123
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412598284317873376746023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46275065522878582251164015 69412598284317873376746023)
  ·
    refine ⟨104118897426476810065119035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69412598284317873376746023 104118897426476810065119035)
    ·
      refine ⟨156178346139715215097678553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104118897426476810065119035 156178346139715215097678553)
      ·
        refine ⟨117133759604786411323258915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156178346139715215097678553 117133759604786411323258915)
        ·
          refine ⟨175700639407179616984888373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117133759604786411323258915 175700639407179616984888373)
          ·
            refine ⟨16471934944423089092333285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175700639407179616984888373 16471934944423089092333285)
            ·
              refine ⟨3088487802079329204812491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16471934944423089092333285 3088487802079329204812491)
              ·
                refine ⟨4632731703118993807218737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088487802079329204812491 4632731703118993807218737)
                ·
                  refine ⟨3474548777339245355414053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632731703118993807218737 3474548777339245355414053)
                  ·
                    refine ⟨651477895751108504140135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474548777339245355414053 651477895751108504140135)
                    ·
                      rfl

theorem cell22_1903123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_1903123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903123 prefixEnd_1903123 := by exact prefixLift 1903123
  have htrace : WordTrace (prefixWord ++ tailWord_1903123) baseStart_1903123 baseEnd_1903123 := by
    simpa [prefixWord, tailWord_1903123, baseEnd_1903123] using wordTrace_append hprefix tailTrace_1903123
  have hstable : (prefixWord ++ tailWord_1903123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903123).length < 2 ^ (prefixWord ++ tailWord_1903123).sum := by decide
  have hdescent : baseEnd_1903123 < baseStart_1903123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903144 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_1903144 : Nat := 118140960795 + 1903144 * 2 ^ 59
def prefixEnd_1903144 : Nat := 4983230072969 + 3 ^ 40 * 1903144 * 2
def baseEnd_1903144 : Nat := 217161694826757149788357

theorem tailTrace_1903144 : CollatzResearch.WordTrace tailWord_1903144 prefixEnd_1903144 217161694826757149788357 := by
  unfold tailWord_1903144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706682108620896981630243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46275576144827862642173657 34706682108620896981630243)
  ·
    refine ⟨52060023162931345472445365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34706682108620896981630243 52060023162931345472445365)
    ·
      refine ⟨4880627171524813638041753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52060023162931345472445365 4880627171524813638041753)
      ·
        refine ⟨3660470378643610228531315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880627171524813638041753 3660470378643610228531315)
        ·
          refine ⟨5490705567965415342796973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660470378643610228531315 5490705567965415342796973)
          ·
            refine ⟨2059014587987030753548865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5490705567965415342796973 2059014587987030753548865)
            ·
              refine ⟨1544260940990273065161649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059014587987030753548865 1544260940990273065161649)
              ·
                refine ⟨1158195705742704798871237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544260940990273065161649 1158195705742704798871237)
                ·
                  refine ⟨217161694826757149788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158195705742704798871237 217161694826757149788357)
                  ·
                    rfl

theorem cell22_1903144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_1903144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903144 prefixEnd_1903144 := by exact prefixLift 1903144
  have htrace : WordTrace (prefixWord ++ tailWord_1903144) baseStart_1903144 baseEnd_1903144 := by
    simpa [prefixWord, tailWord_1903144, baseEnd_1903144] using wordTrace_append hprefix tailTrace_1903144
  have hstable : (prefixWord ++ tailWord_1903144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903144).length < 2 ^ (prefixWord ++ tailWord_1903144).sum := by decide
  have hdescent : baseEnd_1903144 < baseStart_1903144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903174 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1903174 : Nat := 118140960795 + 1903174 * 2 ^ 59
def prefixEnd_1903174 : Nat := 4983230072969 + 3 ^ 40 * 1903174 * 2
def baseEnd_1903174 : Nat := 651495354093361371114979

theorem tailTrace_1903174 : CollatzResearch.WordTrace tailWord_1903174 prefixEnd_1903174 651495354093361371114979 := by
  unfold tailWord_1903174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169201825222909658964143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46276305604755406057901717 2169201825222909658964143)
  ·
    refine ⟨3253802737834364488446215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169201825222909658964143 3253802737834364488446215)
    ·
      refine ⟨4880704106751546732669323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3253802737834364488446215 4880704106751546732669323)
      ·
        refine ⟨7321056160127320099003985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880704106751546732669323 7321056160127320099003985)
        ·
          refine ⟨5490792120095490074252989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7321056160127320099003985 5490792120095490074252989)
          ·
            refine ⟨2059047045035808777844871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5490792120095490074252989 2059047045035808777844871)
            ·
              refine ⟨3088570567553713166767307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059047045035808777844871 3088570567553713166767307)
              ·
                refine ⟨4632855851330569750150961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088570567553713166767307 4632855851330569750150961)
                ·
                  refine ⟨3474641888497927312613221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632855851330569750150961 3474641888497927312613221)
                  ·
                    refine ⟨651495354093361371114979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474641888497927312613221 651495354093361371114979)
                    ·
                      rfl

theorem cell22_1903174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1903174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903174 prefixEnd_1903174 := by exact prefixLift 1903174
  have htrace : WordTrace (prefixWord ++ tailWord_1903174) baseStart_1903174 baseEnd_1903174 := by
    simpa [prefixWord, tailWord_1903174, baseEnd_1903174] using wordTrace_append hprefix tailTrace_1903174
  have hstable : (prefixWord ++ tailWord_1903174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903174).length < 2 ^ (prefixWord ++ tailWord_1903174).sum := by decide
  have hdescent : baseEnd_1903174 < baseStart_1903174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903228 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_1903228 : Nat := 118140960795 + 1903228 * 2 ^ 59
def prefixEnd_1903228 : Nat := 4983230072969 + 3 ^ 40 * 1903228 * 2
def baseEnd_1903228 : Nat := 217171279798974410088271

theorem tailTrace_1903228 : CollatzResearch.WordTrace tailWord_1903228 prefixEnd_1903228 217171279798974410088271 := by
  unfold tailWord_1903228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708213974468738154659169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46277618632624984206212225 34708213974468738154659169)
  ·
    refine ⟨26031160480851553615994377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34708213974468738154659169 26031160480851553615994377)
    ·
      refine ⟨19523370360638665211995783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26031160480851553615994377 19523370360638665211995783)
      ·
        refine ⟨29285055540957997817993675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19523370360638665211995783 29285055540957997817993675)
        ·
          refine ⟨43927583311436996726990513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29285055540957997817993675 43927583311436996726990513)
          ·
            refine ⟨32945687483577747545242885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43927583311436996726990513 32945687483577747545242885)
            ·
              refine ⟨6177316403170827664733041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32945687483577747545242885 6177316403170827664733041)
              ·
                refine ⟨4632987302378120748549781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177316403170827664733041 4632987302378120748549781)
                ·
                  refine ⟨217171279798974410088271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4632987302378120748549781 217171279798974410088271)
                  ·
                    rfl

theorem cell22_1903228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_1903228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903228 prefixEnd_1903228 := by exact prefixLift 1903228
  have htrace : WordTrace (prefixWord ++ tailWord_1903228) baseStart_1903228 baseEnd_1903228 := by
    simpa [prefixWord, tailWord_1903228, baseEnd_1903228] using wordTrace_append hprefix tailTrace_1903228
  have hstable : (prefixWord ++ tailWord_1903228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903228).length < 2 ^ (prefixWord ++ tailWord_1903228).sum := by decide
  have hdescent : baseEnd_1903228 < baseStart_1903228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903281 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_1903281 : Nat := 118140960795 + 1903281 * 2 ^ 59
def prefixEnd_1903281 : Nat := 4983230072969 + 3 ^ 40 * 1903281 * 2
def baseEnd_1903281 : Nat := 651531982380048758689651

theorem tailTrace_1903281 : CollatzResearch.WordTrace tailWord_1903281 prefixEnd_1903281 651531982380048758689651 := by
  unfold tailWord_1903281
  simp only [CollatzResearch.WordTrace]
  refine ⟨69418361017745466360997697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46278907345163644240665131 69418361017745466360997697)
  ·
    refine ⟨52063770763309099770748273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69418361017745466360997697 52063770763309099770748273)
    ·
      refine ⟨39047828072481824828061205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52063770763309099770748273 39047828072481824828061205)
      ·
        refine ⟨1830366940897585538815369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39047828072481824828061205 1830366940897585538815369)
        ·
          refine ⟨1372775205673189154111527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830366940897585538815369 1372775205673189154111527)
          ·
            refine ⟨2059162808509783731167291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372775205673189154111527 2059162808509783731167291)
            ·
              refine ⟨3088744212764675596750937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059162808509783731167291 3088744212764675596750937)
              ·
                refine ⟨2316558159573506697563203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088744212764675596750937 2316558159573506697563203)
                ·
                  refine ⟨3474837239360260046344805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316558159573506697563203 3474837239360260046344805)
                  ·
                    refine ⟨651531982380048758689651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474837239360260046344805 651531982380048758689651)
                    ·
                      rfl

theorem cell22_1903281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_1903281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903281 prefixEnd_1903281 := by exact prefixLift 1903281
  have htrace : WordTrace (prefixWord ++ tailWord_1903281) baseStart_1903281 baseEnd_1903281 := by
    simpa [prefixWord, tailWord_1903281, baseEnd_1903281] using wordTrace_append hprefix tailTrace_1903281
  have hstable : (prefixWord ++ tailWord_1903281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903281).length < 2 ^ (prefixWord ++ tailWord_1903281).sum := by decide
  have hdescent : baseEnd_1903281 < baseStart_1903281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903350 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1903350 : Nat := 118140960795 + 1903350 * 2 ^ 59
def prefixEnd_1903350 : Nat := 4983230072969 + 3 ^ 40 * 1903350 * 2
def baseEnd_1903350 : Nat := 651555602490155578714439

theorem tailTrace_1903350 : CollatzResearch.WordTrace tailWord_1903350 prefixEnd_1903350 651555602490155578714439 := by
  unfold tailWord_1903350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338804853405968196578719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46280585102996994096839669 4338804853405968196578719)
  ·
    refine ⟨6508207280108952294868079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4338804853405968196578719 6508207280108952294868079)
    ·
      refine ⟨9762310920163428442302119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508207280108952294868079 9762310920163428442302119)
      ·
        refine ⟨14643466380245142663453179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762310920163428442302119 14643466380245142663453179)
        ·
          refine ⟨21965199570367713995179769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643466380245142663453179 21965199570367713995179769)
          ·
            refine ⟨16473899677775785496384827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21965199570367713995179769 16473899677775785496384827)
            ·
              refine ⟨24710849516663678244577241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16473899677775785496384827 24710849516663678244577241)
              ·
                refine ⟨18533137137497758683432931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24710849516663678244577241 18533137137497758683432931)
                ·
                  refine ⟨27799705706246638025149397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533137137497758683432931 27799705706246638025149397)
                  ·
                    refine ⟨651555602490155578714439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27799705706246638025149397 651555602490155578714439)
                    ·
                      rfl

theorem cell22_1903350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1903350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903350 prefixEnd_1903350 := by exact prefixLift 1903350
  have htrace : WordTrace (prefixWord ++ tailWord_1903350) baseStart_1903350 baseEnd_1903350 := by
    simpa [prefixWord, tailWord_1903350, baseEnd_1903350] using wordTrace_append hprefix tailTrace_1903350
  have hstable : (prefixWord ++ tailWord_1903350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903350).length < 2 ^ (prefixWord ++ tailWord_1903350).sum := by decide
  have hdescent : baseEnd_1903350 < baseStart_1903350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903363 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 10]
def baseStart_1903363 : Nat := 118140960795 + 1903363 * 2 ^ 59
def prefixEnd_1903363 : Nat := 4983230072969 + 3 ^ 40 * 1903363 * 2
def baseEnd_1903363 : Nat := 217186684218609292713133

theorem tailTrace_1903363 : CollatzResearch.WordTrace tailWord_1903363 prefixEnd_1903363 217186684218609292713133 := by
  unfold tailWord_1903363
  simp only [CollatzResearch.WordTrace]
  refine ⟨69421351803448394365482743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46280901202298929576988495 69421351803448394365482743)
  ·
    refine ⟨104132027705172591548224115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69421351803448394365482743 104132027705172591548224115)
    ·
      refine ⟨156198041557758887322336173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104132027705172591548224115 156198041557758887322336173)
      ·
        refine ⟨58574265584159582745876065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156198041557758887322336173 58574265584159582745876065)
        ·
          refine ⟨43930699188119687059407049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58574265584159582745876065 43930699188119687059407049)
          ·
            refine ⟨32948024391089765294555287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43930699188119687059407049 32948024391089765294555287)
            ·
              refine ⟨49422036586634647941832931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32948024391089765294555287 49422036586634647941832931)
              ·
                refine ⟨74133054879951971912749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49422036586634647941832931 74133054879951971912749397)
                ·
                  refine ⟨217186684218609292713133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74133054879951971912749397 217186684218609292713133)
                  ·
                    rfl

theorem cell22_1903363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_1903363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903363 prefixEnd_1903363 := by exact prefixLift 1903363
  have htrace : WordTrace (prefixWord ++ tailWord_1903363) baseStart_1903363 baseEnd_1903363 := by
    simpa [prefixWord, tailWord_1903363, baseEnd_1903363] using wordTrace_append hprefix tailTrace_1903363
  have hstable : (prefixWord ++ tailWord_1903363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903363).length < 2 ^ (prefixWord ++ tailWord_1903363).sum := by decide
  have hdescent : baseEnd_1903363 < baseStart_1903363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903410 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1903410 : Nat := 118140960795 + 1903410 * 2 ^ 59
def prefixEnd_1903410 : Nat := 4983230072969 + 3 ^ 40 * 1903410 * 2
def baseEnd_1903410 : Nat := 651576141716335422214255

theorem tailTrace_1903410 : CollatzResearch.WordTrace tailWord_1903410 prefixEnd_1903410 651576141716335422214255 := by
  unfold tailWord_1903410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355766508569530348110921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46282044022852080928295789 17355766508569530348110921)
  ·
    refine ⟨13016824881427147761083191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17355766508569530348110921 13016824881427147761083191)
    ·
      refine ⟨19525237322140721641624787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016824881427147761083191 19525237322140721641624787)
      ·
        refine ⟨29287855983211082462437181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525237322140721641624787 29287855983211082462437181)
        ·
          refine ⟨10982945993704155923413943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29287855983211082462437181 10982945993704155923413943)
          ·
            refine ⟨16474418990556233885120915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982945993704155923413943 16474418990556233885120915)
            ·
              refine ⟨24711628485834350827681373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474418990556233885120915 24711628485834350827681373)
              ·
                refine ⟨9266860682187881560380515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24711628485834350827681373 9266860682187881560380515)
                ·
                  refine ⟨13900291023281822340570773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266860682187881560380515 13900291023281822340570773)
                  ·
                    refine ⟨651576141716335422214255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13900291023281822340570773 651576141716335422214255)
                    ·
                      rfl

theorem cell22_1903410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1903410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903410 prefixEnd_1903410 := by exact prefixLift 1903410
  have htrace : WordTrace (prefixWord ++ tailWord_1903410) baseStart_1903410 baseEnd_1903410 := by
    simpa [prefixWord, tailWord_1903410, baseEnd_1903410] using wordTrace_append hprefix tailTrace_1903410
  have hstable : (prefixWord ++ tailWord_1903410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903410).length < 2 ^ (prefixWord ++ tailWord_1903410).sum := by decide
  have hdescent : baseEnd_1903410 < baseStart_1903410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903517 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1903517 : Nat := 118140960795 + 1903517 * 2 ^ 59
def prefixEnd_1903517 : Nat := 4983230072969 + 3 ^ 40 * 1903517 * 2
def baseEnd_1903517 : Nat := 651612770003022809788927

theorem tailTrace_1903517 : CollatzResearch.WordTrace tailWord_1903517 prefixEnd_1903517 651612770003022809788927 := by
  unfold tailWord_1903517
  simp only [CollatzResearch.WordTrace]
  refine ⟨69426968644890478666588805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46284645763260319111059203 69426968644890478666588805)
  ·
    refine ⟨13017556620916964749985401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69426968644890478666588805 13017556620916964749985401)
    ·
      refine ⟨9763167465687723562489051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13017556620916964749985401 9763167465687723562489051)
      ·
        refine ⟨14644751198531585343733577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763167465687723562489051 14644751198531585343733577)
        ·
          refine ⟨10983563398898689007800183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644751198531585343733577 10983563398898689007800183)
          ·
            refine ⟨16475345098348033511700275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983563398898689007800183 16475345098348033511700275)
            ·
              refine ⟨24713017647522050267550413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475345098348033511700275 24713017647522050267550413)
              ·
                refine ⟨9267381617820768850331405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24713017647522050267550413 9267381617820768850331405)
                ·
                  refine ⟨3475268106682788318874277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9267381617820768850331405 3475268106682788318874277)
                  ·
                    refine ⟨651612770003022809788927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3475268106682788318874277 651612770003022809788927)
                    ·
                      rfl

theorem cell22_1903517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1903517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903517 prefixEnd_1903517 := by exact prefixLift 1903517
  have htrace : WordTrace (prefixWord ++ tailWord_1903517) baseStart_1903517 baseEnd_1903517 := by
    simpa [prefixWord, tailWord_1903517, baseEnd_1903517] using wordTrace_append hprefix tailTrace_1903517
  have hstable : (prefixWord ++ tailWord_1903517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903517).length < 2 ^ (prefixWord ++ tailWord_1903517).sum := by decide
  have hdescent : baseEnd_1903517 < baseStart_1903517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903549 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1903549 : Nat := 118140960795 + 1903549 * 2 ^ 59
def prefixEnd_1903549 : Nat := 4983230072969 + 3 ^ 40 * 1903549 * 2
def baseEnd_1903549 : Nat := 217207908085661797662943

theorem tailTrace_1903549 : CollatzResearch.WordTrace tailWord_1903549 prefixEnd_1903549 217207908085661797662943 := by
  unfold tailWord_1903549
  simp only [CollatzResearch.WordTrace]
  refine ⟨69428135780774548131753701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46285423853849698754502467 69428135780774548131753701)
  ·
    refine ⟨13017775458895227774703819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69428135780774548131753701 13017775458895227774703819)
    ·
      refine ⟨19526663188342841662055729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13017775458895227774703819 19526663188342841662055729)
      ·
        refine ⟨14644997391257131246541797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19526663188342841662055729 14644997391257131246541797)
        ·
          refine ⟨2745937010860712108726587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14644997391257131246541797 2745937010860712108726587)
          ·
            refine ⟨4118905516291068163089881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745937010860712108726587 4118905516291068163089881)
            ·
              refine ⟨3089179137218301122317411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118905516291068163089881 3089179137218301122317411)
              ·
                refine ⟨4633768705827451683476117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089179137218301122317411 4633768705827451683476117)
                ·
                  refine ⟨217207908085661797662943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4633768705827451683476117 217207908085661797662943)
                  ·
                    rfl

theorem cell22_1903549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1903549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903549 prefixEnd_1903549 := by exact prefixLift 1903549
  have htrace : WordTrace (prefixWord ++ tailWord_1903549) baseStart_1903549 baseEnd_1903549 := by
    simpa [prefixWord, tailWord_1903549, baseEnd_1903549] using wordTrace_append hprefix tailTrace_1903549
  have hstable : (prefixWord ++ tailWord_1903549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903549).length < 2 ^ (prefixWord ++ tailWord_1903549).sum := by decide
  have hdescent : baseEnd_1903549 < baseStart_1903549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903577 : List Nat := [1, 2, 1, 2, 5, 2, 1, 8]
def baseStart_1903577 : Nat := 118140960795 + 1903577 * 2 ^ 59
def prefixEnd_1903577 : Nat := 4983230072969 + 3 ^ 40 * 1903577 * 2
def baseEnd_1903577 : Nat := 72403701025466961476527

theorem tailTrace_1903577 : CollatzResearch.WordTrace tailWord_1903577 prefixEnd_1903577 72403701025466961476527 := by
  unfold tailWord_1903577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429157024673108913772985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46286104683115405942515323 69429157024673108913772985)
  ·
    refine ⟨52071867768504831685329739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69429157024673108913772985 52071867768504831685329739)
    ·
      refine ⟨78107801652757247527994609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52071867768504831685329739 78107801652757247527994609)
      ·
        refine ⟨58580851239567935645995957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78107801652757247527994609 58580851239567935645995957)
        ·
          refine ⟨5491954803709493966812121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58580851239567935645995957 5491954803709493966812121)
          ·
            refine ⟨4118966102782120475109091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491954803709493966812121 4118966102782120475109091)
            ·
              refine ⟨6178449154173180712663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118966102782120475109091 6178449154173180712663637)
              ·
                refine ⟨72403701025466961476527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6178449154173180712663637 72403701025466961476527)
                ·
                  rfl

theorem cell22_1903577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 8].length) (baseStart_1903577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903577 prefixEnd_1903577 := by exact prefixLift 1903577
  have htrace : WordTrace (prefixWord ++ tailWord_1903577) baseStart_1903577 baseEnd_1903577 := by
    simpa [prefixWord, tailWord_1903577, baseEnd_1903577] using wordTrace_append hprefix tailTrace_1903577
  have hstable : (prefixWord ++ tailWord_1903577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903577).length < 2 ^ (prefixWord ++ tailWord_1903577).sum := by decide
  have hdescent : baseEnd_1903577 < baseStart_1903577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903583 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 4]
def baseStart_1903583 : Nat := 118140960795 + 1903583 * 2 ^ 59
def prefixEnd_1903583 : Nat := 4983230072969 + 3 ^ 40 * 1903583 * 2
def baseEnd_1903583 : Nat := 217211787717273545879575

theorem tailTrace_1903583 : CollatzResearch.WordTrace tailWord_1903583 prefixEnd_1903583 217211787717273545879575 := by
  unfold tailWord_1903583
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429375862651371938491403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46286250575100914625660935 69429375862651371938491403)
  ·
    refine ⟨104144063793977057907737105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69429375862651371938491403 104144063793977057907737105)
    ·
      refine ⟨78108047845482793430802829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104144063793977057907737105 78108047845482793430802829)
      ·
        refine ⟨29290517942056047536551061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78108047845482793430802829 29290517942056047536551061)
        ·
          refine ⟨1372993028533877228275831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29290517942056047536551061 1372993028533877228275831)
          ·
            refine ⟨2059489542800815842413747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372993028533877228275831 2059489542800815842413747)
            ·
              refine ⟨3089234314201223763620621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059489542800815842413747 3089234314201223763620621)
              ·
                refine ⟨1158462867825458911357733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3089234314201223763620621 1158462867825458911357733)
                ·
                  refine ⟨217211787717273545879575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158462867825458911357733 217211787717273545879575)
                  ·
                    rfl

theorem cell22_1903583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 4].length) (baseStart_1903583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903583 prefixEnd_1903583 := by exact prefixLift 1903583
  have htrace : WordTrace (prefixWord ++ tailWord_1903583) baseStart_1903583 baseEnd_1903583 := by
    simpa [prefixWord, tailWord_1903583, baseEnd_1903583] using wordTrace_append hprefix tailTrace_1903583
  have hstable : (prefixWord ++ tailWord_1903583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903583).length < 2 ^ (prefixWord ++ tailWord_1903583).sum := by decide
  have hdescent : baseEnd_1903583 < baseStart_1903583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903667 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 6]
def baseStart_1903667 : Nat := 118140960795 + 1903667 * 2 ^ 59
def prefixEnd_1903667 : Nat := 4983230072969 + 3 ^ 40 * 1903667 * 2
def baseEnd_1903667 : Nat := 217221372689490806179489

theorem tailTrace_1903667 : CollatzResearch.WordTrace tailWord_1903667 prefixEnd_1903667 217221372689490806179489 := by
  unfold tailWord_1903667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69432439594347054284549255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46288293062898036189699503 69432439594347054284549255)
  ·
    refine ⟨104148659391520581426823883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69432439594347054284549255 104148659391520581426823883)
    ·
      refine ⟨156222989087280872140235825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104148659391520581426823883 156222989087280872140235825)
      ·
        refine ⟨117167241815460654105176869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156222989087280872140235825 117167241815460654105176869)
        ·
          refine ⟨21968857840398872644720663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117167241815460654105176869 21968857840398872644720663)
          ·
            refine ⟨32953286760598308967080995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21968857840398872644720663 32953286760598308967080995)
            ·
              refine ⟨49429930140897463450621493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32953286760598308967080995 49429930140897463450621493)
              ·
                refine ⟨4634055950709137198495765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49429930140897463450621493 4634055950709137198495765)
                ·
                  refine ⟨217221372689490806179489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4634055950709137198495765 217221372689490806179489)
                  ·
                    rfl

theorem cell22_1903667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_1903667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903667 prefixEnd_1903667 := by exact prefixLift 1903667
  have htrace : WordTrace (prefixWord ++ tailWord_1903667) baseStart_1903667 baseEnd_1903667 := by
    simpa [prefixWord, tailWord_1903667, baseEnd_1903667] using wordTrace_append hprefix tailTrace_1903667
  have hstable : (prefixWord ++ tailWord_1903667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903667).length < 2 ^ (prefixWord ++ tailWord_1903667).sum := by decide
  have hdescent : baseEnd_1903667 < baseStart_1903667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903701 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 4]
def baseStart_1903701 : Nat := 118140960795 + 1903701 * 2 ^ 59
def prefixEnd_1903701 : Nat := 4983230072969 + 3 ^ 40 * 1903701 * 2
def baseEnd_1903701 : Nat := 217225252321102554396121

theorem tailTrace_1903701 : CollatzResearch.WordTrace tailWord_1903701 prefixEnd_1903701 217225252321102554396121 := by
  unfold tailWord_1903701
  simp only [CollatzResearch.WordTrace]
  refine ⟨69433679676223878091286957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46289119784149252060857971 69433679676223878091286957)
  ·
    refine ⟨26037629878583954284232609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69433679676223878091286957 26037629878583954284232609)
    ·
      refine ⟨19528222408937965713174457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26037629878583954284232609 19528222408937965713174457)
      ·
        refine ⟨14646166806703474284880843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19528222408937965713174457 14646166806703474284880843)
        ·
          refine ⟨21969250210055211427321265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646166806703474284880843 21969250210055211427321265)
          ·
            refine ⟨16476937657541408570490949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21969250210055211427321265 16476937657541408570490949)
            ·
              refine ⟨3089425810789014106967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16476937657541408570490949 3089425810789014106967053)
              ·
                refine ⟨1158534679045880290112645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3089425810789014106967053 1158534679045880290112645)
                ·
                  refine ⟨217225252321102554396121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158534679045880290112645 217225252321102554396121)
                  ·
                    rfl

theorem cell22_1903701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_1903701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903701 prefixEnd_1903701 := by exact prefixLift 1903701
  have htrace : WordTrace (prefixWord ++ tailWord_1903701) baseStart_1903701 baseEnd_1903701 := by
    simpa [prefixWord, tailWord_1903701, baseEnd_1903701] using wordTrace_append hprefix tailTrace_1903701
  have hstable : (prefixWord ++ tailWord_1903701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903701).length < 2 ^ (prefixWord ++ tailWord_1903701).sum := by decide
  have hdescent : baseEnd_1903701 < baseStart_1903701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903712 : List Nat := [2, 1, 1, 3, 2, 2, 11]
def baseStart_1903712 : Nat := 118140960795 + 1903712 * 2 ^ 59
def prefixEnd_1903712 : Nat := 4983230072969 + 3 ^ 40 * 1903712 * 2
def baseEnd_1903712 : Nat := 24136278610670640783827

theorem tailTrace_1903712 : CollatzResearch.WordTrace tailWord_1903712 prefixEnd_1903712 24136278610670640783827 := by
  unfold tailWord_1903712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717040439592013484968695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46289387252789351313291593 34717040439592013484968695)
  ·
    refine ⟨52075560659388020227453043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34717040439592013484968695 52075560659388020227453043)
    ·
      refine ⟨78113340989082030341179565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52075560659388020227453043 78113340989082030341179565)
      ·
        refine ⟨29292502870905761377942337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78113340989082030341179565 29292502870905761377942337)
        ·
          refine ⟨21969377153179321033456753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29292502870905761377942337 21969377153179321033456753)
          ·
            refine ⟨16477032864884490775092565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21969377153179321033456753 16477032864884490775092565)
            ·
              refine ⟨24136278610670640783827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16477032864884490775092565 24136278610670640783827)
              ·
                rfl

theorem cell22_1903712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 11].length) (baseStart_1903712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903712 prefixEnd_1903712 := by exact prefixLift 1903712
  have htrace : WordTrace (prefixWord ++ tailWord_1903712) baseStart_1903712 baseEnd_1903712 := by
    simpa [prefixWord, tailWord_1903712, baseEnd_1903712] using wordTrace_append hprefix tailTrace_1903712
  have hstable : (prefixWord ++ tailWord_1903712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903712).length < 2 ^ (prefixWord ++ tailWord_1903712).sum := by decide
  have hdescent : baseEnd_1903712 < baseStart_1903712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903791 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 5]
def baseStart_1903791 : Nat := 118140960795 + 1903791 * 2 ^ 59
def prefixEnd_1903791 : Nat := 4983230072969 + 3 ^ 40 * 1903791 * 2
def baseEnd_1903791 : Nat := 217235521934192476146029

theorem tailTrace_1903791 : CollatzResearch.WordTrace tailWord_1903791 prefixEnd_1903791 217235521934192476146029 := by
  unfold tailWord_1903791
  simp only [CollatzResearch.WordTrace]
  refine ⟨69436962245897823462063227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46291308163931882308042151 69436962245897823462063227)
  ·
    refine ⟨104155443368846735193094841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69436962245897823462063227 104155443368846735193094841)
    ·
      refine ⟨78116582526635051394821131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104155443368846735193094841 78116582526635051394821131)
      ·
        refine ⟨117174873789952577092231697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78116582526635051394821131 117174873789952577092231697)
        ·
          refine ⟨87881155342464432819173773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117174873789952577092231697 87881155342464432819173773)
          ·
            refine ⟨32955433253424162307190165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87881155342464432819173773 32955433253424162307190165)
            ·
              refine ⟨1544785933754257608149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32955433253424162307190165 1544785933754257608149539)
              ·
                refine ⟨2317178900631386412224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544785933754257608149539 2317178900631386412224309)
                ·
                  refine ⟨217235521934192476146029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317178900631386412224309 217235521934192476146029)
                  ·
                    rfl

theorem cell22_1903791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 5].length) (baseStart_1903791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903791 prefixEnd_1903791 := by exact prefixLift 1903791
  have htrace : WordTrace (prefixWord ++ tailWord_1903791) baseStart_1903791 baseEnd_1903791 := by
    simpa [prefixWord, tailWord_1903791, baseEnd_1903791] using wordTrace_append hprefix tailTrace_1903791
  have hstable : (prefixWord ++ tailWord_1903791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903791).length < 2 ^ (prefixWord ++ tailWord_1903791).sum := by decide
  have hdescent : baseEnd_1903791 < baseStart_1903791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903834 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1903834 : Nat := 118140960795 + 1903834 * 2 ^ 59
def prefixEnd_1903834 : Nat := 4983230072969 + 3 ^ 40 * 1903834 * 2
def baseEnd_1903834 : Nat := 651721285581339649612955

theorem tailTrace_1903834 : CollatzResearch.WordTrace tailWord_1903834 prefixEnd_1903834 651721285581339649612955 := by
  unfold tailWord_1903834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359632646185510451469639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46292353723161361203919037 17359632646185510451469639)
  ·
    refine ⟨26039448969278265677204459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17359632646185510451469639 26039448969278265677204459)
    ·
      refine ⟨39059173453917398515806689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039448969278265677204459 39059173453917398515806689)
      ·
        refine ⟨29294380090438048886855017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39059173453917398515806689 29294380090438048886855017)
        ·
          refine ⟨21970785067828536665141263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29294380090438048886855017 21970785067828536665141263)
          ·
            refine ⟨32956177601742804997711895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21970785067828536665141263 32956177601742804997711895)
            ·
              refine ⟨49434266402614207496567843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32956177601742804997711895 49434266402614207496567843)
              ·
                refine ⟨74151399603921311244851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49434266402614207496567843 74151399603921311244851765)
                ·
                  refine ⟨6951693712867622929204853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74151399603921311244851765 6951693712867622929204853)
                  ·
                    refine ⟨651721285581339649612955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6951693712867622929204853 651721285581339649612955)
                    ·
                      rfl

theorem cell22_1903834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1903834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903834 prefixEnd_1903834 := by exact prefixLift 1903834
  have htrace : WordTrace (prefixWord ++ tailWord_1903834) baseStart_1903834 baseEnd_1903834 := by
    simpa [prefixWord, tailWord_1903834, baseEnd_1903834] using wordTrace_append hprefix tailTrace_1903834
  have hstable : (prefixWord ++ tailWord_1903834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903834).length < 2 ^ (prefixWord ++ tailWord_1903834).sum := by decide
  have hdescent : baseEnd_1903834 < baseStart_1903834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903851 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_1903851 : Nat := 118140960795 + 1903851 * 2 ^ 59
def prefixEnd_1903851 : Nat := 4983230072969 + 3 ^ 40 * 1903851 * 2
def baseEnd_1903851 : Nat := 651727105028757271937903

theorem tailTrace_1903851 : CollatzResearch.WordTrace tailWord_1903851 prefixEnd_1903851 651727105028757271937903 := by
  unfold tailWord_1903851
  simp only [CollatzResearch.WordTrace]
  refine ⟨69439150625680453709247407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46292767083786969139498271 69439150625680453709247407)
  ·
    refine ⟨104158725938520680563871111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69439150625680453709247407 104158725938520680563871111)
    ·
      refine ⟨156238088907781020845806667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104158725938520680563871111 156238088907781020845806667)
      ·
        refine ⟨234357133361671531268710001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156238088907781020845806667 234357133361671531268710001)
        ·
          refine ⟨175767850021253648451532501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234357133361671531268710001 175767850021253648451532501)
          ·
            refine ⟨4119558984873132385582793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175767850021253648451532501 4119558984873132385582793)
            ·
              refine ⟨3089669238654849289187095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119558984873132385582793 3089669238654849289187095)
              ·
                refine ⟨4634503857982273933780643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089669238654849289187095 4634503857982273933780643)
                ·
                  refine ⟨6951755786973410900670965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634503857982273933780643 6951755786973410900670965)
                  ·
                    refine ⟨651727105028757271937903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6951755786973410900670965 651727105028757271937903)
                    ·
                      rfl

theorem cell22_1903851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_1903851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903851 prefixEnd_1903851 := by exact prefixLift 1903851
  have htrace : WordTrace (prefixWord ++ tailWord_1903851) baseStart_1903851 baseEnd_1903851 := by
    simpa [prefixWord, tailWord_1903851, baseEnd_1903851] using wordTrace_append hprefix tailTrace_1903851
  have hstable : (prefixWord ++ tailWord_1903851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903851).length < 2 ^ (prefixWord ++ tailWord_1903851).sum := by decide
  have hdescent : baseEnd_1903851 < baseStart_1903851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903870 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1903870 : Nat := 118140960795 + 1903870 * 2 ^ 59
def prefixEnd_1903870 : Nat := 4983230072969 + 3 ^ 40 * 1903870 * 2
def baseEnd_1903870 : Nat := 217244536372349185237615

theorem tailTrace_1903870 : CollatzResearch.WordTrace tailWord_1903870 prefixEnd_1903870 217244536372349185237615 := by
  unfold tailWord_1903870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679980451576452494273633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46293229075074413302792709 8679980451576452494273633)
  ·
    refine ⟨6509985338682339370705225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8679980451576452494273633 6509985338682339370705225)
    ·
      refine ⟨4882489004011754528028919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509985338682339370705225 4882489004011754528028919)
      ·
        refine ⟨7323733506017631792043379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882489004011754528028919 7323733506017631792043379)
        ·
          refine ⟨10985600259026447688065069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323733506017631792043379 10985600259026447688065069)
          ·
            refine ⟨4119600097134917883024401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10985600259026447688065069 4119600097134917883024401)
            ·
              refine ⟨3089700072851188412268301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119600097134917883024401 3089700072851188412268301)
              ·
                refine ⟨1158637527319195654600613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3089700072851188412268301 1158637527319195654600613)
                ·
                  refine ⟨217244536372349185237615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158637527319195654600613 217244536372349185237615)
                  ·
                    rfl

theorem cell22_1903870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1903870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903870 prefixEnd_1903870 := by exact prefixLift 1903870
  have htrace : WordTrace (prefixWord ++ tailWord_1903870) baseStart_1903870 baseEnd_1903870 := by
    simpa [prefixWord, tailWord_1903870, baseEnd_1903870] using wordTrace_append hprefix tailTrace_1903870
  have hstable : (prefixWord ++ tailWord_1903870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903870).length < 2 ^ (prefixWord ++ tailWord_1903870).sum := by decide
  have hdescent : baseEnd_1903870 < baseStart_1903870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903902 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1903902 : Nat := 118140960795 + 1903902 * 2 ^ 59
def prefixEnd_1903902 : Nat := 4983230072969 + 3 ^ 40 * 1903902 * 2
def baseEnd_1903902 : Nat := 651744563371010138912747

theorem tailTrace_1903902 : CollatzResearch.WordTrace tailWord_1903902 prefixEnd_1903902 651744563371010138912747 := by
  unfold tailWord_1903902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680126343561961177419245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46294007165663792946235973 8680126343561961177419245)
  ·
    refine ⟨3255047378835735441532217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8680126343561961177419245 3255047378835735441532217)
    ·
      refine ⟨2441285534126801581149163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255047378835735441532217 2441285534126801581149163)
      ·
        refine ⟨3661928301190202371723745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441285534126801581149163 3661928301190202371723745)
        ·
          refine ⟨2746446225892651778792809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3661928301190202371723745 2746446225892651778792809)
          ·
            refine ⟨2059834669419488834094607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746446225892651778792809 2059834669419488834094607)
            ·
              refine ⟨3089752004129233251141911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059834669419488834094607 3089752004129233251141911)
              ·
                refine ⟨4634628006193849876712867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089752004129233251141911 4634628006193849876712867)
                ·
                  refine ⟨6951942009290774815069301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634628006193849876712867 6951942009290774815069301)
                  ·
                    refine ⟨651744563371010138912747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6951942009290774815069301 651744563371010138912747)
                    ·
                      rfl

theorem cell22_1903902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1903902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903902 prefixEnd_1903902 := by exact prefixLift 1903902
  have htrace : WordTrace (prefixWord ++ tailWord_1903902) baseStart_1903902 baseEnd_1903902 := by
    simpa [prefixWord, tailWord_1903902, baseEnd_1903902] using wordTrace_append hprefix tailTrace_1903902
  have hstable : (prefixWord ++ tailWord_1903902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903902).length < 2 ^ (prefixWord ++ tailWord_1903902).sum := by decide
  have hdescent : baseEnd_1903902 < baseStart_1903902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903998 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1903998 : Nat := 118140960795 + 1903998 * 2 ^ 59
def prefixEnd_1903998 : Nat := 4983230072969 + 3 ^ 40 * 1903998 * 2
def baseEnd_1903998 : Nat := 651777426132897888512453

theorem tailTrace_1903998 : CollatzResearch.WordTrace tailWord_1903998 prefixEnd_1903998 651777426132897888512453 := by
  unfold tailWord_1903998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680564019518487226856081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46296341437431931876565765 8680564019518487226856081)
  ·
    refine ⟨6510423014638865420142061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8680564019518487226856081 6510423014638865420142061)
    ·
      refine ⟨2441408630489574532553273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6510423014638865420142061 2441408630489574532553273)
      ·
        refine ⟨1831056472867180899414955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441408630489574532553273 1831056472867180899414955)
        ·
          refine ⟨2746584709300771349122433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831056472867180899414955 2746584709300771349122433)
          ·
            refine ⟨2059938531975578511841825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746584709300771349122433 2059938531975578511841825)
            ·
              refine ⟨1544953898981683883881369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059938531975578511841825 1544953898981683883881369)
              ·
                refine ⟨1158715424236262912911027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544953898981683883881369 1158715424236262912911027)
                ·
                  refine ⟨1738073136354394369366541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158715424236262912911027 1738073136354394369366541)
                  ·
                    refine ⟨651777426132897888512453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738073136354394369366541 651777426132897888512453)
                    ·
                      rfl

theorem cell22_1903998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1903998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1903998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1903998 prefixEnd_1903998 := by exact prefixLift 1903998
  have htrace : WordTrace (prefixWord ++ tailWord_1903998) baseStart_1903998 baseEnd_1903998 := by
    simpa [prefixWord, tailWord_1903998, baseEnd_1903998] using wordTrace_append hprefix tailTrace_1903998
  have hstable : (prefixWord ++ tailWord_1903998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903998).length < 2 ^ (prefixWord ++ tailWord_1903998).sum := by decide
  have hdescent : baseEnd_1903998 < baseStart_1903998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904005 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 4]
def baseStart_1904005 : Nat := 118140960795 + 1904005 * 2 ^ 59
def prefixEnd_1904005 : Nat := 4983230072969 + 3 ^ 40 * 1904005 * 2
def baseEnd_1904005 : Nat := 217259940791984067862477

theorem tailTrace_1904005 : CollatzResearch.WordTrace tailWord_1904005 prefixEnd_1904005 217259940791984067862477 := by
  unfold tailWord_1904005
  simp only [CollatzResearch.WordTrace]
  refine ⟨69444767467122538010353469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46296511644748358673568979 69444767467122538010353469)
  ·
    refine ⟨26041787800170951753882551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69444767467122538010353469 26041787800170951753882551)
    ·
      refine ⟨39062681700256427630823827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26041787800170951753882551 39062681700256427630823827)
      ·
        refine ⟨58594022550384641446235741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39062681700256427630823827 58594022550384641446235741)
        ·
          refine ⟨21972758456394240542338403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58594022550384641446235741 21972758456394240542338403)
          ·
            refine ⟨32959137684591360813507605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972758456394240542338403 32959137684591360813507605)
            ·
              refine ⟨1544959578965220038133169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32959137684591360813507605 1544959578965220038133169)
              ·
                refine ⟨1158719684223915028599877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544959578965220038133169 1158719684223915028599877)
                ·
                  refine ⟨217259940791984067862477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158719684223915028599877 217259940791984067862477)
                  ·
                    rfl

theorem cell22_1904005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_1904005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904005 prefixEnd_1904005 := by exact prefixLift 1904005
  have htrace : WordTrace (prefixWord ++ tailWord_1904005) baseStart_1904005 baseEnd_1904005 := by
    simpa [prefixWord, tailWord_1904005, baseEnd_1904005] using wordTrace_append hprefix tailTrace_1904005
  have hstable : (prefixWord ++ tailWord_1904005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904005).length < 2 ^ (prefixWord ++ tailWord_1904005).sum := by decide
  have hdescent : baseEnd_1904005 < baseStart_1904005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904020 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1904020 : Nat := 118140960795 + 1904020 * 2 ^ 59
def prefixEnd_1904020 : Nat := 4983230072969 + 3 ^ 40 * 1904020 * 2
def baseEnd_1904020 : Nat := 651784957182497164462385

theorem tailTrace_1904020 : CollatzResearch.WordTrace tailWord_1904020 prefixEnd_1904020 651784957182497164462385 := by
  unfold tailWord_1904020
  simp only [CollatzResearch.WordTrace]
  refine ⟨34722657281034097786074757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46296876374712130381433009 34722657281034097786074757)
  ·
    refine ⟨6510498240193893334889017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34722657281034097786074757 6510498240193893334889017)
    ·
      refine ⟨4882873680145420001166763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6510498240193893334889017 4882873680145420001166763)
      ·
        refine ⟨7324310520218130001750145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882873680145420001166763 7324310520218130001750145)
        ·
          refine ⟨5493232890163597501312609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324310520218130001750145 5493232890163597501312609)
          ·
            refine ⟨4119924667622698125984457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5493232890163597501312609 4119924667622698125984457)
            ·
              refine ⟨3089943500717023594488343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119924667622698125984457 3089943500717023594488343)
              ·
                refine ⟨4634915251075535391732515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089943500717023594488343 4634915251075535391732515)
                ·
                  refine ⟨6952372876613303087598773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634915251075535391732515 6952372876613303087598773)
                  ·
                    refine ⟨651784957182497164462385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6952372876613303087598773 651784957182497164462385)
                    ·
                      rfl

theorem cell22_1904020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1904020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904020 prefixEnd_1904020 := by exact prefixLift 1904020
  have htrace : WordTrace (prefixWord ++ tailWord_1904020) baseStart_1904020 baseEnd_1904020 := by
    simpa [prefixWord, tailWord_1904020, baseEnd_1904020] using wordTrace_append hprefix tailTrace_1904020
  have hstable : (prefixWord ++ tailWord_1904020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904020).length < 2 ^ (prefixWord ++ tailWord_1904020).sum := by decide
  have hdescent : baseEnd_1904020 < baseStart_1904020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904078 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1904078 : Nat := 118140960795 + 1904078 * 2 ^ 59
def prefixEnd_1904078 : Nat := 4983230072969 + 3 ^ 40 * 1904078 * 2
def baseEnd_1904078 : Nat := 217268270589268115504069

theorem tailTrace_1904078 : CollatzResearch.WordTrace tailWord_1904078 prefixEnd_1904078 217268270589268115504069 := by
  unfold tailWord_1904078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680928749482258934720111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46298286663905380985173925 8680928749482258934720111)
  ·
    refine ⟨13021393124223388402080167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680928749482258934720111 13021393124223388402080167)
    ·
      refine ⟨19532089686335082603120251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021393124223388402080167 19532089686335082603120251)
      ·
        refine ⟨29298134529502623904680377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532089686335082603120251 29298134529502623904680377)
        ·
          refine ⟨21973600897126967928510283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298134529502623904680377 21973600897126967928510283)
          ·
            refine ⟨32960401345690451892765425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21973600897126967928510283 32960401345690451892765425)
            ·
              refine ⟨24720301009267838919574069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32960401345690451892765425 24720301009267838919574069)
              ·
                refine ⟨2317528219618859898710069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24720301009267838919574069 2317528219618859898710069)
                ·
                  refine ⟨217268270589268115504069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317528219618859898710069 217268270589268115504069)
                  ·
                    rfl

theorem cell22_1904078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1904078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904078 prefixEnd_1904078 := by exact prefixLift 1904078
  have htrace : WordTrace (prefixWord ++ tailWord_1904078) baseStart_1904078 baseEnd_1904078 := by
    simpa [prefixWord, tailWord_1904078, baseEnd_1904078] using wordTrace_append hprefix tailTrace_1904078
  have hstable : (prefixWord ++ tailWord_1904078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904078).length < 2 ^ (prefixWord ++ tailWord_1904078).sum := by decide
  have hdescent : baseEnd_1904078 < baseStart_1904078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904099 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 1, 3]
def baseStart_1904099 : Nat := 118140960795 + 1904099 * 2 ^ 59
def prefixEnd_1904099 : Nat := 4983230072969 + 3 ^ 40 * 1904099 * 2
def baseEnd_1904099 : Nat := 651812000496967291737143

theorem tailTrace_1904099 : CollatzResearch.WordTrace tailWord_1904099 prefixEnd_1904099 651812000496967291737143 := by
  unfold tailWord_1904099
  simp only [CollatzResearch.WordTrace]
  refine ⟨69448195928781992064275351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46298797285854661376183567 69448195928781992064275351)
  ·
    refine ⟨104172293893172988096413027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69448195928781992064275351 104172293893172988096413027)
    ·
      refine ⟨156258440839759482144619541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104172293893172988096413027 156258440839759482144619541)
      ·
        refine ⟨7324614414363725725529041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156258440839759482144619541 7324614414363725725529041)
        ·
          refine ⟨5493460810772794294146781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324614414363725725529041 5493460810772794294146781)
          ·
            refine ⟨2060047804039797860305043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5493460810772794294146781 2060047804039797860305043)
            ·
              refine ⟨3090071706059696790457565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060047804039797860305043 3090071706059696790457565)
              ·
                refine ⟨1158776889772386296421587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3090071706059696790457565 1158776889772386296421587)
                ·
                  refine ⟨1738165334658579444632381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158776889772386296421587 1738165334658579444632381)
                  ·
                    refine ⟨651812000496967291737143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738165334658579444632381 651812000496967291737143)
                    ·
                      rfl

theorem cell22_1904099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 3].length) (baseStart_1904099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904099 prefixEnd_1904099 := by exact prefixLift 1904099
  have htrace : WordTrace (prefixWord ++ tailWord_1904099) baseStart_1904099 baseEnd_1904099 := by
    simpa [prefixWord, tailWord_1904099, baseEnd_1904099] using wordTrace_append hprefix tailTrace_1904099
  have hstable : (prefixWord ++ tailWord_1904099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904099).length < 2 ^ (prefixWord ++ tailWord_1904099).sum := by decide
  have hdescent : baseEnd_1904099 < baseStart_1904099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904129 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 5]
def baseStart_1904129 : Nat := 118140960795 + 1904129 * 2 ^ 59
def prefixEnd_1904129 : Nat := 4983230072969 + 3 ^ 40 * 1904129 * 2
def baseEnd_1904129 : Nat := 217274090036685737829017

theorem tailTrace_1904129 : CollatzResearch.WordTrace tailWord_1904129 prefixEnd_1904129 217274090036685737829017 := by
  unfold tailWord_1904129
  simp only [CollatzResearch.WordTrace]
  refine ⟨69449290118673307187867441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46299526745782204791911627 69449290118673307187867441)
  ·
    refine ⟨52086967589004980390900581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69449290118673307187867441 52086967589004980390900581)
    ·
      refine ⟨9766306422938433823293859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52086967589004980390900581 9766306422938433823293859)
      ·
        refine ⟨14649459634407650734940789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766306422938433823293859 14649459634407650734940789)
        ·
          refine ⟨1373386840725717256400699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14649459634407650734940789 1373386840725717256400699)
          ·
            refine ⟨2060080261088575884601049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373386840725717256400699 2060080261088575884601049)
            ·
              refine ⟨1545060195816431913450787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060080261088575884601049 1545060195816431913450787)
              ·
                refine ⟨2317590293724647870176181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545060195816431913450787 2317590293724647870176181)
                ·
                  refine ⟨217274090036685737829017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317590293724647870176181 217274090036685737829017)
                  ·
                    rfl

theorem cell22_1904129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_1904129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904129 prefixEnd_1904129 := by exact prefixLift 1904129
  have htrace : WordTrace (prefixWord ++ tailWord_1904129) baseStart_1904129 baseEnd_1904129 := by
    simpa [prefixWord, tailWord_1904129, baseEnd_1904129] using wordTrace_append hprefix tailTrace_1904129
  have hstable : (prefixWord ++ tailWord_1904129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904129).length < 2 ^ (prefixWord ++ tailWord_1904129).sum := by decide
  have hdescent : baseEnd_1904129 < baseStart_1904129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904168 : List Nat := [2, 1, 5, 2, 12]
def baseStart_1904168 : Nat := 118140960795 + 1904168 * 2 ^ 59
def prefixEnd_1904168 : Nat := 4983230072969 + 3 ^ 40 * 1904168 * 2
def baseEnd_1904168 : Nat := 2682451113609358484617

theorem tailTrace_1904168 : CollatzResearch.WordTrace tailWord_1904168 prefixEnd_1904168 2682451113609358484617 := by
  unfold tailWord_1904168
  simp only [CollatzResearch.WordTrace]
  refine ⟨34725356282766008424268579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46300475043688011232358105 34725356282766008424268579)
  ·
    refine ⟨52088034424149012636402869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34725356282766008424268579 52088034424149012636402869)
    ·
      refine ⟨4883253227263969934662769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52088034424149012636402869 4883253227263969934662769)
      ·
        refine ⟨3662439920447977450997077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4883253227263969934662769 3662439920447977450997077)
        ·
          refine ⟨2682451113609358484617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3662439920447977450997077 2682451113609358484617)
          ·
            rfl

theorem cell22_1904168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 12].length) (baseStart_1904168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904168 prefixEnd_1904168 := by exact prefixLift 1904168
  have htrace : WordTrace (prefixWord ++ tailWord_1904168) baseStart_1904168 baseEnd_1904168 := by
    simpa [prefixWord, tailWord_1904168, baseEnd_1904168] using wordTrace_append hprefix tailTrace_1904168
  have hstable : (prefixWord ++ tailWord_1904168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904168).length < 2 ^ (prefixWord ++ tailWord_1904168).sum := by decide
  have hdescent : baseEnd_1904168 < baseStart_1904168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904170 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1904170 : Nat := 118140960795 + 1904170 * 2 ^ 59
def prefixEnd_1904170 : Nat := 4983230072969 + 3 ^ 40 * 1904170 * 2
def baseEnd_1904170 : Nat := 651836305247946773211925

theorem tailTrace_1904170 : CollatzResearch.WordTrace tailWord_1904170 prefixEnd_1904170 651836305247946773211925 := by
  unfold tailWord_1904170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17362696377881192797527491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46300523674349847460073309 17362696377881192797527491)
  ·
    refine ⟨26044044566821789196291237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17362696377881192797527491 26044044566821789196291237)
    ·
      refine ⟨4883258356279085474304607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26044044566821789196291237 4883258356279085474304607)
      ·
        refine ⟨7324887534418628211456911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883258356279085474304607 7324887534418628211456911)
        ·
          refine ⟨10987331301627942317185367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324887534418628211456911 10987331301627942317185367)
          ·
            refine ⟨16480996952441913475778051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987331301627942317185367 16480996952441913475778051)
            ·
              refine ⟨24721495428662870213667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16480996952441913475778051 24721495428662870213667077)
              ·
                refine ⟨4635280392874288165062577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24721495428662870213667077 4635280392874288165062577)
                ·
                  refine ⟨3476460294655716123796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635280392874288165062577 3476460294655716123796933)
                  ·
                    refine ⟨651836305247946773211925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476460294655716123796933 651836305247946773211925)
                    ·
                      rfl

theorem cell22_1904170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1904170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904170 prefixEnd_1904170 := by exact prefixLift 1904170
  have htrace : WordTrace (prefixWord ++ tailWord_1904170) baseStart_1904170 baseEnd_1904170 := by
    simpa [prefixWord, tailWord_1904170, baseEnd_1904170] using wordTrace_append hprefix tailTrace_1904170
  have hstable : (prefixWord ++ tailWord_1904170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904170).length < 2 ^ (prefixWord ++ tailWord_1904170).sum := by decide
  have hdescent : baseEnd_1904170 < baseStart_1904170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904174 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1904174 : Nat := 118140960795 + 1904174 * 2 ^ 59
def prefixEnd_1904174 : Nat := 4983230072969 + 3 ^ 40 * 1904174 * 2
def baseEnd_1904174 : Nat := 217279224843230698703971

theorem tailTrace_1904174 : CollatzResearch.WordTrace tailWord_1904174 prefixEnd_1904174 217279224843230698703971 := by
  unfold tailWord_1904174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681366425438784984156947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46300620935673519915503717 8681366425438784984156947)
  ·
    refine ⟨13022049638158177476235421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8681366425438784984156947 13022049638158177476235421)
    ·
      refine ⟨4883268614309316553588283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13022049638158177476235421 4883268614309316553588283)
      ·
        refine ⟨7324902921463974830382425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883268614309316553588283 7324902921463974830382425)
        ·
          refine ⟨5493677191097981122786819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324902921463974830382425 5493677191097981122786819)
          ·
            refine ⟨8240515786646971684180229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493677191097981122786819 8240515786646971684180229)
            ·
              refine ⟨1545096709996307190783793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8240515786646971684180229 1545096709996307190783793)
              ·
                refine ⟨1158822532497230393087845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545096709996307190783793 1158822532497230393087845)
                ·
                  refine ⟨217279224843230698703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158822532497230393087845 217279224843230698703971)
                  ·
                    rfl

theorem cell22_1904174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1904174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904174 prefixEnd_1904174 := by exact prefixLift 1904174
  have htrace : WordTrace (prefixWord ++ tailWord_1904174) baseStart_1904174 baseEnd_1904174 := by
    simpa [prefixWord, tailWord_1904174, baseEnd_1904174] using wordTrace_append hprefix tailTrace_1904174
  have hstable : (prefixWord ++ tailWord_1904174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904174).length < 2 ^ (prefixWord ++ tailWord_1904174).sum := by decide
  have hdescent : baseEnd_1904174 < baseStart_1904174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904185 : List Nat := [1, 2, 1, 5, 1, 4, 1, 7]
def baseStart_1904185 : Nat := 118140960795 + 1904185 * 2 ^ 59
def prefixEnd_1904185 : Nat := 4983230072969 + 3 ^ 40 * 1904185 * 2
def baseEnd_1904185 : Nat := 72426826672721303787431

theorem tailTrace_1904185 : CollatzResearch.WordTrace tailWord_1904185 prefixEnd_1904185 72426826672721303787431 := by
  unfold tailWord_1904185
  simp only [CollatzResearch.WordTrace]
  refine ⟨69451332606470428751906009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46300888404313619167937339 69451332606470428751906009)
  ·
    refine ⟨52088499454852821563929507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69451332606470428751906009 52088499454852821563929507)
    ·
      refine ⟨78132749182279232345894261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52088499454852821563929507 78132749182279232345894261)
      ·
        refine ⟨7324945235838678032427587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78132749182279232345894261 7324945235838678032427587)
        ·
          refine ⟨10987417853758017048641381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324945235838678032427587 10987417853758017048641381)
          ·
            refine ⟨2060140847579628196620259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10987417853758017048641381 2060140847579628196620259)
            ·
              refine ⟨3090211271369442294930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060140847579628196620259 3090211271369442294930389)
              ·
                refine ⟨72426826672721303787431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3090211271369442294930389 72426826672721303787431)
                ·
                  rfl

theorem cell22_1904185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 7].length) (baseStart_1904185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904185 prefixEnd_1904185 := by exact prefixLift 1904185
  have htrace : WordTrace (prefixWord ++ tailWord_1904185) baseStart_1904185 baseEnd_1904185 := by
    simpa [prefixWord, tailWord_1904185, baseEnd_1904185] using wordTrace_append hprefix tailTrace_1904185
  have hstable : (prefixWord ++ tailWord_1904185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904185).length < 2 ^ (prefixWord ++ tailWord_1904185).sum := by decide
  have hdescent : baseEnd_1904185 < baseStart_1904185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904213 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 7]
def baseStart_1904213 : Nat := 118140960795 + 1904213 * 2 ^ 59
def prefixEnd_1904213 : Nat := 4983230072969 + 3 ^ 40 * 1904213 * 2
def baseEnd_1904213 : Nat := 217283675008902998128931

theorem tailTrace_1904213 : CollatzResearch.WordTrace tailWord_1904213 prefixEnd_1904213 217283675008902998128931 := by
  unfold tailWord_1904213
  simp only [CollatzResearch.WordTrace]
  refine ⟨69452353850368989533925293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46301569233579326355950195 69452353850368989533925293)
  ·
    refine ⟨26044632693888371075221985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69452353850368989533925293 26044632693888371075221985)
    ·
      refine ⟨19533474520416278306416489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26044632693888371075221985 19533474520416278306416489)
      ·
        refine ⟨14650105890312208729812367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19533474520416278306416489 14650105890312208729812367)
        ·
          refine ⟨21975158835468313094718551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14650105890312208729812367 21975158835468313094718551)
          ·
            refine ⟨32962738253202469642077827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975158835468313094718551 32962738253202469642077827)
            ·
              refine ⟨49444107379803704463116741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32962738253202469642077827 49444107379803704463116741)
              ·
                refine ⟨9270770133713194586834389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49444107379803704463116741 9270770133713194586834389)
                ·
                  refine ⟨217283675008902998128931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9270770133713194586834389 217283675008902998128931)
                  ·
                    rfl

theorem cell22_1904213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_1904213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904213 prefixEnd_1904213 := by exact prefixLift 1904213
  have htrace : WordTrace (prefixWord ++ tailWord_1904213) baseStart_1904213 baseEnd_1904213 := by
    simpa [prefixWord, tailWord_1904213, baseEnd_1904213] using wordTrace_append hprefix tailTrace_1904213
  have hstable : (prefixWord ++ tailWord_1904213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904213).length < 2 ^ (prefixWord ++ tailWord_1904213).sum := by decide
  have hdescent : baseEnd_1904213 < baseStart_1904213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904234 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1904234 : Nat := 118140960795 + 1904234 * 2 ^ 59
def prefixEnd_1904234 : Nat := 4983230072969 + 3 ^ 40 * 1904234 * 2
def baseEnd_1904234 : Nat := 651858213755871939611729

theorem tailTrace_1904234 : CollatzResearch.WordTrace tailWord_1904234 prefixEnd_1904234 651858213755871939611729 := by
  unfold tailWord_1904234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17363279945823227530109939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46302079855528606746959837 17363279945823227530109939)
  ·
    refine ⟨26044919918734841295164909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17363279945823227530109939 26044919918734841295164909)
    ·
      refine ⟨9766844969525565485686841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26044919918734841295164909 9766844969525565485686841)
      ·
        refine ⟨7325133727144174114265131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9766844969525565485686841 7325133727144174114265131)
        ·
          refine ⟨10987700590716261171397697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325133727144174114265131 10987700590716261171397697)
          ·
            refine ⟨8240775443037195878548273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10987700590716261171397697 8240775443037195878548273)
            ·
              refine ⟨6180581582277896908911205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240775443037195878548273 6180581582277896908911205)
              ·
                refine ⟨1158859046677105670420851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6180581582277896908911205 1158859046677105670420851)
                ·
                  refine ⟨1738288570015658505631277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158859046677105670420851 1738288570015658505631277)
                  ·
                    refine ⟨651858213755871939611729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738288570015658505631277 651858213755871939611729)
                    ·
                      rfl

theorem cell22_1904234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1904234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904234 prefixEnd_1904234 := by exact prefixLift 1904234
  have htrace : WordTrace (prefixWord ++ tailWord_1904234) baseStart_1904234 baseEnd_1904234 := by
    simpa [prefixWord, tailWord_1904234, baseEnd_1904234] using wordTrace_append hprefix tailTrace_1904234
  have hstable : (prefixWord ++ tailWord_1904234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904234).length < 2 ^ (prefixWord ++ tailWord_1904234).sum := by decide
  have hdescent : baseEnd_1904234 < baseStart_1904234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904292 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1904292 : Nat := 118140960795 + 1904292 * 2 ^ 59
def prefixEnd_1904292 : Nat := 4983230072969 + 3 ^ 40 * 1904292 * 2
def baseEnd_1904292 : Nat := 217292689447059707220517

theorem tailTrace_1904292 : CollatzResearch.WordTrace tailWord_1904292 prefixEnd_1904292 217292689447059707220517 := by
  unfold tailWord_1904292
  simp only [CollatzResearch.WordTrace]
  refine ⟨34727617608541393013025565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46303490144721857350700753 34727617608541393013025565)
  ·
    refine ⟨13022856603203022379884587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34727617608541393013025565 13022856603203022379884587)
    ·
      refine ⟨19534284904804533569826881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13022856603203022379884587 19534284904804533569826881)
      ·
        refine ⟨14650713678603400177370161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19534284904804533569826881 14650713678603400177370161)
        ·
          refine ⟨10988035258952550133027621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14650713678603400177370161 10988035258952550133027621)
          ·
            refine ⟨2060256611053603149942679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10988035258952550133027621 2060256611053603149942679)
            ·
              refine ⟨3090384916580404724914019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060256611053603149942679 3090384916580404724914019)
              ·
                refine ⟨4635577374870607087371029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090384916580404724914019 4635577374870607087371029)
                ·
                  refine ⟨217292689447059707220517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4635577374870607087371029 217292689447059707220517)
                  ·
                    rfl

theorem cell22_1904292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1904292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904292 prefixEnd_1904292 := by exact prefixLift 1904292
  have htrace : WordTrace (prefixWord ++ tailWord_1904292) baseStart_1904292 baseEnd_1904292 := by
    simpa [prefixWord, tailWord_1904292, baseEnd_1904292] using wordTrace_append hprefix tailTrace_1904292
  have hstable : (prefixWord ++ tailWord_1904292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904292).length < 2 ^ (prefixWord ++ tailWord_1904292).sum := by decide
  have hdescent : baseEnd_1904292 < baseStart_1904292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904307 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 2, 3]
def baseStart_1904307 : Nat := 118140960795 + 1904307 * 2 ^ 59
def prefixEnd_1904307 : Nat := 4983230072969 + 3 ^ 40 * 1904307 * 2
def baseEnd_1904307 : Nat := 651883203147724082536505

theorem tailTrace_1904307 : CollatzResearch.WordTrace tailWord_1904307 prefixEnd_1904307 651883203147724082536505 := by
  unfold tailWord_1904307
  simp only [CollatzResearch.WordTrace]
  refine ⟨69455782312028443587847175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46303854874685629058564783 69455782312028443587847175)
  ·
    refine ⟨104183673468042665381770763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69455782312028443587847175 104183673468042665381770763)
    ·
      refine ⟨156275510202063998072656145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104183673468042665381770763 156275510202063998072656145)
      ·
        refine ⟨117206632651547998554492109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156275510202063998072656145 117206632651547998554492109)
        ·
          refine ⟨43952487244330499457934541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117206632651547998554492109 43952487244330499457934541)
          ·
            refine ⟨16482182716623937296725453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43952487244330499457934541 16482182716623937296725453)
            ·
              refine ⟨6180818518733976486272045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16482182716623937296725453 6180818518733976486272045)
              ·
                refine ⟨2317806944525241182352017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6180818518733976486272045 2317806944525241182352017)
                ·
                  refine ⟨1738355208393930886764013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317806944525241182352017 1738355208393930886764013)
                  ·
                    refine ⟨651883203147724082536505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738355208393930886764013 651883203147724082536505)
                    ·
                      rfl

theorem cell22_1904307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 3].length) (baseStart_1904307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904307 prefixEnd_1904307 := by exact prefixLift 1904307
  have htrace : WordTrace (prefixWord ++ tailWord_1904307) baseStart_1904307 baseEnd_1904307 := by
    simpa [prefixWord, tailWord_1904307, baseEnd_1904307] using wordTrace_append hprefix tailTrace_1904307
  have hstable : (prefixWord ++ tailWord_1904307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904307).length < 2 ^ (prefixWord ++ tailWord_1904307).sum := by decide
  have hdescent : baseEnd_1904307 < baseStart_1904307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904380 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1904380 : Nat := 118140960795 + 1904380 * 2 ^ 59
def prefixEnd_1904380 : Nat := 4983230072969 + 3 ^ 40 * 1904380 * 2
def baseEnd_1904380 : Nat := 651908192539576225461281

theorem tailTrace_1904380 : CollatzResearch.WordTrace tailWord_1904380 prefixEnd_1904380 651908192539576225461281 := by
  unfold tailWord_1904380
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729222420381988527627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46305629893842651370169729 34729222420381988527627297)
  ·
    refine ⟨26046916815286491395720473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34729222420381988527627297 26046916815286491395720473)
    ·
      refine ⟨19535187611464868546790355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26046916815286491395720473 19535187611464868546790355)
      ·
        refine ⟨29302781417197302820185533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535187611464868546790355 29302781417197302820185533)
        ·
          refine ⟨10988543031448988557569575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29302781417197302820185533 10988543031448988557569575)
          ·
            refine ⟨16482814547173482836354363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988543031448988557569575 16482814547173482836354363)
            ·
              refine ⟨24724221820760224254531545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16482814547173482836354363 24724221820760224254531545)
              ·
                refine ⟨18543166365570168190898659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24724221820760224254531545 18543166365570168190898659)
                ·
                  refine ⟨27814749548355252286347989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18543166365570168190898659 27814749548355252286347989)
                  ·
                    refine ⟨651908192539576225461281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27814749548355252286347989 651908192539576225461281)
                    ·
                      rfl

theorem cell22_1904380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1904380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904380 prefixEnd_1904380 := by exact prefixLift 1904380
  have htrace : WordTrace (prefixWord ++ tailWord_1904380) baseStart_1904380 baseEnd_1904380 := by
    simpa [prefixWord, tailWord_1904380, baseEnd_1904380] using wordTrace_append hprefix tailTrace_1904380
  have hstable : (prefixWord ++ tailWord_1904380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904380).length < 2 ^ (prefixWord ++ tailWord_1904380).sum := by decide
  have hdescent : baseEnd_1904380 < baseStart_1904380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904444 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1904444 : Nat := 118140960795 + 1904444 * 2 ^ 59
def prefixEnd_1904444 : Nat := 4983230072969 + 3 ^ 40 * 1904444 * 2
def baseEnd_1904444 : Nat := 217310033682500463953695

theorem tailTrace_1904444 : CollatzResearch.WordTrace tailWord_1904444 prefixEnd_1904444 217310033682500463953695 := by
  unfold tailWord_1904444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34730389556266057992792193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46307186075021410657056257 34730389556266057992792193)
  ·
    refine ⟨26047792167199543494594145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34730389556266057992792193 26047792167199543494594145)
    ·
      refine ⟨19535844125399657620945609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26047792167199543494594145 19535844125399657620945609)
      ·
        refine ⟨14651883094049743215709207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19535844125399657620945609 14651883094049743215709207)
        ·
          refine ⟨21977824641074614823563811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14651883094049743215709207 21977824641074614823563811)
          ·
            refine ⟨32966736961611922235345717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21977824641074614823563811 32966736961611922235345717)
            ·
              refine ⟨3090631590151117709563661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32966736961611922235345717 3090631590151117709563661)
              ·
                refine ⟨1158986846306669141086373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3090631590151117709563661 1158986846306669141086373)
                ·
                  refine ⟨217310033682500463953695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158986846306669141086373 217310033682500463953695)
                  ·
                    rfl

theorem cell22_1904444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1904444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904444 prefixEnd_1904444 := by exact prefixLift 1904444
  have htrace : WordTrace (prefixWord ++ tailWord_1904444) baseStart_1904444 baseEnd_1904444 := by
    simpa [prefixWord, tailWord_1904444, baseEnd_1904444] using wordTrace_append hprefix tailTrace_1904444
  have hstable : (prefixWord ++ tailWord_1904444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904444).length < 2 ^ (prefixWord ++ tailWord_1904444).sum := by decide
  have hdescent : baseEnd_1904444 < baseStart_1904444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904455 : List Nat := [1, 1, 4, 1, 2, 1, 12]
def baseStart_1904455 : Nat := 118140960795 + 1904455 * 2 ^ 59
def prefixEnd_1904455 : Nat := 4983230072969 + 3 ^ 40 * 1904455 * 2
def baseEnd_1904455 : Nat := 24145698761937075179113

theorem tailTrace_1904455 : CollatzResearch.WordTrace tailWord_1904455 prefixEnd_1904455 24145698761937075179113 := by
  unfold tailWord_1904455
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461180315492264864234819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46307453543661509909489879 69461180315492264864234819)
  ·
    refine ⟨104191770473238397296352229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69461180315492264864234819 104191770473238397296352229)
    ·
      refine ⟨19535956963732199493066043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104191770473238397296352229 19535956963732199493066043)
      ·
        refine ⟨29303935445598299239599065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535956963732199493066043 29303935445598299239599065)
        ·
          refine ⟨21977951584198724429699299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29303935445598299239599065 21977951584198724429699299)
          ·
            refine ⟨32966927376298086644548949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21977951584198724429699299 32966927376298086644548949)
            ·
              refine ⟨24145698761937075179113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 32966927376298086644548949 24145698761937075179113)
              ·
                rfl

theorem cell22_1904455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 12].length) (baseStart_1904455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904455 prefixEnd_1904455 := by exact prefixLift 1904455
  have htrace : WordTrace (prefixWord ++ tailWord_1904455) baseStart_1904455 baseEnd_1904455 := by
    simpa [prefixWord, tailWord_1904455, baseEnd_1904455] using wordTrace_append hprefix tailTrace_1904455
  have hstable : (prefixWord ++ tailWord_1904455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904455).length < 2 ^ (prefixWord ++ tailWord_1904455).sum := by decide
  have hdescent : baseEnd_1904455 < baseStart_1904455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904457 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_1904457 : Nat := 118140960795 + 1904457 * 2 ^ 59
def prefixEnd_1904457 : Nat := 4983230072969 + 3 ^ 40 * 1904457 * 2
def baseEnd_1904457 : Nat := 651934551213173691286045

theorem tailTrace_1904457 : CollatzResearch.WordTrace tailWord_1904457 prefixEnd_1904457 651934551213173691286045 := by
  unfold tailWord_1904457
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461253261485019205807625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46307502174323346137205083 69461253261485019205807625)
  ·
    refine ⟨52095939946113764404355719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69461253261485019205807625 52095939946113764404355719)
    ·
      refine ⟨78143909919170646606533579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52095939946113764404355719 78143909919170646606533579)
      ·
        refine ⟨117215864878755969909800369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78143909919170646606533579 117215864878755969909800369)
        ·
          refine ⟨87911898659066977432350277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117215864878755969909800369 87911898659066977432350277)
          ·
            refine ⟨16483480998575058268565677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87911898659066977432350277 16483480998575058268565677)
            ·
              refine ⟨6181305374465646850712129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16483480998575058268565677 6181305374465646850712129)
              ·
                refine ⟨4635979030849235138034097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181305374465646850712129 4635979030849235138034097)
                ·
                  refine ⟨3476984273136926353525573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635979030849235138034097 3476984273136926353525573)
                  ·
                    refine ⟨651934551213173691286045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476984273136926353525573 651934551213173691286045)
                    ·
                      rfl

theorem cell22_1904457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_1904457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904457 prefixEnd_1904457 := by exact prefixLift 1904457
  have htrace : WordTrace (prefixWord ++ tailWord_1904457) baseStart_1904457 baseEnd_1904457 := by
    simpa [prefixWord, tailWord_1904457, baseEnd_1904457] using wordTrace_append hprefix tailTrace_1904457
  have hstable : (prefixWord ++ tailWord_1904457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904457).length < 2 ^ (prefixWord ++ tailWord_1904457).sum := by decide
  have hdescent : baseEnd_1904457 < baseStart_1904457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904461 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1904461 : Nat := 118140960795 + 1904461 * 2 ^ 59
def prefixEnd_1904461 : Nat := 4983230072969 + 3 ^ 40 * 1904461 * 2
def baseEnd_1904461 : Nat := 217311973498306338062011

theorem tailTrace_1904461 : CollatzResearch.WordTrace tailWord_1904461 prefixEnd_1904461 217311973498306338062011 := by
  unfold tailWord_1904461
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461399153470527888953237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46307599435647018592635491 69461399153470527888953237)
  ·
    refine ⟨3256003085318930994794683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69461399153470527888953237 3256003085318930994794683)
    ·
      refine ⟨4884004627978396492192025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256003085318930994794683 4884004627978396492192025)
      ·
        refine ⟨3663003470983797369144019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4884004627978396492192025 3663003470983797369144019)
        ·
          refine ⟨5494505206475696053716029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663003470983797369144019 5494505206475696053716029)
          ·
            refine ⟨2060439452428386020143511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5494505206475696053716029 2060439452428386020143511)
            ·
              refine ⟨3090659178642579030215267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060439452428386020143511 3090659178642579030215267)
              ·
                refine ⟨4635988767963868545322901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090659178642579030215267 4635988767963868545322901)
                ·
                  refine ⟨217311973498306338062011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4635988767963868545322901 217311973498306338062011)
                  ·
                    rfl

theorem cell22_1904461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1904461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904461 prefixEnd_1904461 := by exact prefixLift 1904461
  have htrace : WordTrace (prefixWord ++ tailWord_1904461) baseStart_1904461 baseEnd_1904461 := by
    simpa [prefixWord, tailWord_1904461, baseEnd_1904461] using wordTrace_append hprefix tailTrace_1904461
  have hstable : (prefixWord ++ tailWord_1904461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904461).length < 2 ^ (prefixWord ++ tailWord_1904461).sum := by decide
  have hdescent : baseEnd_1904461 < baseStart_1904461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904521 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_1904521 : Nat := 118140960795 + 1904521 * 2 ^ 59
def prefixEnd_1904521 : Nat := 4983230072969 + 3 ^ 40 * 1904521 * 2
def baseEnd_1904521 : Nat := 651956459721098857685849

theorem tailTrace_1904521 : CollatzResearch.WordTrace tailWord_1904521 prefixEnd_1904521 651956459721098857685849 := by
  unfold tailWord_1904521
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463587533253158136137417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46309058355502105424091611 69463587533253158136137417)
  ·
    refine ⟨52097690649939868602103063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69463587533253158136137417 52097690649939868602103063)
    ·
      refine ⟨78146535974909802903154595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52097690649939868602103063 78146535974909802903154595)
      ·
        refine ⟨117219803962364704354731893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78146535974909802903154595 117219803962364704354731893)
        ·
          refine ⟨10989356621471691033256115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117219803962364704354731893 10989356621471691033256115)
          ·
            refine ⟨16484034932207536549884173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989356621471691033256115 16484034932207536549884173)
            ·
              refine ⟨6181513099577826206206565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16484034932207536549884173 6181513099577826206206565)
              ·
                refine ⟨1159033706170842413663731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6181513099577826206206565 1159033706170842413663731)
                ·
                  refine ⟨1738550559256263620495597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159033706170842413663731 1738550559256263620495597)
                  ·
                    refine ⟨651956459721098857685849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738550559256263620495597 651956459721098857685849)
                    ·
                      rfl

theorem cell22_1904521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_1904521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904521 prefixEnd_1904521 := by exact prefixLift 1904521
  have htrace : WordTrace (prefixWord ++ tailWord_1904521) baseStart_1904521 baseEnd_1904521 := by
    simpa [prefixWord, tailWord_1904521, baseEnd_1904521] using wordTrace_append hprefix tailTrace_1904521
  have hstable : (prefixWord ++ tailWord_1904521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904521).length < 2 ^ (prefixWord ++ tailWord_1904521).sum := by decide
  have hdescent : baseEnd_1904521 < baseStart_1904521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904592 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_1904592 : Nat := 118140960795 + 1904592 * 2 ^ 59
def prefixEnd_1904592 : Nat := 4983230072969 + 3 ^ 40 * 1904592 * 2
def baseEnd_1904592 : Nat := 651980764472078339160631

theorem tailTrace_1904592 : CollatzResearch.WordTrace tailWord_1904592 prefixEnd_1904592 651980764472078339160631 := by
  unfold tailWord_1904592
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733088557997968630986015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46310784743997291507981353 34733088557997968630986015)
  ·
    refine ⟨52099632836996952946479023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733088557997968630986015 52099632836996952946479023)
    ·
      refine ⟨78149449255495429419718535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52099632836996952946479023 78149449255495429419718535)
      ·
        refine ⟨117224173883243144129577803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78149449255495429419718535 117224173883243144129577803)
        ·
          refine ⟨175836260824864716194366705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117224173883243144129577803 175836260824864716194366705)
          ·
            refine ⟨131877195618648537145775029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175836260824864716194366705 131877195618648537145775029)
            ·
              refine ⟨12363487089248300357416409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131877195618648537145775029 12363487089248300357416409)
              ·
                refine ⟨9272615316936225268062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363487089248300357416409 9272615316936225268062307)
                ·
                  refine ⟨13908922975404337902093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272615316936225268062307 13908922975404337902093461)
                  ·
                    refine ⟨651980764472078339160631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13908922975404337902093461 651980764472078339160631)
                    ·
                      rfl

theorem cell22_1904592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_1904592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904592 prefixEnd_1904592 := by exact prefixLift 1904592
  have htrace : WordTrace (prefixWord ++ tailWord_1904592) baseStart_1904592 baseEnd_1904592 := by
    simpa [prefixWord, tailWord_1904592, baseEnd_1904592] using wordTrace_append hprefix tailTrace_1904592
  have hstable : (prefixWord ++ tailWord_1904592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904592).length < 2 ^ (prefixWord ++ tailWord_1904592).sum := by decide
  have hdescent : baseEnd_1904592 < baseStart_1904592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904630 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1904630 : Nat := 118140960795 + 1904630 * 2 ^ 59
def prefixEnd_1904630 : Nat := 4983230072969 + 3 ^ 40 * 1904630 * 2
def baseEnd_1904630 : Nat := 217331257549552968903505

theorem tailTrace_1904630 : CollatzResearch.WordTrace tailWord_1904630 prefixEnd_1904630 217331257549552968903505 := by
  unfold tailWord_1904630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341722693116141859490959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46311708726572179834570229 4341722693116141859490959)
  ·
    refine ⟨6512584039674212789236439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341722693116141859490959 6512584039674212789236439)
    ·
      refine ⟨9768876059511319183854659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512584039674212789236439 9768876059511319183854659)
      ·
        refine ⟨14653314089266978775781989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768876059511319183854659 14653314089266978775781989)
        ·
          refine ⟨2747496391737558520459123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14653314089266978775781989 2747496391737558520459123)
          ·
            refine ⟨4121244587606337780688685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747496391737558520459123 4121244587606337780688685)
            ·
              refine ⟨1545466720352376667758257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121244587606337780688685 1545466720352376667758257)
              ·
                refine ⟨1159100040264282500818693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545466720352376667758257 1159100040264282500818693)
                ·
                  refine ⟨217331257549552968903505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159100040264282500818693 217331257549552968903505)
                  ·
                    rfl

theorem cell22_1904630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1904630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904630 prefixEnd_1904630 := by exact prefixLift 1904630
  have htrace : WordTrace (prefixWord ++ tailWord_1904630) baseStart_1904630 baseEnd_1904630 := by
    simpa [prefixWord, tailWord_1904630, baseEnd_1904630] using wordTrace_append hprefix tailTrace_1904630
  have hstable : (prefixWord ++ tailWord_1904630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904630).length < 2 ^ (prefixWord ++ tailWord_1904630).sum := by decide
  have hdescent : baseEnd_1904630 < baseStart_1904630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904660 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1904660 : Nat := 118140960795 + 1904660 * 2 ^ 59
def prefixEnd_1904660 : Nat := 4983230072969 + 3 ^ 40 * 1904660 * 2
def baseEnd_1904660 : Nat := 652004042261748828460423

theorem tailTrace_1904660 : CollatzResearch.WordTrace tailWord_1904660 prefixEnd_1904660 652004042261748828460423 := by
  unfold tailWord_1904660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34734328639874792437723717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46312438186499723250298289 34734328639874792437723717)
  ·
    refine ⟨6512686619976523582073197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34734328639874792437723717 6512686619976523582073197)
    ·
      refine ⟨2442257482491196343277449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6512686619976523582073197 2442257482491196343277449)
      ·
        refine ⟨1831693111868397257458087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442257482491196343277449 1831693111868397257458087)
        ·
          refine ⟨2747539667802595886187131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831693111868397257458087 2747539667802595886187131)
          ·
            refine ⟨4121309501703893829280697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747539667802595886187131 4121309501703893829280697)
            ·
              refine ⟨3090982126277920371960523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121309501703893829280697 3090982126277920371960523)
              ·
                refine ⟨4636473189416880557940785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090982126277920371960523 4636473189416880557940785)
                ·
                  refine ⟨3477354892062660418455589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636473189416880557940785 3477354892062660418455589)
                  ·
                    refine ⟨652004042261748828460423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477354892062660418455589 652004042261748828460423)
                    ·
                      rfl

theorem cell22_1904660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1904660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904660 prefixEnd_1904660 := by exact prefixLift 1904660
  have htrace : WordTrace (prefixWord ++ tailWord_1904660) baseStart_1904660 baseEnd_1904660 := by
    simpa [prefixWord, tailWord_1904660, baseEnd_1904660] using wordTrace_append hprefix tailTrace_1904660
  have hstable : (prefixWord ++ tailWord_1904660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904660).length < 2 ^ (prefixWord ++ tailWord_1904660).sum := by decide
  have hdescent : baseEnd_1904660 < baseStart_1904660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_1904667 : Nat := 118140960795 + 1904667 * 2 ^ 59
def prefixEnd_1904667 : Nat := 4983230072969 + 3 ^ 40 * 1904667 * 2
def baseEnd_1904667 : Nat := 652006438504803143535401

theorem tailTrace_1904667 : CollatzResearch.WordTrace tailWord_1904667 prefixEnd_1904667 652006438504803143535401 := by
  unfold tailWord_1904667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69468912590724225070952255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46312608393816150047301503 69468912590724225070952255)
  ·
    refine ⟨104203368886086337606428383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69468912590724225070952255 104203368886086337606428383)
    ·
      refine ⟨156305053329129506409642575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104203368886086337606428383 156305053329129506409642575)
      ·
        refine ⟨234457579993694259614463863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156305053329129506409642575 234457579993694259614463863)
        ·
          refine ⟨351686369990541389421695795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234457579993694259614463863 351686369990541389421695795)
          ·
            refine ⟨527529554985812084132543693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351686369990541389421695795 527529554985812084132543693)
            ·
              refine ⟨197823583119679531549703885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527529554985812084132543693 197823583119679531549703885)
              ·
                refine ⟨74183843669879824331138957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197823583119679531549703885 74183843669879824331138957)
                ·
                  refine ⟨27818941376204934124177109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74183843669879824331138957 27818941376204934124177109)
                  ·
                    refine ⟨652006438504803143535401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27818941376204934124177109 652006438504803143535401)
                    ·
                      rfl

theorem cell22_1904667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_1904667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904667 prefixEnd_1904667 := by exact prefixLift 1904667
  have htrace : WordTrace (prefixWord ++ tailWord_1904667) baseStart_1904667 baseEnd_1904667 := by
    simpa [prefixWord, tailWord_1904667, baseEnd_1904667] using wordTrace_append hprefix tailTrace_1904667
  have hstable : (prefixWord ++ tailWord_1904667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904667).length < 2 ^ (prefixWord ++ tailWord_1904667).sum := by decide
  have hdescent : baseEnd_1904667 < baseStart_1904667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904686 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1904686 : Nat := 118140960795 + 1904686 * 2 ^ 59
def prefixEnd_1904686 : Nat := 4983230072969 + 3 ^ 40 * 1904686 * 2
def baseEnd_1904686 : Nat := 217337647531031142436781

theorem tailTrace_1904686 : CollatzResearch.WordTrace tailWord_1904686 prefixEnd_1904686 217337647531031142436781 := by
  unfold tailWord_1904686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683700697206923914486739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46313070385103594210595941 8683700697206923914486739)
  ·
    refine ⟨13025551045810385871730109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8683700697206923914486739 13025551045810385871730109)
    ·
      refine ⟨4884581642178894701898791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13025551045810385871730109 4884581642178894701898791)
      ·
        refine ⟨7326872463268342052848187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884581642178894701898791 7326872463268342052848187)
        ·
          refine ⟨10990308694902513079272281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326872463268342052848187 10990308694902513079272281)
          ·
            refine ⟨8242731521176884809454211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10990308694902513079272281 8242731521176884809454211)
            ·
              refine ⟨12364097281765327214181317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242731521176884809454211 12364097281765327214181317)
              ·
                refine ⟨2318268240330998852658997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12364097281765327214181317 2318268240330998852658997)
                ·
                  refine ⟨217337647531031142436781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318268240330998852658997 217337647531031142436781)
                  ·
                    rfl

theorem cell22_1904686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1904686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904686 prefixEnd_1904686 := by exact prefixLift 1904686
  have htrace : WordTrace (prefixWord ++ tailWord_1904686) baseStart_1904686 baseEnd_1904686 := by
    simpa [prefixWord, tailWord_1904686, baseEnd_1904686] using wordTrace_append hprefix tailTrace_1904686
  have hstable : (prefixWord ++ tailWord_1904686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904686).length < 2 ^ (prefixWord ++ tailWord_1904686).sum := by decide
  have hdescent : baseEnd_1904686 < baseStart_1904686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904690 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1904690 : Nat := 118140960795 + 1904690 * 2 ^ 59
def prefixEnd_1904690 : Nat := 4983230072969 + 3 ^ 40 * 1904690 * 2
def baseEnd_1904690 : Nat := 652014311874838750210331

theorem tailTrace_1904690 : CollatzResearch.WordTrace tailWord_1904690 prefixEnd_1904690 652014311874838750210331 := by
  unfold tailWord_1904690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367437867410224999759881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46313167646427266666026349 17367437867410224999759881)
  ·
    refine ⟨13025578400557668749819911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17367437867410224999759881 13025578400557668749819911)
    ·
      refine ⟨19538367600836503124729867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025578400557668749819911 19538367600836503124729867)
      ·
        refine ⟨29307551401254754687094801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19538367600836503124729867 29307551401254754687094801)
        ·
          refine ⟨21980663550941066015321101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29307551401254754687094801 21980663550941066015321101)
          ·
            refine ⟨8242748831602899755745413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21980663550941066015321101 8242748831602899755745413)
            ·
              refine ⟨1545515405925543704202265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8242748831602899755745413 1545515405925543704202265)
              ·
                refine ⟨1159136554444157778151699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545515405925543704202265 1159136554444157778151699)
                ·
                  refine ⟨1738704831666236667227549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159136554444157778151699 1738704831666236667227549)
                  ·
                    refine ⟨652014311874838750210331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738704831666236667227549 652014311874838750210331)
                    ·
                      rfl

theorem cell22_1904690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1904690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904690 prefixEnd_1904690 := by exact prefixLift 1904690
  have htrace : WordTrace (prefixWord ++ tailWord_1904690) baseStart_1904690 baseEnd_1904690 := by
    simpa [prefixWord, tailWord_1904690, baseEnd_1904690] using wordTrace_append hprefix tailTrace_1904690
  have hstable : (prefixWord ++ tailWord_1904690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904690).length < 2 ^ (prefixWord ++ tailWord_1904690).sum := by decide
  have hdescent : baseEnd_1904690 < baseStart_1904690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904729 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_1904729 : Nat := 118140960795 + 1904729 * 2 ^ 59
def prefixEnd_1904729 : Nat := 4983230072969 + 3 ^ 40 * 1904729 * 2
def baseEnd_1904729 : Nat := 652027662371855648485211

theorem tailTrace_1904729 : CollatzResearch.WordTrace tailWord_1904729 prefixEnd_1904729 652027662371855648485211 := by
  unfold tailWord_1904729
  simp only [CollatzResearch.WordTrace]
  refine ⟨69471173916499609659709241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46314115944333073106472827 69471173916499609659709241)
  ·
    refine ⟨52103380437374707244781931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69471173916499609659709241 52103380437374707244781931)
    ·
      refine ⟨78155070656062060867172897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52103380437374707244781931 78155070656062060867172897)
      ·
        refine ⟨58616302992046545650379673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78155070656062060867172897 58616302992046545650379673)
        ·
          refine ⟨43962227244034909237784755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58616302992046545650379673 43962227244034909237784755)
          ·
            refine ⟨65943340866052363856677133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43962227244034909237784755 65943340866052363856677133)
            ·
              refine ⟨24728752824769636446253925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65943340866052363856677133 24728752824769636446253925)
              ·
                refine ⟨4636641154644306833672611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24728752824769636446253925 4636641154644306833672611)
                ·
                  refine ⟨6954961731966460250508917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636641154644306833672611 6954961731966460250508917)
                  ·
                    refine ⟨652027662371855648485211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6954961731966460250508917 652027662371855648485211)
                    ·
                      rfl

theorem cell22_1904729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_1904729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904729 prefixEnd_1904729 := by exact prefixLift 1904729
  have htrace : WordTrace (prefixWord ++ tailWord_1904729) baseStart_1904729 baseEnd_1904729 := by
    simpa [prefixWord, tailWord_1904729, baseEnd_1904729] using wordTrace_append hprefix tailTrace_1904729
  have hstable : (prefixWord ++ tailWord_1904729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904729).length < 2 ^ (prefixWord ++ tailWord_1904729).sum := by decide
  have hdescent : baseEnd_1904729 < baseStart_1904729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904776 : List Nat := [2, 1, 3, 4, 1, 2, 1, 8]
def baseStart_1904776 : Nat := 118140960795 + 1904776 * 2 ^ 59
def prefixEnd_1904776 : Nat := 4983230072969 + 3 ^ 40 * 1904776 * 2
def baseEnd_1904776 : Nat := 72449305714707021395563

theorem tailTrace_1904776 : CollatzResearch.WordTrace tailWord_1904776 prefixEnd_1904776 72449305714707021395563 := by
  unfold tailWord_1904776
  simp only [CollatzResearch.WordTrace]
  refine ⟨34736444073664668343335091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46315258764886224457780121 34736444073664668343335091)
  ·
    refine ⟨52104666110497002515002637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34736444073664668343335091 52104666110497002515002637)
    ·
      refine ⟨19539249791436375943125989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52104666110497002515002637 19539249791436375943125989)
      ·
        refine ⟨3663609335894320489336123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19539249791436375943125989 3663609335894320489336123)
        ·
          refine ⟨5495414003841480734004185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663609335894320489336123 5495414003841480734004185)
          ·
            refine ⟨4121560502881110550503139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495414003841480734004185 4121560502881110550503139)
            ·
              refine ⟨6182340754321665825754709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121560502881110550503139 6182340754321665825754709)
              ·
                refine ⟨72449305714707021395563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6182340754321665825754709 72449305714707021395563)
                ·
                  rfl

theorem cell22_1904776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_1904776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904776 prefixEnd_1904776 := by exact prefixLift 1904776
  have htrace : WordTrace (prefixWord ++ tailWord_1904776) baseStart_1904776 baseEnd_1904776 := by
    simpa [prefixWord, tailWord_1904776, baseEnd_1904776] using wordTrace_append hprefix tailTrace_1904776
  have hstable : (prefixWord ++ tailWord_1904776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904776).length < 2 ^ (prefixWord ++ tailWord_1904776).sum := by decide
  have hdescent : baseEnd_1904776 < baseStart_1904776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904782 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1904782 : Nat := 118140960795 + 1904782 * 2 ^ 59
def prefixEnd_1904782 : Nat := 4983230072969 + 3 ^ 40 * 1904782 * 2
def baseEnd_1904782 : Nat := 217348601784993725636683

theorem tailTrace_1904782 : CollatzResearch.WordTrace tailWord_1904782 prefixEnd_1904782 217348601784993725636683 := by
  unfold tailWord_1904782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684138373163449963923575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46315404656871733140925733 8684138373163449963923575)
  ·
    refine ⟨13026207559745174945885363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8684138373163449963923575 13026207559745174945885363)
    ·
      refine ⟨19539311339617762418828045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026207559745174945885363 19539311339617762418828045)
      ·
        refine ⟨7327241752356660907060517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19539311339617762418828045 7327241752356660907060517)
        ·
          refine ⟨1373857828566873920073847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7327241752356660907060517 1373857828566873920073847)
          ·
            refine ⟨2060786742850310880110771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373857828566873920073847 2060786742850310880110771)
            ·
              refine ⟨3091180114275466320166157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060786742850310880110771 3091180114275466320166157)
              ·
                refine ⟨1159192542853299870062309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3091180114275466320166157 1159192542853299870062309)
                ·
                  refine ⟨217348601784993725636683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159192542853299870062309 217348601784993725636683)
                  ·
                    rfl

theorem cell22_1904782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1904782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904782 prefixEnd_1904782 := by exact prefixLift 1904782
  have htrace : WordTrace (prefixWord ++ tailWord_1904782) baseStart_1904782 baseEnd_1904782 := by
    simpa [prefixWord, tailWord_1904782, baseEnd_1904782] using wordTrace_append hprefix tailTrace_1904782
  have hstable : (prefixWord ++ tailWord_1904782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904782).length < 2 ^ (prefixWord ++ tailWord_1904782).sum := by decide
  have hdescent : baseEnd_1904782 < baseStart_1904782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904819 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_1904819 : Nat := 118140960795 + 1904819 * 2 ^ 59
def prefixEnd_1904819 : Nat := 4983230072969 + 3 ^ 40 * 1904819 * 2
def baseEnd_1904819 : Nat := 652058471211125413734935

theorem tailTrace_1904819 : CollatzResearch.WordTrace tailWord_1904819 prefixEnd_1904819 652058471211125413734935 := by
  unfold tailWord_1904819
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474456486173555030485511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46316304324115703353657007 69474456486173555030485511)
  ·
    refine ⟨104211684729260332545728267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69474456486173555030485511 104211684729260332545728267)
    ·
      refine ⟨156317527093890498818592401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104211684729260332545728267 156317527093890498818592401)
      ·
        refine ⟨117238145320417874113944301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156317527093890498818592401 117238145320417874113944301)
        ·
          refine ⟨43964304495156702792729113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117238145320417874113944301 43964304495156702792729113)
          ·
            refine ⟨32973228371367527094546835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43964304495156702792729113 32973228371367527094546835)
            ·
              refine ⟨49459842557051290641820253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32973228371367527094546835 49459842557051290641820253)
              ·
                refine ⟨18547440958894233990682595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49459842557051290641820253 18547440958894233990682595)
                ·
                  refine ⟨27821161438341350986023893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18547440958894233990682595 27821161438341350986023893)
                  ·
                    refine ⟨652058471211125413734935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27821161438341350986023893 652058471211125413734935)
                    ·
                      rfl

theorem cell22_1904819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_1904819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904819 prefixEnd_1904819 := by exact prefixLift 1904819
  have htrace : WordTrace (prefixWord ++ tailWord_1904819) baseStart_1904819 baseEnd_1904819 := by
    simpa [prefixWord, tailWord_1904819, baseEnd_1904819] using wordTrace_append hprefix tailTrace_1904819
  have hstable : (prefixWord ++ tailWord_1904819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904819).length < 2 ^ (prefixWord ++ tailWord_1904819).sum := by decide
  have hdescent : baseEnd_1904819 < baseStart_1904819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904881 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1904881 : Nat := 118140960795 + 1904881 * 2 ^ 59
def prefixEnd_1904881 : Nat := 4983230072969 + 3 ^ 40 * 1904881 * 2
def baseEnd_1904881 : Nat := 652079695078177918684745

theorem tailTrace_1904881 : CollatzResearch.WordTrace tailWord_1904881 prefixEnd_1904881 652079695078177918684745 := by
  unfold tailWord_1904881
  simp only [CollatzResearch.WordTrace]
  refine ⟨69476717811948939619242497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46317811874632626412828331 69476717811948939619242497)
  ·
    refine ⟨52107538358961704714431873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69476717811948939619242497 52107538358961704714431873)
    ·
      refine ⟨39080653769221278535823905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52107538358961704714431873 39080653769221278535823905)
      ·
        refine ⟨29310490326915958901867929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39080653769221278535823905 29310490326915958901867929)
        ·
          refine ⟨21982867745186969176400947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29310490326915958901867929 21982867745186969176400947)
          ·
            refine ⟨32974301617780453764601421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982867745186969176400947 32974301617780453764601421)
            ·
              refine ⟨12365363106667670161725533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32974301617780453764601421 12365363106667670161725533)
              ·
                refine ⟨4637011165000376310647075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12365363106667670161725533 4637011165000376310647075)
                ·
                  refine ⟨6955516747500564465970613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637011165000376310647075 6955516747500564465970613)
                  ·
                    refine ⟨652079695078177918684745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6955516747500564465970613 652079695078177918684745)
                    ·
                      rfl

theorem cell22_1904881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1904881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904881 prefixEnd_1904881 := by exact prefixLift 1904881
  have htrace : WordTrace (prefixWord ++ tailWord_1904881) baseStart_1904881 baseEnd_1904881 := by
    simpa [prefixWord, tailWord_1904881, baseEnd_1904881] using wordTrace_append hprefix tailTrace_1904881
  have hstable : (prefixWord ++ tailWord_1904881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904881).length < 2 ^ (prefixWord ++ tailWord_1904881).sum := by decide
  have hdescent : baseEnd_1904881 < baseStart_1904881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904932 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_1904932 : Nat := 118140960795 + 1904932 * 2 ^ 59
def prefixEnd_1904932 : Nat := 4983230072969 + 3 ^ 40 * 1904932 * 2
def baseEnd_1904932 : Nat := 652097153420430785659589

theorem tailTrace_1904932 : CollatzResearch.WordTrace tailWord_1904932 prefixEnd_1904932 652097153420430785659589 := by
  unfold tailWord_1904932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739288967382087664674525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46319051956509450219566033 34739288967382087664674525)
  ·
    refine ⟨13027233362768282874252947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34739288967382087664674525 13027233362768282874252947)
    ·
      refine ⟨19540850044152424311379421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13027233362768282874252947 19540850044152424311379421)
      ·
        refine ⟨7327818766557159116767283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19540850044152424311379421 7327818766557159116767283)
        ·
          refine ⟨10991728149835738675150925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7327818766557159116767283 10991728149835738675150925)
          ·
            refine ⟨4121898056188402003181597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10991728149835738675150925 4121898056188402003181597)
            ·
              refine ⟨1545711771070650751193099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121898056188402003181597 1545711771070650751193099)
              ·
                refine ⟨2318567656605976126789649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545711771070650751193099 2318567656605976126789649)
                ·
                  refine ⟨1738925742454482095092237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2318567656605976126789649 1738925742454482095092237)
                  ·
                    refine ⟨652097153420430785659589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738925742454482095092237 652097153420430785659589)
                    ·
                      rfl

theorem cell22_1904932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_1904932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904932 prefixEnd_1904932 := by exact prefixLift 1904932
  have htrace : WordTrace (prefixWord ++ tailWord_1904932) baseStart_1904932 baseEnd_1904932 := by
    simpa [prefixWord, tailWord_1904932, baseEnd_1904932] using wordTrace_append hprefix tailTrace_1904932
  have hstable : (prefixWord ++ tailWord_1904932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904932).length < 2 ^ (prefixWord ++ tailWord_1904932).sum := by decide
  have hdescent : baseEnd_1904932 < baseStart_1904932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904943 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 3, 3]
def baseStart_1904943 : Nat := 118140960795 + 1904943 * 2 ^ 59
def prefixEnd_1904943 : Nat := 4983230072969 + 3 ^ 40 * 1904943 * 2
def baseEnd_1904943 : Nat := 652100918945230423634555

theorem tailTrace_1904943 : CollatzResearch.WordTrace tailWord_1904943 prefixEnd_1904943 652100918945230423634555 := by
  unfold tailWord_1904943
  simp only [CollatzResearch.WordTrace]
  refine ⟨69478979137724324207999483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46319319425149549471999655 69478979137724324207999483)
  ·
    refine ⟨104218468706586486311999225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69478979137724324207999483 104218468706586486311999225)
    ·
      refine ⟨78163851529939864733999419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104218468706586486311999225 78163851529939864733999419)
      ·
        refine ⟨117245777294909797100999129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78163851529939864733999419 117245777294909797100999129)
        ·
          refine ⟨87934332971182347825749347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117245777294909797100999129 87934332971182347825749347)
          ·
            refine ⟨131901499456773521738624021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87934332971182347825749347 131901499456773521738624021)
            ·
              refine ⟨6182882787036258831498001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131901499456773521738624021 6182882787036258831498001)
              ·
                refine ⟨4637162090277194123623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182882787036258831498001 4637162090277194123623501)
                ·
                  refine ⟨1738935783853947796358813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4637162090277194123623501 1738935783853947796358813)
                  ·
                    refine ⟨652100918945230423634555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738935783853947796358813 652100918945230423634555)
                    ·
                      rfl

theorem cell22_1904943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_1904943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904943 prefixEnd_1904943 := by exact prefixLift 1904943
  have htrace : WordTrace (prefixWord ++ tailWord_1904943) baseStart_1904943 baseEnd_1904943 := by
    simpa [prefixWord, tailWord_1904943, baseEnd_1904943] using wordTrace_append hprefix tailTrace_1904943
  have hstable : (prefixWord ++ tailWord_1904943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904943).length < 2 ^ (prefixWord ++ tailWord_1904943).sum := by decide
  have hdescent : baseEnd_1904943 < baseStart_1904943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904945 : List Nat := [1, 2, 2, 3, 4, 2, 2, 6]
def baseStart_1904945 : Nat := 118140960795 + 1904945 * 2 ^ 59
def prefixEnd_1904945 : Nat := 4983230072969 + 3 ^ 40 * 1904945 * 2
def baseEnd_1904945 : Nat := 72455733731789231676061

theorem tailTrace_1904945 : CollatzResearch.WordTrace tailWord_1904945 prefixEnd_1904945 72455733731789231676061 := by
  unfold tailWord_1904945
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479052083717078549572289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46319368055811385699714859 69479052083717078549572289)
  ·
    refine ⟨52109289062787808912179217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69479052083717078549572289 52109289062787808912179217)
    ·
      refine ⟨39081966797090856684134413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52109289062787808912179217 39081966797090856684134413)
      ·
        refine ⟨14655737548909071256550405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39081966797090856684134413 14655737548909071256550405)
        ·
          refine ⟨2747950790420450860603201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14655737548909071256550405 2747950790420450860603201)
          ·
            refine ⟨2060963092815338145452401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747950790420450860603201 2060963092815338145452401)
            ·
              refine ⟨1545722319611503609089301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060963092815338145452401 1545722319611503609089301)
              ·
                refine ⟨72455733731789231676061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1545722319611503609089301 72455733731789231676061)
                ·
                  rfl

theorem cell22_1904945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 6].length) (baseStart_1904945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904945 prefixEnd_1904945 := by exact prefixLift 1904945
  have htrace : WordTrace (prefixWord ++ tailWord_1904945) baseStart_1904945 baseEnd_1904945 := by
    simpa [prefixWord, tailWord_1904945, baseEnd_1904945] using wordTrace_append hprefix tailTrace_1904945
  have hstable : (prefixWord ++ tailWord_1904945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904945).length < 2 ^ (prefixWord ++ tailWord_1904945).sum := by decide
  have hdescent : baseEnd_1904945 < baseStart_1904945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904956 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_1904956 : Nat := 118140960795 + 1904956 * 2 ^ 59
def prefixEnd_1904956 : Nat := 4983230072969 + 3 ^ 40 * 1904956 * 2
def baseEnd_1904956 : Nat := 217368456370300907686505

theorem tailTrace_1904956 : CollatzResearch.WordTrace tailWord_1904956 prefixEnd_1904956 217368456370300907686505 := by
  unfold tailWord_1904956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739726643338613714111361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46319635524451484952148481 34739726643338613714111361)
  ·
    refine ⟨26054794982503960285583521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34739726643338613714111361 26054794982503960285583521)
    ·
      refine ⟨19541096236877970214187641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26054794982503960285583521 19541096236877970214187641)
      ·
        refine ⟨14655822177658477660640731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19541096236877970214187641 14655822177658477660640731)
        ·
          refine ⟨21983733266487716490961097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655822177658477660640731 21983733266487716490961097)
          ·
            refine ⟨16487799949865787368220823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21983733266487716490961097 16487799949865787368220823)
            ·
              refine ⟨24731699924798681052331235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16487799949865787368220823 24731699924798681052331235)
              ·
                refine ⟨37097549887198021578496853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24731699924798681052331235 37097549887198021578496853)
                ·
                  refine ⟨217368456370300907686505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37097549887198021578496853 217368456370300907686505)
                  ·
                    rfl

theorem cell22_1904956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_1904956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904956 prefixEnd_1904956 := by exact prefixLift 1904956
  have htrace : WordTrace (prefixWord ++ tailWord_1904956) baseStart_1904956 baseEnd_1904956 := by
    simpa [prefixWord, tailWord_1904956, baseEnd_1904956] using wordTrace_append hprefix tailTrace_1904956
  have hstable : (prefixWord ++ tailWord_1904956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904956).length < 2 ^ (prefixWord ++ tailWord_1904956).sum := by decide
  have hdescent : baseEnd_1904956 < baseStart_1904956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904960 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_1904960 : Nat := 118140960795 + 1904960 * 2 ^ 59
def prefixEnd_1904960 : Nat := 4983230072969 + 3 ^ 40 * 1904960 * 2
def baseEnd_1904960 : Nat := 652106738392648045959503

theorem tailTrace_1904960 : CollatzResearch.WordTrace tailWord_1904960 prefixEnd_1904960 652106738392648045959503 := by
  unfold tailWord_1904960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739799589331368055684167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46319732785775157407578889 34739799589331368055684167)
  ·
    refine ⟨52109699383997052083526251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34739799589331368055684167 52109699383997052083526251)
    ·
      refine ⟨78164549075995578125289377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52109699383997052083526251 78164549075995578125289377)
      ·
        refine ⟨58623411806996683593967033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78164549075995578125289377 58623411806996683593967033)
        ·
          refine ⟨43967558855247512695475275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58623411806996683593967033 43967558855247512695475275)
          ·
            refine ⟨65951338282871269043212913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43967558855247512695475275 65951338282871269043212913)
            ·
              refine ⟨49463503712153451782409685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65951338282871269043212913 49463503712153451782409685)
              ·
                refine ⟨1159300868253596526150227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49463503712153451782409685 1159300868253596526150227)
                ·
                  refine ⟨1738951302380394789225341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159300868253596526150227 1738951302380394789225341)
                  ·
                    refine ⟨652106738392648045959503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1738951302380394789225341 652106738392648045959503)
                    ·
                      rfl

theorem cell22_1904960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_1904960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904960 prefixEnd_1904960 := by exact prefixLift 1904960
  have htrace : WordTrace (prefixWord ++ tailWord_1904960) baseStart_1904960 baseEnd_1904960 := by
    simpa [prefixWord, tailWord_1904960, baseEnd_1904960] using wordTrace_append hprefix tailTrace_1904960
  have hstable : (prefixWord ++ tailWord_1904960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904960).length < 2 ^ (prefixWord ++ tailWord_1904960).sum := by decide
  have hdescent : baseEnd_1904960 < baseStart_1904960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_1904971 : Nat := 118140960795 + 1904971 * 2 ^ 59
def prefixEnd_1904971 : Nat := 4983230072969 + 3 ^ 40 * 1904971 * 2
def baseEnd_1904971 : Nat := 652110503917447683934469

theorem tailTrace_1904971 : CollatzResearch.WordTrace tailWord_1904971 prefixEnd_1904971 652110503917447683934469 := by
  unfold tailWord_1904971
  simp only [CollatzResearch.WordTrace]
  refine ⟨69480000381622884990018767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46320000254415256660012511 69480000381622884990018767)
  ·
    refine ⟨104220000572434327485028151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69480000381622884990018767 104220000572434327485028151)
    ·
      refine ⟨156330000858651491227542227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104220000572434327485028151 156330000858651491227542227)
      ·
        refine ⟨234495001287977236841313341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156330000858651491227542227 234495001287977236841313341)
        ·
          refine ⟨87935625482991463815492503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234495001287977236841313341 87935625482991463815492503)
          ·
            refine ⟨131903438224487195723238755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87935625482991463815492503 131903438224487195723238755)
            ·
              refine ⟨197855157336730793584858133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131903438224487195723238755 197855157336730793584858133)
              ·
                refine ⟨9274460500159255949290225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197855157336730793584858133 9274460500159255949290225)
                ·
                  refine ⟨6955845375119441961967669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9274460500159255949290225 6955845375119441961967669)
                  ·
                    refine ⟨652110503917447683934469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6955845375119441961967669 652110503917447683934469)
                    ·
                      rfl

theorem cell22_1904971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_1904971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904971 prefixEnd_1904971 := by exact prefixLift 1904971
  have htrace : WordTrace (prefixWord ++ tailWord_1904971) baseStart_1904971 baseEnd_1904971 := by
    simpa [prefixWord, tailWord_1904971, baseEnd_1904971] using wordTrace_append hprefix tailTrace_1904971
  have hstable : (prefixWord ++ tailWord_1904971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904971).length < 2 ^ (prefixWord ++ tailWord_1904971).sum := by decide
  have hdescent : baseEnd_1904971 < baseStart_1904971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1904986 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1904986 : Nat := 118140960795 + 1904986 * 2 ^ 59
def prefixEnd_1904986 : Nat := 4983230072969 + 3 ^ 40 * 1904986 * 2
def baseEnd_1904986 : Nat := 652115638723992644809423

theorem tailTrace_1904986 : CollatzResearch.WordTrace tailWord_1904986 prefixEnd_1904986 652115638723992644809423 := by
  unfold tailWord_1904986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370136869142135637953703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46320364984379028367876541 17370136869142135637953703)
  ·
    refine ⟨26055205303713203456930555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17370136869142135637953703 26055205303713203456930555)
    ·
      refine ⟨39082807955569805185395833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26055205303713203456930555 39082807955569805185395833)
      ·
        refine ⟨29312105966677353889046875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39082807955569805185395833 29312105966677353889046875)
        ·
          refine ⟨43968158950016030833570313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29312105966677353889046875 43968158950016030833570313)
          ·
            refine ⟨32976119212512023125177735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43968158950016030833570313 32976119212512023125177735)
            ·
              refine ⟨49464178818768034687766603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32976119212512023125177735 49464178818768034687766603)
              ·
                refine ⟨74196268228152052031649905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49464178818768034687766603 74196268228152052031649905)
                ·
                  refine ⟨55647201171114039023737429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74196268228152052031649905 55647201171114039023737429)
                  ·
                    refine ⟨652115638723992644809423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55647201171114039023737429 652115638723992644809423)
                    ·
                      rfl

theorem cell22_1904986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1904986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1904986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1904986 prefixEnd_1904986 := by exact prefixLift 1904986
  have htrace : WordTrace (prefixWord ++ tailWord_1904986) baseStart_1904986 baseEnd_1904986 := by
    simpa [prefixWord, tailWord_1904986, baseEnd_1904986] using wordTrace_append hprefix tailTrace_1904986
  have hstable : (prefixWord ++ tailWord_1904986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1904986).length < 2 ^ (prefixWord ++ tailWord_1904986).sum := by decide
  have hdescent : baseEnd_1904986 < baseStart_1904986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1904986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905001 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 8]
def baseStart_1905001 : Nat := 118140960795 + 1905001 * 2 ^ 59
def prefixEnd_1905001 : Nat := 4983230072969 + 3 ^ 40 * 1905001 * 2
def baseEnd_1905001 : Nat := 217373591176845868561459

theorem tailTrace_1905001 : CollatzResearch.WordTrace tailWord_1905001 prefixEnd_1905001 217373591176845868561459 := by
  unfold tailWord_1905001
  simp only [CollatzResearch.WordTrace]
  refine ⟨69481094571514200113610857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46320729714342800075740571 69481094571514200113610857)
  ·
    refine ⟨52110820928635650085208143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69481094571514200113610857 52110820928635650085208143)
    ·
      refine ⟨78166231392953475127812215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52110820928635650085208143 78166231392953475127812215)
      ·
        refine ⟨117249347089430212691718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78166231392953475127812215 117249347089430212691718323)
        ·
          refine ⟨175874020634145319037577485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117249347089430212691718323 175874020634145319037577485)
          ·
            refine ⟨65952757737804494639091557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175874020634145319037577485 65952757737804494639091557)
            ·
              refine ⟨12366142075838342744829667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65952757737804494639091557 12366142075838342744829667)
              ·
                refine ⟨18549213113757514117244501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366142075838342744829667 18549213113757514117244501)
                ·
                  refine ⟨217373591176845868561459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18549213113757514117244501 217373591176845868561459)
                  ·
                    rfl

theorem cell22_1905001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_1905001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905001 prefixEnd_1905001 := by exact prefixLift 1905001
  have htrace : WordTrace (prefixWord ++ tailWord_1905001) baseStart_1905001 baseEnd_1905001 := by
    simpa [prefixWord, tailWord_1905001, baseEnd_1905001] using wordTrace_append hprefix tailTrace_1905001
  have hstable : (prefixWord ++ tailWord_1905001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905001).length < 2 ^ (prefixWord ++ tailWord_1905001).sum := by decide
  have hdescent : baseEnd_1905001 < baseStart_1905001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905035 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 4]
def baseStart_1905035 : Nat := 118140960795 + 1905035 * 2 ^ 59
def prefixEnd_1905035 : Nat := 4983230072969 + 3 ^ 40 * 1905035 * 2
def baseEnd_1905035 : Nat := 217377470808457616778091

theorem tailTrace_1905035 : CollatzResearch.WordTrace tailWord_1905035 prefixEnd_1905035 217377470808457616778091 := by
  unfold tailWord_1905035
  simp only [CollatzResearch.WordTrace]
  refine ⟨69482334653391023920348559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46321556435594015946899039 69482334653391023920348559)
  ·
    refine ⟨104223501980086535880522839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69482334653391023920348559 104223501980086535880522839)
    ·
      refine ⟨156335252970129803820784259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104223501980086535880522839 156335252970129803820784259)
      ·
        refine ⟨234502879455194705731176389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156335252970129803820784259 234502879455194705731176389)
        ·
          refine ⟨43969289897849007324595573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234502879455194705731176389 43969289897849007324595573)
          ·
            refine ⟨4122120927923344436680835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43969289897849007324595573 4122120927923344436680835)
            ·
              refine ⟨6183181391885016655021253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122120927923344436680835 6183181391885016655021253)
              ·
                refine ⟨1159346510978440622816485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6183181391885016655021253 1159346510978440622816485)
                ·
                  refine ⟨217377470808457616778091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159346510978440622816485 217377470808457616778091)
                  ·
                    rfl

theorem cell22_1905035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 4].length) (baseStart_1905035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905035 prefixEnd_1905035 := by exact prefixLift 1905035
  have htrace : WordTrace (prefixWord ++ tailWord_1905035) baseStart_1905035 baseEnd_1905035 := by
    simpa [prefixWord, tailWord_1905035, baseEnd_1905035] using wordTrace_append hprefix tailTrace_1905035
  have hstable : (prefixWord ++ tailWord_1905035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905035).length < 2 ^ (prefixWord ++ tailWord_1905035).sum := by decide
  have hdescent : baseEnd_1905035 < baseStart_1905035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905050 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1905050 : Nat := 118140960795 + 1905050 * 2 ^ 59
def prefixEnd_1905050 : Nat := 4983230072969 + 3 ^ 40 * 1905050 * 2
def baseEnd_1905050 : Nat := 652137547231917811209227

theorem tailTrace_1905050 : CollatzResearch.WordTrace tailWord_1905050 prefixEnd_1905050 652137547231917811209227 := by
  unfold tailWord_1905050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370720437084170370536151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46321921165557787654763069 17370720437084170370536151)
  ·
    refine ⟨26056080655626255555804227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17370720437084170370536151 26056080655626255555804227)
    ·
      refine ⟨39084120983439383333706341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26056080655626255555804227 39084120983439383333706341)
      ·
        refine ⟨7328272684394884375069939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39084120983439383333706341 7328272684394884375069939)
        ·
          refine ⟨10992409026592326562604909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328272684394884375069939 10992409026592326562604909)
          ·
            refine ⟨4122153384972122460976841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10992409026592326562604909 4122153384972122460976841)
            ·
              refine ⟨3091615038729091845732631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122153384972122460976841 3091615038729091845732631)
              ·
                refine ⟨4637422558093637768598947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091615038729091845732631 4637422558093637768598947)
                ·
                  refine ⟨6956133837140456652898421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637422558093637768598947 6956133837140456652898421)
                  ·
                    refine ⟨652137547231917811209227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6956133837140456652898421 652137547231917811209227)
                    ·
                      rfl

theorem cell22_1905050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1905050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905050 prefixEnd_1905050 := by exact prefixLift 1905050
  have htrace : WordTrace (prefixWord ++ tailWord_1905050) baseStart_1905050 baseEnd_1905050 := by
    simpa [prefixWord, tailWord_1905050, baseEnd_1905050] using wordTrace_append hprefix tailTrace_1905050
  have hstable : (prefixWord ++ tailWord_1905050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905050).length < 2 ^ (prefixWord ++ tailWord_1905050).sum := by decide
  have hdescent : baseEnd_1905050 < baseStart_1905050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905069 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1905069 : Nat := 118140960795 + 1905069 * 2 ^ 59
def prefixEnd_1905069 : Nat := 4983230072969 + 3 ^ 40 * 1905069 * 2
def baseEnd_1905069 : Nat := 217381350440069364994723

theorem tailTrace_1905069 : CollatzResearch.WordTrace tailWord_1905069 prefixEnd_1905069 217381350440069364994723 := by
  unfold tailWord_1905069
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483574735267847727086261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46322383156845231818057507 69483574735267847727086261)
  ·
    refine ⟨6514085131431360724414337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69483574735267847727086261 6514085131431360724414337)
    ·
      refine ⟨4885563848573520543310753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6514085131431360724414337 4885563848573520543310753)
      ·
        refine ⟨3664172886430140407483065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4885563848573520543310753 3664172886430140407483065)
        ·
          refine ⟨2748129664822605305612299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664172886430140407483065 2748129664822605305612299)
          ·
            refine ⟨4122194497233907958418449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748129664822605305612299 4122194497233907958418449)
            ·
              refine ⟨3091645872925430968813837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122194497233907958418449 3091645872925430968813837)
              ·
                refine ⟨1159367202347036613305189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3091645872925430968813837 1159367202347036613305189)
                ·
                  refine ⟨217381350440069364994723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159367202347036613305189 217381350440069364994723)
                  ·
                    rfl

theorem cell22_1905069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1905069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905069 prefixEnd_1905069 := by exact prefixLift 1905069
  have htrace : WordTrace (prefixWord ++ tailWord_1905069) baseStart_1905069 baseEnd_1905069 := by
    simpa [prefixWord, tailWord_1905069, baseEnd_1905069] using wordTrace_append hprefix tailTrace_1905069
  have hstable : (prefixWord ++ tailWord_1905069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905069).length < 2 ^ (prefixWord ++ tailWord_1905069).sum := by decide
  have hdescent : baseEnd_1905069 < baseStart_1905069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905084 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1905084 : Nat := 118140960795 + 1905084 * 2 ^ 59
def prefixEnd_1905084 : Nat := 4983230072969 + 3 ^ 40 * 1905084 * 2
def baseEnd_1905084 : Nat := 652149186126753055859123

theorem tailTrace_1905084 : CollatzResearch.WordTrace tailWord_1905084 prefixEnd_1905084 652149186126753055859123 := by
  unfold tailWord_1905084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34742060915106752644441153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46322747886809003525921537 34742060915106752644441153)
  ·
    refine ⟨26056545686330064483330865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34742060915106752644441153 26056545686330064483330865)
    ·
      refine ⟨19542409264747548362498149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26056545686330064483330865 19542409264747548362498149)
      ·
        refine ⟨3664201737140165317968403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19542409264747548362498149 3664201737140165317968403)
        ·
          refine ⟨5496302605710247976952605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664201737140165317968403 5496302605710247976952605)
          ·
            refine ⟨2061113477141342991357227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5496302605710247976952605 2061113477141342991357227)
            ·
              refine ⟨3091670215712014487035841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061113477141342991357227 3091670215712014487035841)
              ·
                refine ⟨2318752661784010865276881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3091670215712014487035841 2318752661784010865276881)
                ·
                  refine ⟨1739064496338008148957661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2318752661784010865276881 1739064496338008148957661)
                  ·
                    refine ⟨652149186126753055859123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739064496338008148957661 652149186126753055859123)
                    ·
                      rfl

theorem cell22_1905084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1905084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905084 prefixEnd_1905084 := by exact prefixLift 1905084
  have htrace : WordTrace (prefixWord ++ tailWord_1905084) baseStart_1905084 baseEnd_1905084 := by
    simpa [prefixWord, tailWord_1905084, baseEnd_1905084] using wordTrace_append hprefix tailTrace_1905084
  have hstable : (prefixWord ++ tailWord_1905084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905084).length < 2 ^ (prefixWord ++ tailWord_1905084).sum := by decide
  have hdescent : baseEnd_1905084 < baseStart_1905084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905095 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1905095 : Nat := 118140960795 + 1905095 * 2 ^ 59
def prefixEnd_1905095 : Nat := 4983230072969 + 3 ^ 40 * 1905095 * 2
def baseEnd_1905095 : Nat := 652152951651552693834089

theorem tailTrace_1905095 : CollatzResearch.WordTrace tailWord_1905095 prefixEnd_1905095 652152951651552693834089 := by
  unfold tailWord_1905095
  simp only [CollatzResearch.WordTrace]
  refine ⟨69484523033173654167532739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46323015355449102778355159 69484523033173654167532739)
  ·
    refine ⟨104226784549760481251299109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69484523033173654167532739 104226784549760481251299109)
    ·
      refine ⟨19542522103080090234618583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104226784549760481251299109 19542522103080090234618583)
      ·
        refine ⟨29313783154620135351927875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19542522103080090234618583 29313783154620135351927875)
        ·
          refine ⟨43970674731930203027891813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29313783154620135351927875 43970674731930203027891813)
          ·
            refine ⟨8244501512236913067729715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43970674731930203027891813 8244501512236913067729715)
            ·
              refine ⟨12366752268355369601594573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244501512236913067729715 12366752268355369601594573)
              ·
                refine ⟨4637532100633263600597965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12366752268355369601594573 4637532100633263600597965)
                ·
                  refine ⟨1739074537737473850224237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4637532100633263600597965 1739074537737473850224237)
                  ·
                    refine ⟨652152951651552693834089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739074537737473850224237 652152951651552693834089)
                    ·
                      rfl

theorem cell22_1905095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1905095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905095 prefixEnd_1905095 := by exact prefixLift 1905095
  have htrace : WordTrace (prefixWord ++ tailWord_1905095) baseStart_1905095 baseEnd_1905095 := by
    simpa [prefixWord, tailWord_1905095, baseEnd_1905095] using wordTrace_append hprefix tailTrace_1905095
  have hstable : (prefixWord ++ tailWord_1905095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905095).length < 2 ^ (prefixWord ++ tailWord_1905095).sum := by decide
  have hdescent : baseEnd_1905095 < baseStart_1905095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905159 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 5]
def baseStart_1905159 : Nat := 118140960795 + 1905159 * 2 ^ 59
def prefixEnd_1905159 : Nat := 4983230072969 + 3 ^ 40 * 1905159 * 2
def baseEnd_1905159 : Nat := 217391620053159286744631

theorem tailTrace_1905159 : CollatzResearch.WordTrace tailWord_1905159 prefixEnd_1905159 217391620053159286744631 := by
  unfold tailWord_1905159
  simp only [CollatzResearch.WordTrace]
  refine ⟨69486857304941793097862531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46324571536627862065241687 69486857304941793097862531)
  ·
    refine ⟨104230285957412689646793797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69486857304941793097862531 104230285957412689646793797)
    ·
      refine ⟨19543178617014879308773837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104230285957412689646793797 19543178617014879308773837)
      ·
        refine ⟨7328691981380579740790189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19543178617014879308773837 7328691981380579740790189)
        ·
          refine ⟨2748259493017717402796321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7328691981380579740790189 2748259493017717402796321)
          ·
            refine ⟨2061194619763288052097241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748259493017717402796321 2061194619763288052097241)
            ·
              refine ⟨1545895964822466039072931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061194619763288052097241 1545895964822466039072931)
              ·
                refine ⟨2318843947233699058609397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545895964822466039072931 2318843947233699058609397)
                ·
                  refine ⟨217391620053159286744631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318843947233699058609397 217391620053159286744631)
                  ·
                    rfl

theorem cell22_1905159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 5].length) (baseStart_1905159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905159 prefixEnd_1905159 := by exact prefixLift 1905159
  have htrace : WordTrace (prefixWord ++ tailWord_1905159) baseStart_1905159 baseEnd_1905159 := by
    simpa [prefixWord, tailWord_1905159, baseEnd_1905159] using wordTrace_append hprefix tailTrace_1905159
  have hstable : (prefixWord ++ tailWord_1905159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905159).length < 2 ^ (prefixWord ++ tailWord_1905159).sum := by decide
  have hdescent : baseEnd_1905159 < baseStart_1905159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905185 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1905185 : Nat := 118140960795 + 1905185 * 2 ^ 59
def prefixEnd_1905185 : Nat := 4983230072969 + 3 ^ 40 * 1905185 * 2
def baseEnd_1905185 : Nat := 652183760490822459083813

theorem tailTrace_1905185 : CollatzResearch.WordTrace tailWord_1905185 prefixEnd_1905185 652183760490822459083813 := by
  unfold tailWord_1905185
  simp only [CollatzResearch.WordTrace]
  refine ⟨69487805602847599538309009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46325203735231733025539339 69487805602847599538309009)
  ·
    refine ⟨52115854202135699653731757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69487805602847599538309009 52115854202135699653731757)
    ·
      refine ⟨19543445325800887370149409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52115854202135699653731757 19543445325800887370149409)
      ·
        refine ⟨14657583994350665527612057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19543445325800887370149409 14657583994350665527612057)
        ·
          refine ⟨10993187995762999145709043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14657583994350665527612057 10993187995762999145709043)
          ·
            refine ⟨16489781993644498718563565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993187995762999145709043 16489781993644498718563565)
            ·
              refine ⟨6183668247616687019461337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16489781993644498718563565 6183668247616687019461337)
              ·
                refine ⟨4637751185712515264596003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183668247616687019461337 4637751185712515264596003)
                ·
                  refine ⟨6956626778568772896894005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637751185712515264596003 6956626778568772896894005)
                  ·
                    refine ⟨652183760490822459083813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6956626778568772896894005 652183760490822459083813)
                    ·
                      rfl

theorem cell22_1905185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1905185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905185 prefixEnd_1905185 := by exact prefixLift 1905185
  have htrace : WordTrace (prefixWord ++ tailWord_1905185) baseStart_1905185 baseEnd_1905185 := by
    simpa [prefixWord, tailWord_1905185, baseEnd_1905185] using wordTrace_append hprefix tailTrace_1905185
  have hstable : (prefixWord ++ tailWord_1905185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905185).length < 2 ^ (prefixWord ++ tailWord_1905185).sum := by decide
  have hdescent : baseEnd_1905185 < baseStart_1905185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905197 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1905197 : Nat := 118140960795 + 1905197 * 2 ^ 59
def prefixEnd_1905197 : Nat := 4983230072969 + 3 ^ 40 * 1905197 * 2
def baseEnd_1905197 : Nat := 652187868336058427783777

theorem tailTrace_1905197 : CollatzResearch.WordTrace tailWord_1905197 prefixEnd_1905197 652187868336058427783777 := by
  unfold tailWord_1905197
  simp only [CollatzResearch.WordTrace]
  refine ⟨69488243278804125587745845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46325495519202750391830563 69488243278804125587745845)
  ·
    refine ⟨6514522807387886773851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69488243278804125587745845 6514522807387886773851173)
    ·
      refine ⟨1221473026385228770097095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6514522807387886773851173 1221473026385228770097095)
      ·
        refine ⟨1832209539577843155145643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221473026385228770097095 1832209539577843155145643)
        ·
          refine ⟨2748314309366764732718465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832209539577843155145643 2748314309366764732718465)
          ·
            refine ⟨2061235732025073549538849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748314309366764732718465 2061235732025073549538849)
            ·
              refine ⟨1545926799018805162154137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061235732025073549538849 1545926799018805162154137)
              ·
                refine ⟨1159445099264103871615603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545926799018805162154137 1159445099264103871615603)
                ·
                  refine ⟨1739167648896155807423405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159445099264103871615603 1739167648896155807423405)
                  ·
                    refine ⟨652187868336058427783777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739167648896155807423405 652187868336058427783777)
                    ·
                      rfl

theorem cell22_1905197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1905197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905197 prefixEnd_1905197 := by exact prefixLift 1905197
  have htrace : WordTrace (prefixWord ++ tailWord_1905197) baseStart_1905197 baseEnd_1905197 := by
    simpa [prefixWord, tailWord_1905197, baseEnd_1905197] using wordTrace_append hprefix tailTrace_1905197
  have hstable : (prefixWord ++ tailWord_1905197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905197).length < 2 ^ (prefixWord ++ tailWord_1905197).sum := by decide
  have hdescent : baseEnd_1905197 < baseStart_1905197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905200 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_1905200 : Nat := 118140960795 + 1905200 * 2 ^ 59
def prefixEnd_1905200 : Nat := 4983230072969 + 3 ^ 40 * 1905200 * 2
def baseEnd_1905200 : Nat := 652188895297367419958767

theorem tailTrace_1905200 : CollatzResearch.WordTrace tailWord_1905200 prefixEnd_1905200 652188895297367419958767 := by
  unfold tailWord_1905200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34744176348896628550052527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46325568465195504733403369 34744176348896628550052527)
  ·
    refine ⟨52116264523344942825078791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34744176348896628550052527 52116264523344942825078791)
    ·
      refine ⟨78174396785017414237618187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52116264523344942825078791 78174396785017414237618187)
      ·
        refine ⟨117261595177526121356427281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78174396785017414237618187 117261595177526121356427281)
        ·
          refine ⟨87946196383144591017320461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117261595177526121356427281 87946196383144591017320461)
          ·
            refine ⟨32979823643679221631495173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87946196383144591017320461 32979823643679221631495173)
            ·
              refine ⟨6183716933189854055905345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32979823643679221631495173 6183716933189854055905345)
              ·
                refine ⟨4637787699892390541929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183716933189854055905345 4637787699892390541929009)
                ·
                  refine ⟨3478340774919292906446757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637787699892390541929009 3478340774919292906446757)
                  ·
                    refine ⟨652188895297367419958767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478340774919292906446757 652188895297367419958767)
                    ·
                      rfl

theorem cell22_1905200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_1905200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905200 prefixEnd_1905200 := by exact prefixLift 1905200
  have htrace : WordTrace (prefixWord ++ tailWord_1905200) baseStart_1905200 baseEnd_1905200 := by
    simpa [prefixWord, tailWord_1905200, baseEnd_1905200] using wordTrace_append hprefix tailTrace_1905200
  have hstable : (prefixWord ++ tailWord_1905200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905200).length < 2 ^ (prefixWord ++ tailWord_1905200).sum := by decide
  have hdescent : baseEnd_1905200 < baseStart_1905200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905202 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1905202 : Nat := 118140960795 + 1905202 * 2 ^ 59
def prefixEnd_1905202 : Nat := 4983230072969 + 3 ^ 40 * 1905202 * 2
def baseEnd_1905202 : Nat := 652189579938240081408761

theorem tailTrace_1905202 : CollatzResearch.WordTrace tailWord_1905202 prefixEnd_1905202 652189579938240081408761 := by
  unfold tailWord_1905202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372106410946502860419465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46325617095857340961118573 17372106410946502860419465)
  ·
    refine ⟨13029079808209877145314599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17372106410946502860419465 13029079808209877145314599)
    ·
      refine ⟨19543619712314815717971899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13029079808209877145314599 19543619712314815717971899)
      ·
        refine ⟨29315429568472223576957849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543619712314815717971899 29315429568472223576957849)
        ·
          refine ⟨21986572176354167682718387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29315429568472223576957849 21986572176354167682718387)
          ·
            refine ⟨32979858264531251524077581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21986572176354167682718387 32979858264531251524077581)
            ·
              refine ⟨12367446849199219321529093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32979858264531251524077581 12367446849199219321529093)
              ·
                refine ⟨2318896284224853622786705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12367446849199219321529093 2318896284224853622786705)
                ·
                  refine ⟨1739172213168640217090029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2318896284224853622786705 1739172213168640217090029)
                  ·
                    refine ⟨652189579938240081408761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739172213168640217090029 652189579938240081408761)
                    ·
                      rfl

theorem cell22_1905202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1905202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905202 prefixEnd_1905202 := by exact prefixLift 1905202
  have htrace : WordTrace (prefixWord ++ tailWord_1905202) baseStart_1905202 baseEnd_1905202 := by
    simpa [prefixWord, tailWord_1905202, baseEnd_1905202] using wordTrace_append hprefix tailTrace_1905202
  have hstable : (prefixWord ++ tailWord_1905202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905202).length < 2 ^ (prefixWord ++ tailWord_1905202).sum := by decide
  have hdescent : baseEnd_1905202 < baseStart_1905202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905264 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_1905264 : Nat := 118140960795 + 1905264 * 2 ^ 59
def prefixEnd_1905264 : Nat := 4983230072969 + 3 ^ 40 * 1905264 * 2
def baseEnd_1905264 : Nat := 652210803805292586358571

theorem tailTrace_1905264 : CollatzResearch.WordTrace tailWord_1905264 prefixEnd_1905264 652210803805292586358571 := by
  unfold tailWord_1905264
  simp only [CollatzResearch.WordTrace]
  refine ⟨34745343484780698015217423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46327124646374264020289897 34745343484780698015217423)
  ·
    refine ⟨52118015227171047022826135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34745343484780698015217423 52118015227171047022826135)
    ·
      refine ⟨78177022840756570534239203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52118015227171047022826135 78177022840756570534239203)
      ·
        refine ⟨117265534261134855801358805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78177022840756570534239203 117265534261134855801358805)
        ·
          refine ⟨2748410959245348182844347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117265534261134855801358805 2748410959245348182844347)
          ·
            refine ⟨4122616438868022274266521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748410959245348182844347 4122616438868022274266521)
            ·
              refine ⟨3091962329151016705699891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122616438868022274266521 3091962329151016705699891)
              ·
                refine ⟨4637943493726525058549837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091962329151016705699891 4637943493726525058549837)
                ·
                  refine ⟨1739228810147446896956189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4637943493726525058549837 1739228810147446896956189)
                  ·
                    refine ⟨652210803805292586358571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739228810147446896956189 652210803805292586358571)
                    ·
                      rfl

theorem cell22_1905264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_1905264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905264 prefixEnd_1905264 := by exact prefixLift 1905264
  have htrace : WordTrace (prefixWord ++ tailWord_1905264) baseStart_1905264 baseEnd_1905264 := by
    simpa [prefixWord, tailWord_1905264, baseEnd_1905264] using wordTrace_append hprefix tailTrace_1905264
  have hstable : (prefixWord ++ tailWord_1905264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905264).length < 2 ^ (prefixWord ++ tailWord_1905264).sum := by decide
  have hdescent : baseEnd_1905264 < baseStart_1905264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905298 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1905298 : Nat := 118140960795 + 1905298 * 2 ^ 59
def prefixEnd_1905298 : Nat := 4983230072969 + 3 ^ 40 * 1905298 * 2
def baseEnd_1905298 : Nat := 652222442700127831008467

theorem tailTrace_1905298 : CollatzResearch.WordTrace tailWord_1905298 prefixEnd_1905298 652222442700127831008467 := by
  unfold tailWord_1905298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372981762859554959293137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46327951367625479891448365 17372981762859554959293137)
  ·
    refine ⟨13029736322144666219469853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17372981762859554959293137 13029736322144666219469853)
    ·
      refine ⟨4886151120804249832301195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13029736322144666219469853 4886151120804249832301195)
      ·
        refine ⟨7329226681206374748451793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886151120804249832301195 7329226681206374748451793)
        ·
          refine ⟨5496920010904781061338845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7329226681206374748451793 5496920010904781061338845)
          ·
            refine ⟨2061345004089292898002067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5496920010904781061338845 2061345004089292898002067)
            ·
              refine ⟨3092017506133939347003101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061345004089292898002067 3092017506133939347003101)
              ·
                refine ⟨1159506564800227255126163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092017506133939347003101 1159506564800227255126163)
                ·
                  refine ⟨1739259847200340882689245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159506564800227255126163 1739259847200340882689245)
                  ·
                    refine ⟨652222442700127831008467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739259847200340882689245 652222442700127831008467)
                    ·
                      rfl

theorem cell22_1905298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1905298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905298 prefixEnd_1905298 := by exact prefixLift 1905298
  have htrace : WordTrace (prefixWord ++ tailWord_1905298) baseStart_1905298 baseEnd_1905298 := by
    simpa [prefixWord, tailWord_1905298, baseEnd_1905298] using wordTrace_append hprefix tailTrace_1905298
  have hstable : (prefixWord ++ tailWord_1905298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905298).length < 2 ^ (prefixWord ++ tailWord_1905298).sum := by decide
  have hdescent : baseEnd_1905298 < baseStart_1905298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905352 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1905352 : Nat := 118140960795 + 1905352 * 2 ^ 59
def prefixEnd_1905352 : Nat := 4983230072969 + 3 ^ 40 * 1905352 * 2
def baseEnd_1905352 : Nat := 652240928003689690158301

theorem tailTrace_1905352 : CollatzResearch.WordTrace tailWord_1905352 prefixEnd_1905352 652240928003689690158301 := by
  unfold tailWord_1905352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34746948296621293529819155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46329264395495058039758873 34746948296621293529819155)
  ·
    refine ⟨52120422444931940294728733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34746948296621293529819155 52120422444931940294728733)
    ·
      refine ⟨19545158416849477610523275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52120422444931940294728733 19545158416849477610523275)
      ·
        refine ⟨29317737625274216415784913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545158416849477610523275 29317737625274216415784913)
        ·
          refine ⟨21988303218955662311838685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29317737625274216415784913 21988303218955662311838685)
          ·
            refine ⟨8245613707108373366939507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21988303218955662311838685 8245613707108373366939507)
            ·
              refine ⟨12368420560662560050409261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245613707108373366939507 12368420560662560050409261)
              ·
                refine ⟨4638157710248460018903473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12368420560662560050409261 4638157710248460018903473)
                ·
                  refine ⟨3478618282686345014177605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638157710248460018903473 3478618282686345014177605)
                  ·
                    refine ⟨652240928003689690158301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478618282686345014177605 652240928003689690158301)
                    ·
                      rfl

theorem cell22_1905352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1905352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905352 prefixEnd_1905352 := by exact prefixLift 1905352
  have htrace : WordTrace (prefixWord ++ tailWord_1905352) baseStart_1905352 baseEnd_1905352 := by
    simpa [prefixWord, tailWord_1905352, baseEnd_1905352] using wordTrace_append hprefix tailTrace_1905352
  have hstable : (prefixWord ++ tailWord_1905352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905352).length < 2 ^ (prefixWord ++ tailWord_1905352).sum := by decide
  have hdescent : baseEnd_1905352 < baseStart_1905352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905384 : List Nat := [2, 1, 4, 1, 4, 2, 1, 7]
def baseStart_1905384 : Nat := 118140960795 + 1905384 * 2 ^ 59
def prefixEnd_1905384 : Nat := 4983230072969 + 3 ^ 40 * 1905384 * 2
def baseEnd_1905384 : Nat := 72472431361961363706467

theorem tailTrace_1905384 : CollatzResearch.WordTrace tailWord_1905384 prefixEnd_1905384 72472431361961363706467 := by
  unfold tailWord_1905384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34747531864563328262401603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46330042486084437683202137 34747531864563328262401603)
  ·
    refine ⟨52121297796844992393602405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34747531864563328262401603 52121297796844992393602405)
    ·
      refine ⟨9772743336908436073800451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52121297796844992393602405 9772743336908436073800451)
      ·
        refine ⟨14659115005362654110700677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772743336908436073800451 14659115005362654110700677)
        ·
          refine ⟨2748584063505497645756377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14659115005362654110700677 2748584063505497645756377)
          ·
            refine ⟨2061438047629123234317283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748584063505497645756377 2061438047629123234317283)
            ·
              refine ⟨3092157071443684851475925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061438047629123234317283 3092157071443684851475925)
              ·
                refine ⟨72472431361961363706467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3092157071443684851475925 72472431361961363706467)
                ·
                  rfl

theorem cell22_1905384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_1905384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905384 prefixEnd_1905384 := by exact prefixLift 1905384
  have htrace : WordTrace (prefixWord ++ tailWord_1905384) baseStart_1905384 baseEnd_1905384 := by
    simpa [prefixWord, tailWord_1905384, baseEnd_1905384] using wordTrace_append hprefix tailTrace_1905384
  have hstable : (prefixWord ++ tailWord_1905384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905384).length < 2 ^ (prefixWord ++ tailWord_1905384).sum := by decide
  have hdescent : baseEnd_1905384 < baseStart_1905384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905395 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 9]
def baseStart_1905395 : Nat := 118140960795 + 1905395 * 2 ^ 59
def prefixEnd_1905395 : Nat := 4983230072969 + 3 ^ 40 * 1905395 * 2
def baseEnd_1905395 : Nat := 217418549260817303777723

theorem tailTrace_1905395 : CollatzResearch.WordTrace tailWord_1905395 prefixEnd_1905395 217418549260817303777723 := by
  unfold tailWord_1905395
  simp only [CollatzResearch.WordTrace]
  refine ⟨69495464932086805403453639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46330309954724536935635759 69495464932086805403453639)
  ·
    refine ⟨104243197398130208105180459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69495464932086805403453639 104243197398130208105180459)
    ·
      refine ⟨156364796097195312157770689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104243197398130208105180459 156364796097195312157770689)
      ·
        refine ⟨117273597072896484118328017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156364796097195312157770689 117273597072896484118328017)
        ·
          refine ⟨87955197804672363088746013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117273597072896484118328017 87955197804672363088746013)
          ·
            refine ⟨32983199176752136158279755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87955197804672363088746013 32983199176752136158279755)
            ·
              refine ⟨49474798765128204237419633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32983199176752136158279755 49474798765128204237419633)
              ·
                refine ⟨37106099073846153178064725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49474798765128204237419633 37106099073846153178064725)
                ·
                  refine ⟨217418549260817303777723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37106099073846153178064725 217418549260817303777723)
                  ·
                    rfl

theorem cell22_1905395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_1905395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905395 prefixEnd_1905395 := by exact prefixLift 1905395
  have htrace : WordTrace (prefixWord ++ tailWord_1905395) baseStart_1905395 baseEnd_1905395 := by
    simpa [prefixWord, tailWord_1905395, baseEnd_1905395] using wordTrace_append hprefix tailTrace_1905395
  have hstable : (prefixWord ++ tailWord_1905395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905395).length < 2 ^ (prefixWord ++ tailWord_1905395).sum := by decide
  have hdescent : baseEnd_1905395 < baseStart_1905395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905412 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1905412 : Nat := 118140960795 + 1905412 * 2 ^ 59
def prefixEnd_1905412 : Nat := 4983230072969 + 3 ^ 40 * 1905412 * 2
def baseEnd_1905412 : Nat := 217420489076623177886039

theorem tailTrace_1905412 : CollatzResearch.WordTrace tailWord_1905412 prefixEnd_1905412 217420489076623177886039 := by
  unfold tailWord_1905412
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748042486512608653411245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46330723315350144871214993 34748042486512608653411245)
  ·
    refine ⟨13030515932442228245029217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34748042486512608653411245 13030515932442228245029217)
    ·
      refine ⟨9772886949331671183771913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13030515932442228245029217 9772886949331671183771913)
      ·
        refine ⟨7329665211998753387828935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9772886949331671183771913 7329665211998753387828935)
        ·
          refine ⟨10994497817998130081743403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329665211998753387828935 10994497817998130081743403)
          ·
            refine ⟨16491746726997195122615105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994497817998130081743403 16491746726997195122615105)
            ·
              refine ⟨12368810045247896341961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16491746726997195122615105 12368810045247896341961329)
              ·
                refine ⟨9276607533935922256470997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12368810045247896341961329 9276607533935922256470997)
                ·
                  refine ⟨217420489076623177886039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9276607533935922256470997 217420489076623177886039)
                  ·
                    rfl

theorem cell22_1905412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1905412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905412 prefixEnd_1905412 := by exact prefixLift 1905412
  have htrace : WordTrace (prefixWord ++ tailWord_1905412) baseStart_1905412 baseEnd_1905412 := by
    simpa [prefixWord, tailWord_1905412, baseEnd_1905412] using wordTrace_append hprefix tailTrace_1905412
  have hstable : (prefixWord ++ tailWord_1905412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905412).length < 2 ^ (prefixWord ++ tailWord_1905412).sum := by decide
  have hdescent : baseEnd_1905412 < baseStart_1905412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905416 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_1905416 : Nat := 118140960795 + 1905416 * 2 ^ 59
def prefixEnd_1905416 : Nat := 4983230072969 + 3 ^ 40 * 1905416 * 2
def baseEnd_1905416 : Nat := 652262836511614856558105

theorem tailTrace_1905416 : CollatzResearch.WordTrace tailWord_1905416 prefixEnd_1905416 652262836511614856558105 := by
  unfold tailWord_1905416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748115432505362994984051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46330820576673817326645401 34748115432505362994984051)
  ·
    refine ⟨52122173148758044492476077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34748115432505362994984051 52122173148758044492476077)
    ·
      refine ⟨19545814930784266684678529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52122173148758044492476077 19545814930784266684678529)
      ·
        refine ⟨14659361198088200013508897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19545814930784266684678529 14659361198088200013508897)
        ·
          refine ⟨10994520898566150010131673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659361198088200013508897 10994520898566150010131673)
          ·
            refine ⟨8245890673924612507598755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994520898566150010131673 8245890673924612507598755)
            ·
              refine ⟨12368836010886918761398133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245890673924612507598755 12368836010886918761398133)
              ·
                refine ⟨1159578376020648633881075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12368836010886918761398133 1159578376020648633881075)
                ·
                  refine ⟨1739367564030972950821613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159578376020648633881075 1739367564030972950821613)
                  ·
                    refine ⟨652262836511614856558105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739367564030972950821613 652262836511614856558105)
                    ·
                      rfl

theorem cell22_1905416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_1905416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905416 prefixEnd_1905416 := by exact prefixLift 1905416
  have htrace : WordTrace (prefixWord ++ tailWord_1905416) baseStart_1905416 baseEnd_1905416 := by
    simpa [prefixWord, tailWord_1905416, baseEnd_1905416] using wordTrace_append hprefix tailTrace_1905416
  have hstable : (prefixWord ++ tailWord_1905416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905416).length < 2 ^ (prefixWord ++ tailWord_1905416).sum := by decide
  have hdescent : baseEnd_1905416 < baseStart_1905416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905457 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 6]
def baseStart_1905457 : Nat := 118140960795 + 1905457 * 2 ^ 59
def prefixEnd_1905457 : Nat := 4983230072969 + 3 ^ 40 * 1905457 * 2
def baseEnd_1905457 : Nat := 217425623883168138760993

theorem tailTrace_1905457 : CollatzResearch.WordTrace tailWord_1905457 prefixEnd_1905457 217425623883168138760993 := by
  unfold tailWord_1905457
  simp only [CollatzResearch.WordTrace]
  refine ⟨69497726257862189992210625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46331817505241459994807083 69497726257862189992210625)
  ·
    refine ⟨52123294693396642494157969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69497726257862189992210625 52123294693396642494157969)
    ·
      refine ⟨39092471020047481870618477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52123294693396642494157969 39092471020047481870618477)
      ·
        refine ⟨14659676632517805701481929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39092471020047481870618477 14659676632517805701481929)
        ·
          refine ⟨10994757474388354276111447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659676632517805701481929 10994757474388354276111447)
          ·
            refine ⟨16492136211582531414167171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994757474388354276111447 16492136211582531414167171)
            ·
              refine ⟨24738204317373797121250757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16492136211582531414167171 24738204317373797121250757)
              ·
                refine ⟨4638413309507586960234517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24738204317373797121250757 4638413309507586960234517)
                ·
                  refine ⟨217425623883168138760993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4638413309507586960234517 217425623883168138760993)
                  ·
                    rfl

theorem cell22_1905457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_1905457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905457 prefixEnd_1905457 := by exact prefixLift 1905457
  have htrace : WordTrace (prefixWord ++ tailWord_1905457) baseStart_1905457 baseEnd_1905457 := by
    simpa [prefixWord, tailWord_1905457, baseEnd_1905457] using wordTrace_append hprefix tailTrace_1905457
  have hstable : (prefixWord ++ tailWord_1905457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905457).length < 2 ^ (prefixWord ++ tailWord_1905457).sum := by decide
  have hdescent : baseEnd_1905457 < baseStart_1905457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905459 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 1, 4]
def baseStart_1905459 : Nat := 118140960795 + 1905459 * 2 ^ 59
def prefixEnd_1905459 : Nat := 4983230072969 + 3 ^ 40 * 1905459 * 2
def baseEnd_1905459 : Nat := 652277556290377077732973

theorem tailTrace_1905459 : CollatzResearch.WordTrace tailWord_1905459 prefixEnd_1905459 652277556290377077732973 := by
  unfold tailWord_1905459
  simp only [CollatzResearch.WordTrace]
  refine ⟨69497799203854944333783431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46331866135903296222522287 69497799203854944333783431)
  ·
    refine ⟨104246698805782416500675147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69497799203854944333783431 104246698805782416500675147)
    ·
      refine ⟨156370048208673624751012721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104246698805782416500675147 156370048208673624751012721)
      ·
        refine ⟨117277536156505218563259541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156370048208673624751012721 117277536156505218563259541)
        ·
          refine ⟨5497384507336182120152791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117277536156505218563259541 5497384507336182120152791)
          ·
            refine ⟨8246076761004273180229187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497384507336182120152791 8246076761004273180229187)
            ·
              refine ⟨12369115141506409770343781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246076761004273180229187 12369115141506409770343781)
              ·
                refine ⟨2319209089032451831939459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12369115141506409770343781 2319209089032451831939459)
                ·
                  refine ⟨3478813633548677747909189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319209089032451831939459 3478813633548677747909189)
                  ·
                    refine ⟨652277556290377077732973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478813633548677747909189 652277556290377077732973)
                    ·
                      rfl

theorem cell22_1905459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_1905459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905459 prefixEnd_1905459 := by exact prefixLift 1905459
  have htrace : WordTrace (prefixWord ++ tailWord_1905459) baseStart_1905459 baseEnd_1905459 := by
    simpa [prefixWord, tailWord_1905459, baseEnd_1905459] using wordTrace_append hprefix tailTrace_1905459
  have hstable : (prefixWord ++ tailWord_1905459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905459).length < 2 ^ (prefixWord ++ tailWord_1905459).sum := by decide
  have hdescent : baseEnd_1905459 < baseStart_1905459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905472 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_1905472 : Nat := 118140960795 + 1905472 * 2 ^ 59
def prefixEnd_1905472 : Nat := 4983230072969 + 3 ^ 40 * 1905472 * 2
def baseEnd_1905472 : Nat := 652282006456049377157933

theorem tailTrace_1905472 : CollatzResearch.WordTrace tailWord_1905472 prefixEnd_1905472 652282006456049377157933 := by
  unfold tailWord_1905472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34749136676403923777003335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46332182235205231702671113 34749136676403923777003335)
  ·
    refine ⟨52123705014605885665505003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34749136676403923777003335 52123705014605885665505003)
    ·
      refine ⟨78185557521908828498257505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52123705014605885665505003 78185557521908828498257505)
      ·
        refine ⟨58639168141431621373693129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78185557521908828498257505 58639168141431621373693129)
        ·
          refine ⟨43979376106073716030269847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58639168141431621373693129 43979376106073716030269847)
          ·
            refine ⟨65969064159110574045404771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43979376106073716030269847 65969064159110574045404771)
            ·
              refine ⟨98953596238665861068107157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65969064159110574045404771 98953596238665861068107157)
              ·
                refine ⟨4638449823687462237567523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98953596238665861068107157 4638449823687462237567523)
                ·
                  refine ⟨6957674735531193356351285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638449823687462237567523 6957674735531193356351285)
                  ·
                    refine ⟨652282006456049377157933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6957674735531193356351285 652282006456049377157933)
                    ·
                      rfl

theorem cell22_1905472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_1905472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905472 prefixEnd_1905472 := by exact prefixLift 1905472
  have htrace : WordTrace (prefixWord ++ tailWord_1905472) baseStart_1905472 baseEnd_1905472 := by
    simpa [prefixWord, tailWord_1905472, baseEnd_1905472] using wordTrace_append hprefix tailTrace_1905472
  have hstable : (prefixWord ++ tailWord_1905472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905472).length < 2 ^ (prefixWord ++ tailWord_1905472).sum := by decide
  have hdescent : baseEnd_1905472 < baseStart_1905472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905532 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1905532 : Nat := 118140960795 + 1905532 * 2 ^ 59
def prefixEnd_1905532 : Nat := 4983230072969 + 3 ^ 40 * 1905532 * 2
def baseEnd_1905532 : Nat := 652302545682229220657749

theorem tailTrace_1905532 : CollatzResearch.WordTrace tailWord_1905532 prefixEnd_1905532 652302545682229220657749 := by
  unfold tailWord_1905532
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750230866295238900595425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46333641155060318534127233 34750230866295238900595425)
  ·
    refine ⟨26062673149721429175446569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34750230866295238900595425 26062673149721429175446569)
    ·
      refine ⟨19547004862291071881584927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26062673149721429175446569 19547004862291071881584927)
      ·
        refine ⟨29320507293436607822377391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19547004862291071881584927 29320507293436607822377391)
        ·
          refine ⟨43980760940154911733566087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29320507293436607822377391 43980760940154911733566087)
          ·
            refine ⟨65971141410232367600349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43980760940154911733566087 65971141410232367600349131)
            ·
              refine ⟨98956712115348551400523697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65971141410232367600349131 98956712115348551400523697)
              ·
                refine ⟨74217534086511413550392773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98956712115348551400523697 74217534086511413550392773)
                ·
                  refine ⟨13915787641220890040698645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74217534086511413550392773 13915787641220890040698645)
                  ·
                    refine ⟨652302545682229220657749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13915787641220890040698645 652302545682229220657749)
                    ·
                      rfl

theorem cell22_1905532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1905532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905532 prefixEnd_1905532 := by exact prefixLift 1905532
  have htrace : WordTrace (prefixWord ++ tailWord_1905532) baseStart_1905532 baseEnd_1905532 := by
    simpa [prefixWord, tailWord_1905532, baseEnd_1905532] using wordTrace_append hprefix tailTrace_1905532
  have hstable : (prefixWord ++ tailWord_1905532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905532).length < 2 ^ (prefixWord ++ tailWord_1905532).sum := by decide
  have hdescent : baseEnd_1905532 < baseStart_1905532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905547 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 7]
def baseStart_1905547 : Nat := 118140960795 + 1905547 * 2 ^ 59
def prefixEnd_1905547 : Nat := 4983230072969 + 3 ^ 40 * 1905547 * 2
def baseEnd_1905547 : Nat := 217435893496258060510901

theorem tailTrace_1905547 : CollatzResearch.WordTrace tailWord_1905547 prefixEnd_1905547 217435893496258060510901 := by
  unfold tailWord_1905547
  simp only [CollatzResearch.WordTrace]
  refine ⟨69501008827536135362986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46334005885024090241991263 69501008827536135362986895)
  ·
    refine ⟨104251513241304203044480343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69501008827536135362986895 104251513241304203044480343)
    ·
      refine ⟨156377269861956304566720515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104251513241304203044480343 156377269861956304566720515)
      ·
        refine ⟨234565904792934456850080773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156377269861956304566720515 234565904792934456850080773)
        ·
          refine ⟨43981107148675210659390145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234565904792934456850080773 43981107148675210659390145)
          ·
            refine ⟨32985830361506407994542609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43981107148675210659390145 32985830361506407994542609)
            ·
              refine ⟨24739372771129805995906957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32985830361506407994542609 24739372771129805995906957)
              ·
                refine ⟨9277264789173677248465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24739372771129805995906957 9277264789173677248465109)
                ·
                  refine ⟨217435893496258060510901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9277264789173677248465109 217435893496258060510901)
                  ·
                    rfl

theorem cell22_1905547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_1905547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905547 prefixEnd_1905547 := by exact prefixLift 1905547
  have htrace : WordTrace (prefixWord ++ tailWord_1905547) baseStart_1905547 baseEnd_1905547 := by
    simpa [prefixWord, tailWord_1905547, baseEnd_1905547] using wordTrace_append hprefix tailTrace_1905547
  have hstable : (prefixWord ++ tailWord_1905547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905547).length < 2 ^ (prefixWord ++ tailWord_1905547).sum := by decide
  have hdescent : baseEnd_1905547 < baseStart_1905547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905585 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_1905585 : Nat := 118140960795 + 1905585 * 2 ^ 59
def prefixEnd_1905585 : Nat := 4983230072969 + 3 ^ 40 * 1905585 * 2
def baseEnd_1905585 : Nat := 652320688665354749082587

theorem tailTrace_1905585 : CollatzResearch.WordTrace tailWord_1905585 prefixEnd_1905585 652320688665354749082587 := by
  unfold tailWord_1905585
  simp only [CollatzResearch.WordTrace]
  refine ⟨69502394801398467852870209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46334929867598978568580139 69502394801398467852870209)
  ·
    refine ⟨52126796101048850889652657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69502394801398467852870209 52126796101048850889652657)
    ·
      refine ⟨39095097075786638167239493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52126796101048850889652657 39095097075786638167239493)
      ·
        refine ⟨7330330701709994656357405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39095097075786638167239493 7330330701709994656357405)
        ·
          refine ⟨2748874013141247996134027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7330330701709994656357405 2748874013141247996134027)
          ·
            refine ⟨4123311019711871994201041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748874013141247996134027 4123311019711871994201041)
            ·
              refine ⟨3092483264783903995650781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123311019711871994201041 3092483264783903995650781)
              ·
                refine ⟨1159681224293963998369043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092483264783903995650781 1159681224293963998369043)
                ·
                  refine ⟨1739521836440945997553565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159681224293963998369043 1739521836440945997553565)
                  ·
                    refine ⟨652320688665354749082587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739521836440945997553565 652320688665354749082587)
                    ·
                      rfl

theorem cell22_1905585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_1905585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905585 prefixEnd_1905585 := by exact prefixLift 1905585
  have htrace : WordTrace (prefixWord ++ tailWord_1905585) baseStart_1905585 baseEnd_1905585 := by
    simpa [prefixWord, tailWord_1905585, baseEnd_1905585] using wordTrace_append hprefix tailTrace_1905585
  have hstable : (prefixWord ++ tailWord_1905585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905585).length < 2 ^ (prefixWord ++ tailWord_1905585).sum := by decide
  have hdescent : baseEnd_1905585 < baseStart_1905585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905675 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 2, 3]
def baseStart_1905675 : Nat := 118140960795 + 1905675 * 2 ^ 59
def prefixEnd_1905675 : Nat := 4983230072969 + 3 ^ 40 * 1905675 * 2
def baseEnd_1905675 : Nat := 652351497504624514332311

theorem tailTrace_1905675 : CollatzResearch.WordTrace tailWord_1905675 prefixEnd_1905675 652351497504624514332311 := by
  unfold tailWord_1905675
  simp only [CollatzResearch.WordTrace]
  refine ⟨69505677371072413223646479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46337118247381608815764319 69505677371072413223646479)
  ·
    refine ⟨104258516056608619835469719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69505677371072413223646479 104258516056608619835469719)
    ·
      refine ⟨156387774084912929753204579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104258516056608619835469719 156387774084912929753204579)
      ·
        refine ⟨234581661127369394629806869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156387774084912929753204579 234581661127369394629806869)
        ·
          refine ⟨10996015365345440373272197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234581661127369394629806869 10996015365345440373272197)
          ·
            refine ⟨2061752881002270069988537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10996015365345440373272197 2061752881002270069988537)
            ·
              refine ⟨1546314660751702552491403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061752881002270069988537 1546314660751702552491403)
              ·
                refine ⟨2319471991127553828737105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546314660751702552491403 2319471991127553828737105)
                ·
                  refine ⟨1739603993345665371552829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319471991127553828737105 1739603993345665371552829)
                  ·
                    refine ⟨652351497504624514332311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739603993345665371552829 652351497504624514332311)
                    ·
                      rfl

theorem cell22_1905675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 3].length) (baseStart_1905675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905675 prefixEnd_1905675 := by exact prefixLift 1905675
  have htrace : WordTrace (prefixWord ++ tailWord_1905675) baseStart_1905675 baseEnd_1905675 := by
    simpa [prefixWord, tailWord_1905675, baseEnd_1905675] using wordTrace_append hprefix tailTrace_1905675
  have hstable : (prefixWord ++ tailWord_1905675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905675).length < 2 ^ (prefixWord ++ tailWord_1905675).sum := by decide
  have hdescent : baseEnd_1905675 < baseStart_1905675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905720 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_1905720 : Nat := 118140960795 + 1905720 * 2 ^ 59
def prefixEnd_1905720 : Nat := 4983230072969 + 3 ^ 40 * 1905720 * 2
def baseEnd_1905720 : Nat := 652366901924259396957173

theorem tailTrace_1905720 : CollatzResearch.WordTrace tailWord_1905720 prefixEnd_1905720 652366901924259396957173 := by
  unfold tailWord_1905720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34753659327954692954517307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46338212437272923939356409 34753659327954692954517307)
  ·
    refine ⟨52130488991932039431775961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34753659327954692954517307 52130488991932039431775961)
    ·
      refine ⟨39097866743949029573831971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52130488991932039431775961 39097866743949029573831971)
      ·
        refine ⟨58646800115923544360747957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39097866743949029573831971 58646800115923544360747957)
        ·
          refine ⟨5498137510867832283820121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58646800115923544360747957 5498137510867832283820121)
          ·
            refine ⟨4123603133150874212865091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5498137510867832283820121 4123603133150874212865091)
            ·
              refine ⟨6185404699726311319297637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123603133150874212865091 6185404699726311319297637)
              ·
                refine ⟨1159763381198683372368307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6185404699726311319297637 1159763381198683372368307)
                ·
                  refine ⟨1739645071798025058552461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159763381198683372368307 1739645071798025058552461)
                  ·
                    refine ⟨652366901924259396957173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739645071798025058552461 652366901924259396957173)
                    ·
                      rfl

theorem cell22_1905720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_1905720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905720 prefixEnd_1905720 := by exact prefixLift 1905720
  have htrace : WordTrace (prefixWord ++ tailWord_1905720) baseStart_1905720 baseEnd_1905720 := by
    simpa [prefixWord, tailWord_1905720, baseEnd_1905720] using wordTrace_append hprefix tailTrace_1905720
  have hstable : (prefixWord ++ tailWord_1905720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905720).length < 2 ^ (prefixWord ++ tailWord_1905720).sum := by decide
  have hdescent : baseEnd_1905720 < baseStart_1905720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905778 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1905778 : Nat := 118140960795 + 1905778 * 2 ^ 59
def prefixEnd_1905778 : Nat := 4983230072969 + 3 ^ 40 * 1905778 * 2
def baseEnd_1905778 : Nat := 217462252169855526335665

theorem tailTrace_1905778 : CollatzResearch.WordTrace tailWord_1905778 prefixEnd_1905778 217462252169855526335665 := by
  unfold tailWord_1905778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377358522424815453661497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46339622726466174543097325 17377358522424815453661497)
  ·
    refine ⟨13033018891818611590246123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17377358522424815453661497 13033018891818611590246123)
    ·
      refine ⟨19549528337727917385369185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13033018891818611590246123 19549528337727917385369185)
      ·
        refine ⟨14662146253295938039026889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19549528337727917385369185 14662146253295938039026889)
        ·
          refine ⟨10996609689971953529270167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14662146253295938039026889 10996609689971953529270167)
          ·
            refine ⟨16494914534957930293905251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996609689971953529270167 16494914534957930293905251)
            ·
              refine ⟨24742371802436895440857877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16494914534957930293905251 24742371802436895440857877)
              ·
                refine ⟨1159798678239229473790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24742371802436895440857877 1159798678239229473790213)
                ·
                  refine ⟨217462252169855526335665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159798678239229473790213 217462252169855526335665)
                  ·
                    rfl

theorem cell22_1905778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1905778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905778 prefixEnd_1905778 := by exact prefixLift 1905778
  have htrace : WordTrace (prefixWord ++ tailWord_1905778) baseStart_1905778 baseEnd_1905778 := by
    simpa [prefixWord, tailWord_1905778, baseEnd_1905778] using wordTrace_append hprefix tailTrace_1905778
  have hstable : (prefixWord ++ tailWord_1905778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905778).length < 2 ^ (prefixWord ++ tailWord_1905778).sum := by decide
  have hdescent : baseEnd_1905778 < baseStart_1905778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905793 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1905793 : Nat := 118140960795 + 1905793 * 2 ^ 59
def prefixEnd_1905793 : Nat := 4983230072969 + 3 ^ 40 * 1905793 * 2
def baseEnd_1905793 : Nat := 652391891316111539881949

theorem tailTrace_1905793 : CollatzResearch.WordTrace tailWord_1905793 prefixEnd_1905793 652391891316111539881949 := by
  unfold tailWord_1905793
  simp only [CollatzResearch.WordTrace]
  refine ⟨69509981184644919376442033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46339987456429946250961355 69509981184644919376442033)
  ·
    refine ⟨52132485888483689532331525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69509981184644919376442033 52132485888483689532331525)
    ·
      refine ⟨9774841104090691787312161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52132485888483689532331525 9774841104090691787312161)
      ·
        refine ⟨7331130828068018840484121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9774841104090691787312161 7331130828068018840484121)
        ·
          refine ⟨5498348121051014130363091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7331130828068018840484121 5498348121051014130363091)
          ·
            refine ⟨8247522181576521195544637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498348121051014130363091 8247522181576521195544637)
            ·
              refine ⟨3092820818091195448329239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8247522181576521195544637 3092820818091195448329239)
              ·
                refine ⟨4639231227136793172493859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092820818091195448329239 4639231227136793172493859)
                ·
                  refine ⟨6958846840705189758740789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639231227136793172493859 6958846840705189758740789)
                  ·
                    refine ⟨652391891316111539881949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6958846840705189758740789 652391891316111539881949)
                    ·
                      rfl

theorem cell22_1905793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1905793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905793 prefixEnd_1905793 := by exact prefixLift 1905793
  have htrace : WordTrace (prefixWord ++ tailWord_1905793) baseStart_1905793 baseEnd_1905793 := by
    simpa [prefixWord, tailWord_1905793, baseEnd_1905793] using wordTrace_append hprefix tailTrace_1905793
  have hstable : (prefixWord ++ tailWord_1905793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905793).length < 2 ^ (prefixWord ++ tailWord_1905793).sum := by decide
  have hdescent : baseEnd_1905793 < baseStart_1905793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905823 : List Nat := [1, 1, 2, 6, 2, 2, 8]
def baseStart_1905823 : Nat := 118140960795 + 1905823 * 2 ^ 59
def prefixEnd_1905823 : Nat := 4983230072969 + 3 ^ 40 * 1905823 * 2
def baseEnd_1905823 : Nat := 24163042997377831912291

theorem tailTrace_1905823 : CollatzResearch.WordTrace tailWord_1905823 prefixEnd_1905823 24163042997377831912291 := by
  unfold tailWord_1905823
  simp only [CollatzResearch.WordTrace]
  refine ⟨69511075374536234500034123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46340716916357489666689415 69511075374536234500034123)
  ·
    refine ⟨104266613061804351750051185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69511075374536234500034123 104266613061804351750051185)
    ·
      refine ⟨78199959796353263812538389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104266613061804351750051185 78199959796353263812538389)
      ·
        refine ⟨3665623115454059241212737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78199959796353263812538389 3665623115454059241212737)
        ·
          refine ⟨2749217336590544430909553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3665623115454059241212737 2749217336590544430909553)
          ·
            refine ⟨2061913002442908323182165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749217336590544430909553 2061913002442908323182165)
            ·
              refine ⟨24163042997377831912291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2061913002442908323182165 24163042997377831912291)
              ·
                rfl

theorem cell22_1905823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 8].length) (baseStart_1905823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905823 prefixEnd_1905823 := by exact prefixLift 1905823
  have htrace : WordTrace (prefixWord ++ tailWord_1905823) baseStart_1905823 baseEnd_1905823 := by
    simpa [prefixWord, tailWord_1905823, baseEnd_1905823] using wordTrace_append hprefix tailTrace_1905823
  have hstable : (prefixWord ++ tailWord_1905823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905823).length < 2 ^ (prefixWord ++ tailWord_1905823).sum := by decide
  have hdescent : baseEnd_1905823 < baseStart_1905823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905889 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1905889 : Nat := 118140960795 + 1905889 * 2 ^ 59
def prefixEnd_1905889 : Nat := 4983230072969 + 3 ^ 40 * 1905889 * 2
def baseEnd_1905889 : Nat := 652424754077999289481655

theorem tailTrace_1905889 : CollatzResearch.WordTrace tailWord_1905889 prefixEnd_1905889 652424754077999289481655 := by
  unfold tailWord_1905889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69513482592297127771936721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46342321728198085181291147 69513482592297127771936721)
  ·
    refine ⟨52135111944222845828952541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69513482592297127771936721 52135111944222845828952541)
    ·
      refine ⟨19550666979083567185857203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52135111944222845828952541 19550666979083567185857203)
      ·
        refine ⟨29326000468625350778785805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19550666979083567185857203 29326000468625350778785805)
        ·
          refine ⟨10997250175734506542044677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29326000468625350778785805 10997250175734506542044677)
          ·
            refine ⟨2061984407950219976633377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10997250175734506542044677 2061984407950219976633377)
            ·
              refine ⟨1546488305962664982475033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061984407950219976633377 1546488305962664982475033)
              ·
                refine ⟨1159866229471998736856275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546488305962664982475033 1159866229471998736856275)
                ·
                  refine ⟨1739799344207998105284413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159866229471998736856275 1739799344207998105284413)
                  ·
                    refine ⟨652424754077999289481655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739799344207998105284413 652424754077999289481655)
                    ·
                      rfl

theorem cell22_1905889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1905889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905889 prefixEnd_1905889 := by exact prefixLift 1905889
  have htrace : WordTrace (prefixWord ++ tailWord_1905889) baseStart_1905889 baseEnd_1905889 := by
    simpa [prefixWord, tailWord_1905889, baseEnd_1905889] using wordTrace_append hprefix tailTrace_1905889
  have hstable : (prefixWord ++ tailWord_1905889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905889).length < 2 ^ (prefixWord ++ tailWord_1905889).sum := by decide
  have hdescent : baseEnd_1905889 < baseStart_1905889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905898 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1905898 : Nat := 118140960795 + 1905898 * 2 ^ 59
def prefixEnd_1905898 : Nat := 4983230072969 + 3 ^ 40 * 1905898 * 2
def baseEnd_1905898 : Nat := 652427834961926266006627

theorem tailTrace_1905898 : CollatzResearch.WordTrace tailWord_1905898 prefixEnd_1905898 652427834961926266006627 := by
  unfold tailWord_1905898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17378452712316130577253587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46342540566176348206009565 17378452712316130577253587)
  ·
    refine ⟨26067679068474195865880381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17378452712316130577253587 26067679068474195865880381)
    ·
      refine ⟨9775379650677823449705143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26067679068474195865880381 9775379650677823449705143)
      ·
        refine ⟨14663069476016735174557715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9775379650677823449705143 14663069476016735174557715)
        ·
          refine ⟨21994604214025102761836573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663069476016735174557715 21994604214025102761836573)
          ·
            refine ⟨8247976580259413535688715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21994604214025102761836573 8247976580259413535688715)
            ·
              refine ⟨12371964870389120303533073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247976580259413535688715 12371964870389120303533073)
              ·
                refine ⟨9278973652791840227649805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371964870389120303533073 9278973652791840227649805)
                ·
                  refine ⟨3479615119796940085368677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9278973652791840227649805 3479615119796940085368677)
                  ·
                    refine ⟨652427834961926266006627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479615119796940085368677 652427834961926266006627)
                    ·
                      rfl

theorem cell22_1905898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1905898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905898 prefixEnd_1905898 := by exact prefixLift 1905898
  have htrace : WordTrace (prefixWord ++ tailWord_1905898) baseStart_1905898 baseEnd_1905898 := by
    simpa [prefixWord, tailWord_1905898, baseEnd_1905898] using wordTrace_append hprefix tailTrace_1905898
  have hstable : (prefixWord ++ tailWord_1905898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905898).length < 2 ^ (prefixWord ++ tailWord_1905898).sum := by decide
  have hdescent : baseEnd_1905898 < baseStart_1905898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905911 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1905911 : Nat := 118140960795 + 1905911 * 2 ^ 59
def prefixEnd_1905911 : Nat := 4983230072969 + 3 ^ 40 * 1905911 * 2
def baseEnd_1905911 : Nat := 652432285127598565431587

theorem tailTrace_1905911 : CollatzResearch.WordTrace tailWord_1905911 prefixEnd_1905911 652432285127598565431587 := by
  unfold tailWord_1905911
  simp only [CollatzResearch.WordTrace]
  refine ⟨69514284998217425529237587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46342856665478283686158391 69514284998217425529237587)
  ·
    refine ⟨104271427497326138293856381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69514284998217425529237587 104271427497326138293856381)
    ·
      refine ⟨39101785311497301860196143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104271427497326138293856381 39101785311497301860196143)
      ·
        refine ⟨58652677967245952790294215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39101785311497301860196143 58652677967245952790294215)
        ·
          refine ⟨87979016950868929185441323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58652677967245952790294215 87979016950868929185441323)
          ·
            refine ⟨131968525426303393778161985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87979016950868929185441323 131968525426303393778161985)
            ·
              refine ⟨98976394069727545333621489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131968525426303393778161985 98976394069727545333621489)
              ·
                refine ⟨74232295552295659000216117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98976394069727545333621489 74232295552295659000216117)
                ·
                  refine ⟨6959277708027718031270261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74232295552295659000216117 6959277708027718031270261)
                  ·
                    refine ⟨652432285127598565431587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6959277708027718031270261 652432285127598565431587)
                    ·
                      rfl

theorem cell22_1905911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1905911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905911 prefixEnd_1905911 := by exact prefixLift 1905911
  have htrace : WordTrace (prefixWord ++ tailWord_1905911) baseStart_1905911 baseEnd_1905911 := by
    simpa [prefixWord, tailWord_1905911, baseEnd_1905911] using wordTrace_append hprefix tailTrace_1905911
  have hstable : (prefixWord ++ tailWord_1905911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905911).length < 2 ^ (prefixWord ++ tailWord_1905911).sum := by decide
  have hdescent : baseEnd_1905911 < baseStart_1905911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905932 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_1905932 : Nat := 118140960795 + 1905932 * 2 ^ 59
def prefixEnd_1905932 : Nat := 4983230072969 + 3 ^ 40 * 1905932 * 2
def baseEnd_1905932 : Nat := 652439473856761510656523

theorem tailTrace_1905932 : CollatzResearch.WordTrace tailWord_1905932 prefixEnd_1905932 652439473856761510656523 := by
  unfold tailWord_1905932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34757525465570673057876025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46343367287427564077168033 34757525465570673057876025)
  ·
    refine ⟨26068144099178004793407019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34757525465570673057876025 26068144099178004793407019)
    ·
      refine ⟨39102216148767007190110529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26068144099178004793407019 39102216148767007190110529)
      ·
        refine ⟨29326662111575255392582897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39102216148767007190110529 29326662111575255392582897)
        ·
          refine ⟨21994996583681441544437173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29326662111575255392582897 21994996583681441544437173)
          ·
            refine ⟨2062030929720135144790985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21994996583681441544437173 2062030929720135144790985)
            ·
              refine ⟨1546523197290101358593239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062030929720135144790985 1546523197290101358593239)
              ·
                refine ⟨2319784795935152037889859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546523197290101358593239 2319784795935152037889859)
                ·
                  refine ⟨3479677193902728056834789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319784795935152037889859 3479677193902728056834789)
                  ·
                    refine ⟨652439473856761510656523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479677193902728056834789 652439473856761510656523)
                    ·
                      rfl

theorem cell22_1905932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_1905932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905932 prefixEnd_1905932 := by exact prefixLift 1905932
  have htrace : WordTrace (prefixWord ++ tailWord_1905932) baseStart_1905932 baseEnd_1905932 := by
    simpa [prefixWord, tailWord_1905932, baseEnd_1905932] using wordTrace_append hprefix tailTrace_1905932
  have hstable : (prefixWord ++ tailWord_1905932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905932).length < 2 ^ (prefixWord ++ tailWord_1905932).sum := by decide
  have hdescent : baseEnd_1905932 < baseStart_1905932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905943 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1905943 : Nat := 118140960795 + 1905943 * 2 ^ 59
def prefixEnd_1905943 : Nat := 4983230072969 + 3 ^ 40 * 1905943 * 2
def baseEnd_1905943 : Nat := 652443239381561148631489

theorem tailTrace_1905943 : CollatzResearch.WordTrace tailWord_1905943 prefixEnd_1905943 652443239381561148631489 := by
  unfold tailWord_1905943
  simp only [CollatzResearch.WordTrace]
  refine ⟨69515452134101494994402483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46343634756067663329601655 69515452134101494994402483)
  ·
    refine ⟨104273178201152242491603725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69515452134101494994402483 104273178201152242491603725)
    ·
      refine ⟨39102441825432090934351397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104273178201152242491603725 39102441825432090934351397)
      ·
        refine ⟨7331707842268517050190887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39102441825432090934351397 7331707842268517050190887)
        ·
          refine ⟨10997561763402775575286331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331707842268517050190887 10997561763402775575286331)
          ·
            refine ⟨16496342645104163362929497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997561763402775575286331 16496342645104163362929497)
            ·
              refine ⟨12372256983828122522197123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496342645104163362929497 12372256983828122522197123)
              ·
                refine ⟨18558385475742183783295685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372256983828122522197123 18558385475742183783295685)
                ·
                  refine ⟨3479697276701659459367941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18558385475742183783295685 3479697276701659459367941)
                  ·
                    refine ⟨652443239381561148631489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479697276701659459367941 652443239381561148631489)
                    ·
                      rfl

theorem cell22_1905943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1905943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905943 prefixEnd_1905943 := by exact prefixLift 1905943
  have htrace : WordTrace (prefixWord ++ tailWord_1905943) baseStart_1905943 baseEnd_1905943 := by
    simpa [prefixWord, tailWord_1905943, baseEnd_1905943] using wordTrace_append hprefix tailTrace_1905943
  have hstable : (prefixWord ++ tailWord_1905943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905943).length < 2 ^ (prefixWord ++ tailWord_1905943).sum := by decide
  have hdescent : baseEnd_1905943 < baseStart_1905943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905962 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1905962 : Nat := 118140960795 + 1905962 * 2 ^ 59
def prefixEnd_1905962 : Nat := 4983230072969 + 3 ^ 40 * 1905962 * 2
def baseEnd_1905962 : Nat := 652449743469851432406431

theorem tailTrace_1905962 : CollatzResearch.WordTrace tailWord_1905962 prefixEnd_1905962 652449743469851432406431 := by
  unfold tailWord_1905962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379036280258165309836035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46344096747355107492896093 17379036280258165309836035)
  ·
    refine ⟨26068554420387247964754053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17379036280258165309836035 26068554420387247964754053)
    ·
      refine ⟨4887853953822608993391385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26068554420387247964754053 4887853953822608993391385)
      ·
        refine ⟨3665890465366956745043539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4887853953822608993391385 3665890465366956745043539)
        ·
          refine ⟨5498835698050435117565309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665890465366956745043539 5498835698050435117565309)
          ·
            refine ⟨2062063386768913169086991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5498835698050435117565309 2062063386768913169086991)
            ·
              refine ⟨3093095080153369753630487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062063386768913169086991 3093095080153369753630487)
              ·
                refine ⟨4639642620230054630445731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093095080153369753630487 4639642620230054630445731)
                ·
                  refine ⟨6959463930345081945668597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639642620230054630445731 6959463930345081945668597)
                  ·
                    refine ⟨652449743469851432406431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6959463930345081945668597 652449743469851432406431)
                    ·
                      rfl

theorem cell22_1905962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1905962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905962 prefixEnd_1905962 := by exact prefixLift 1905962
  have htrace : WordTrace (prefixWord ++ tailWord_1905962) baseStart_1905962 baseEnd_1905962 := by
    simpa [prefixWord, tailWord_1905962, baseEnd_1905962] using wordTrace_append hprefix tailTrace_1905962
  have hstable : (prefixWord ++ tailWord_1905962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905962).length < 2 ^ (prefixWord ++ tailWord_1905962).sum := by decide
  have hdescent : baseEnd_1905962 < baseStart_1905962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1905981 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 4]
def baseStart_1905981 : Nat := 118140960795 + 1905981 * 2 ^ 59
def prefixEnd_1905981 : Nat := 4983230072969 + 3 ^ 40 * 1905981 * 2
def baseEnd_1905981 : Nat := 217485415852713905393791

theorem tailTrace_1905981 : CollatzResearch.WordTrace tailWord_1905981 prefixEnd_1905981 217485415852713905393791 := by
  unfold tailWord_1905981
  simp only [CollatzResearch.WordTrace]
  refine ⟨69516838107963827484285797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46344558738642551656190531 69516838107963827484285797)
  ·
    refine ⟨13034407145243217653303587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69516838107963827484285797 13034407145243217653303587)
    ·
      refine ⟨19551610717864826479955381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13034407145243217653303587 19551610717864826479955381)
      ·
        refine ⟨1832963504799827482495817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19551610717864826479955381 1832963504799827482495817)
        ·
          refine ⟨1374722628599870611871863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1832963504799827482495817 1374722628599870611871863)
          ·
            refine ⟨2062083942899805917807795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374722628599870611871863 2062083942899805917807795)
            ·
              refine ⟨3093125914349708876711693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062083942899805917807795 3093125914349708876711693)
              ·
                refine ⟨1159922217881140828766885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093125914349708876711693 1159922217881140828766885)
                ·
                  refine ⟨217485415852713905393791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159922217881140828766885 217485415852713905393791)
                  ·
                    rfl

theorem cell22_1905981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_1905981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1905981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1905981 prefixEnd_1905981 := by exact prefixLift 1905981
  have htrace : WordTrace (prefixWord ++ tailWord_1905981) baseStart_1905981 baseEnd_1905981 := by
    simpa [prefixWord, tailWord_1905981, baseEnd_1905981] using wordTrace_append hprefix tailTrace_1905981
  have hstable : (prefixWord ++ tailWord_1905981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1905981).length < 2 ^ (prefixWord ++ tailWord_1905981).sum := by decide
  have hdescent : baseEnd_1905981 < baseStart_1905981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1905981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906003 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 5]
def baseStart_1906003 : Nat := 118140960795 + 1906003 * 2 ^ 59
def prefixEnd_1906003 : Nat := 4983230072969 + 3 ^ 40 * 1906003 * 2
def baseEnd_1906003 : Nat := 217487926202580330710435

theorem tailTrace_1906003 : CollatzResearch.WordTrace tailWord_1906003 prefixEnd_1906003 217487926202580330710435 := by
  unfold tailWord_1906003
  simp only [CollatzResearch.WordTrace]
  refine ⟨69517640513884125241586663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46345093675922750161057775 69517640513884125241586663)
  ·
    refine ⟨104276460770826187862379995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69517640513884125241586663 104276460770826187862379995)
    ·
      refine ⟨156414691156239281793569993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104276460770826187862379995 156414691156239281793569993)
      ·
        refine ⟨117311018367179461345177495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156414691156239281793569993 117311018367179461345177495)
        ·
          refine ⟨175966527550769192017766243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117311018367179461345177495 175966527550769192017766243)
          ·
            refine ⟨263949791326153788026649365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175966527550769192017766243 263949791326153788026649365)
            ·
              refine ⟨12372646468413458813749189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263949791326153788026649365 12372646468413458813749189)
              ·
                refine ⟨2319871212827523527577973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12372646468413458813749189 2319871212827523527577973)
                ·
                  refine ⟨217487926202580330710435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2319871212827523527577973 217487926202580330710435)
                  ·
                    rfl

theorem cell22_1906003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].length) (baseStart_1906003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906003 prefixEnd_1906003 := by exact prefixLift 1906003
  have htrace : WordTrace (prefixWord ++ tailWord_1906003) baseStart_1906003 baseEnd_1906003 := by
    simpa [prefixWord, tailWord_1906003, baseEnd_1906003] using wordTrace_append hprefix tailTrace_1906003
  have hstable : (prefixWord ++ tailWord_1906003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906003).length < 2 ^ (prefixWord ++ tailWord_1906003).sum := by decide
  have hdescent : baseEnd_1906003 < baseStart_1906003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906007 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1906007 : Nat := 118140960795 + 1906007 * 2 ^ 59
def prefixEnd_1906007 : Nat := 4983230072969 + 3 ^ 40 * 1906007 * 2
def baseEnd_1906007 : Nat := 652465147889486315031293

theorem tailTrace_1906007 : CollatzResearch.WordTrace tailWord_1906007 prefixEnd_1906007 652465147889486315031293 := by
  unfold tailWord_1906007
  simp only [CollatzResearch.WordTrace]
  refine ⟨69517786405869633924732275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46345190937246422616488183 69517786405869633924732275)
  ·
    refine ⟨104276679608804450887098413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69517786405869633924732275 104276679608804450887098413)
    ·
      refine ⟨39103754853301669082661905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104276679608804450887098413 39103754853301669082661905)
      ·
        refine ⟨29327816139976251811996429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39103754853301669082661905 29327816139976251811996429)
        ·
          refine ⟨10997931052491094429498661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29327816139976251811996429 10997931052491094429498661)
          ·
            refine ⟨2062112072342080205530999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10997931052491094429498661 2062112072342080205530999)
            ·
              refine ⟨3093168108513120308296499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062112072342080205530999 3093168108513120308296499)
              ·
                refine ⟨4639752162769680462444749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093168108513120308296499 4639752162769680462444749)
                ·
                  refine ⟨1739907061038630173416781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4639752162769680462444749 1739907061038630173416781)
                  ·
                    refine ⟨652465147889486315031293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739907061038630173416781 652465147889486315031293)
                    ·
                      rfl

theorem cell22_1906007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1906007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906007 prefixEnd_1906007 := by exact prefixLift 1906007
  have htrace : WordTrace (prefixWord ++ tailWord_1906007) baseStart_1906007 baseEnd_1906007 := by
    simpa [prefixWord, tailWord_1906007, baseEnd_1906007] using wordTrace_append hprefix tailTrace_1906007
  have hstable : (prefixWord ++ tailWord_1906007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906007).length < 2 ^ (prefixWord ++ tailWord_1906007).sum := by decide
  have hdescent : baseEnd_1906007 < baseStart_1906007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906020 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1906020 : Nat := 118140960795 + 1906020 * 2 ^ 59
def prefixEnd_1906020 : Nat := 4983230072969 + 3 ^ 40 * 1906020 * 2
def baseEnd_1906020 : Nat := 217489866018386204818751

theorem tailTrace_1906020 : CollatzResearch.WordTrace tailWord_1906020 prefixEnd_1906020 217489866018386204818751 := by
  unfold tailWord_1906020
  simp only [CollatzResearch.WordTrace]
  refine ⟨34759130277411268572477757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46345507036548358096637009 34759130277411268572477757)
  ·
    refine ⟨13034673854029225714679159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34759130277411268572477757 13034673854029225714679159)
    ·
      refine ⟨19552010781043838572018739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13034673854029225714679159 19552010781043838572018739)
      ·
        refine ⟨29328016171565757858028109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19552010781043838572018739 29328016171565757858028109)
        ·
          refine ⟨10998006064337159196760541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29328016171565757858028109 10998006064337159196760541)
          ·
            refine ⟨4124252274126434698785203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10998006064337159196760541 4124252274126434698785203)
            ·
              refine ⟨6186378411189652048177805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124252274126434698785203 6186378411189652048177805)
              ·
                refine ⟨2319891904196119518066677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186378411189652048177805 2319891904196119518066677)
                ·
                  refine ⟨217489866018386204818751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2319891904196119518066677 217489866018386204818751)
                  ·
                    rfl

theorem cell22_1906020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1906020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906020 prefixEnd_1906020 := by exact prefixLift 1906020
  have htrace : WordTrace (prefixWord ++ tailWord_1906020) baseStart_1906020 baseEnd_1906020 := by
    simpa [prefixWord, tailWord_1906020, baseEnd_1906020] using wordTrace_append hprefix tailTrace_1906020
  have hstable : (prefixWord ++ tailWord_1906020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906020).length < 2 ^ (prefixWord ++ tailWord_1906020).sum := by decide
  have hdescent : baseEnd_1906020 < baseStart_1906020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906065 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 4]
def baseStart_1906065 : Nat := 118140960795 + 1906065 * 2 ^ 59
def prefixEnd_1906065 : Nat := 4983230072969 + 3 ^ 40 * 1906065 * 2
def baseEnd_1906065 : Nat := 217495000824931165693705

theorem tailTrace_1906065 : CollatzResearch.WordTrace tailWord_1906065 prefixEnd_1906065 217495000824931165693705 := by
  unfold tailWord_1906065
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519901839659509830343649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46346601226439673220229099 69519901839659509830343649)
  ·
    refine ⟨52139926379744632372757737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69519901839659509830343649 52139926379744632372757737)
    ·
      refine ⟨39104944784808474279568303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52139926379744632372757737 39104944784808474279568303)
      ·
        refine ⟨58657417177212711419352455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39104944784808474279568303 58657417177212711419352455)
        ·
          refine ⟨87986125765819067129028683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58657417177212711419352455 87986125765819067129028683)
          ·
            refine ⟨131979188648728600693543025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87986125765819067129028683 131979188648728600693543025)
            ·
              refine ⟨98984391486546450520157269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131979188648728600693543025 98984391486546450520157269)
              ·
                refine ⟨1159973337732966217033093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 98984391486546450520157269 1159973337732966217033093)
                ·
                  refine ⟨217495000824931165693705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159973337732966217033093 217495000824931165693705)
                  ·
                    rfl

theorem cell22_1906065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_1906065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906065 prefixEnd_1906065 := by exact prefixLift 1906065
  have htrace : WordTrace (prefixWord ++ tailWord_1906065) baseStart_1906065 baseEnd_1906065 := by
    simpa [prefixWord, tailWord_1906065, baseEnd_1906065] using wordTrace_append hprefix tailTrace_1906065
  have hstable : (prefixWord ++ tailWord_1906065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906065).length < 2 ^ (prefixWord ++ tailWord_1906065).sum := by decide
  have hdescent : baseEnd_1906065 < baseStart_1906065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906080 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_1906080 : Nat := 118140960795 + 1906080 * 2 ^ 59
def prefixEnd_1906080 : Nat := 4983230072969 + 3 ^ 40 * 1906080 * 2
def baseEnd_1906080 : Nat := 652490137281338457956069

theorem tailTrace_1906080 : CollatzResearch.WordTrace tailWord_1906080 prefixEnd_1906080 652490137281338457956069 := by
  unfold tailWord_1906080
  simp only [CollatzResearch.WordTrace]
  refine ⟨34760224467302583696069847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46346965956403444928093129 34760224467302583696069847)
  ·
    refine ⟨52140336700953875544104771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34760224467302583696069847 52140336700953875544104771)
    ·
      refine ⟨78210505051430813316157157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52140336700953875544104771 78210505051430813316157157)
      ·
        refine ⟨14664469697143277496779467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78210505051430813316157157 14664469697143277496779467)
        ·
          refine ⟨21996704545714916245169201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664469697143277496779467 21996704545714916245169201)
          ·
            refine ⟨16497528409286187183876901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21996704545714916245169201 16497528409286187183876901)
            ·
              refine ⟨3093286576741160096976919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16497528409286187183876901 3093286576741160096976919)
              ·
                refine ⟨4639929865111740145465379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093286576741160096976919 4639929865111740145465379)
                ·
                  refine ⟨6959894797667610218198069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639929865111740145465379 6959894797667610218198069)
                  ·
                    refine ⟨652490137281338457956069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6959894797667610218198069 652490137281338457956069)
                    ·
                      rfl

theorem cell22_1906080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_1906080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906080 prefixEnd_1906080 := by exact prefixLift 1906080
  have htrace : WordTrace (prefixWord ++ tailWord_1906080) baseStart_1906080 baseEnd_1906080 := by
    simpa [prefixWord, tailWord_1906080, baseEnd_1906080] using wordTrace_append hprefix tailTrace_1906080
  have hstable : (prefixWord ++ tailWord_1906080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906080).length < 2 ^ (prefixWord ++ tailWord_1906080).sum := by decide
  have hdescent : baseEnd_1906080 < baseStart_1906080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906123 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_1906123 : Nat := 118140960795 + 1906123 * 2 ^ 59
def prefixEnd_1906123 : Nat := 4983230072969 + 3 ^ 40 * 1906123 * 2
def baseEnd_1906123 : Nat := 652504857060100679130937

theorem tailTrace_1906123 : CollatzResearch.WordTrace tailWord_1906123 prefixEnd_1906123 652504857060100679130937 := by
  unfold tailWord_1906123
  simp only [CollatzResearch.WordTrace]
  refine ⟨69522017273449385735955023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46348011515632923823970015 69522017273449385735955023)
  ·
    refine ⟨104283025910174078603932535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69522017273449385735955023 104283025910174078603932535)
    ·
      refine ⟨156424538865261117905898803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104283025910174078603932535 156424538865261117905898803)
      ·
        refine ⟨234636808297891676858848205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156424538865261117905898803 234636808297891676858848205)
        ·
          refine ⟨87988803111709378822068077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234636808297891676858848205 87988803111709378822068077)
          ·
            refine ⟨32995801166891017058275529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87988803111709378822068077 32995801166891017058275529)
            ·
              refine ⟨24746850875168262793706647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32995801166891017058275529 24746850875168262793706647)
              ·
                refine ⟨37120276312752394190559971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24746850875168262793706647 37120276312752394190559971)
                ·
                  refine ⟨55680414469128591285839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37120276312752394190559971 55680414469128591285839957)
                  ·
                    refine ⟨652504857060100679130937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55680414469128591285839957 652504857060100679130937)
                    ·
                      rfl

theorem cell22_1906123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_1906123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906123 prefixEnd_1906123 := by exact prefixLift 1906123
  have htrace : WordTrace (prefixWord ++ tailWord_1906123) baseStart_1906123 baseEnd_1906123 := by
    simpa [prefixWord, tailWord_1906123, baseEnd_1906123] using wordTrace_append hprefix tailTrace_1906123
  have hstable : (prefixWord ++ tailWord_1906123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906123).length < 2 ^ (prefixWord ++ tailWord_1906123).sum := by decide
  have hdescent : baseEnd_1906123 < baseStart_1906123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906159 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 1, 3]
def baseStart_1906159 : Nat := 118140960795 + 1906159 * 2 ^ 59
def prefixEnd_1906159 : Nat := 4983230072969 + 3 ^ 40 * 1906159 * 2
def baseEnd_1906159 : Nat := 652517180595808585230827

theorem tailTrace_1906159 : CollatzResearch.WordTrace tailWord_1906159 prefixEnd_1906159 652517180595808585230827 := by
  unfold tailWord_1906159
  simp only [CollatzResearch.WordTrace]
  refine ⟨69523330301318963884265531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46348886867545975922843687 69523330301318963884265531)
  ·
    refine ⟨104284995451978445826398297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69523330301318963884265531 104284995451978445826398297)
    ·
      refine ⟨78213746588983834369798723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104284995451978445826398297 78213746588983834369798723)
      ·
        refine ⟨117320619883475751554698085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78213746588983834369798723 117320619883475751554698085)
        ·
          refine ⟨21997616228151703416505891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117320619883475751554698085 21997616228151703416505891)
          ·
            refine ⟨32996424342227555124758837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21997616228151703416505891 32996424342227555124758837)
            ·
              refine ⟨3093414782083833292946141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32996424342227555124758837 3093414782083833292946141)
              ·
                refine ⟨1160030543281437484854803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093414782083833292946141 1160030543281437484854803)
                ·
                  refine ⟨1740045814922156227282205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160030543281437484854803 1740045814922156227282205)
                  ·
                    refine ⟨652517180595808585230827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740045814922156227282205 652517180595808585230827)
                    ·
                      rfl

theorem cell22_1906159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_1906159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906159 prefixEnd_1906159 := by exact prefixLift 1906159
  have htrace : WordTrace (prefixWord ++ tailWord_1906159) baseStart_1906159 baseEnd_1906159 := by
    simpa [prefixWord, tailWord_1906159, baseEnd_1906159] using wordTrace_append hprefix tailTrace_1906159
  have hstable : (prefixWord ++ tailWord_1906159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906159).length < 2 ^ (prefixWord ++ tailWord_1906159).sum := by decide
  have hdescent : baseEnd_1906159 < baseStart_1906159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906182 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1906182 : Nat := 118140960795 + 1906182 * 2 ^ 59
def prefixEnd_1906182 : Nat := 4983230072969 + 3 ^ 40 * 1906182 * 2
def baseEnd_1906182 : Nat := 652525053965844191905757

theorem tailTrace_1906182 : CollatzResearch.WordTrace tailWord_1906182 prefixEnd_1906182 652525053965844191905757 := by
  unfold tailWord_1906182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172630286882363712886025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46349446120157092541568533 2172630286882363712886025)
  ·
    refine ⟨1629472715161772784664519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2172630286882363712886025 1629472715161772784664519)
    ·
      refine ⟨2444209072742659176996779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629472715161772784664519 2444209072742659176996779)
      ·
        refine ⟨3666313609113988765495169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444209072742659176996779 3666313609113988765495169)
        ·
          refine ⟨2749735206835491574121377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666313609113988765495169 2749735206835491574121377)
          ·
            refine ⟨2062301405126618680591033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749735206835491574121377 2062301405126618680591033)
            ·
              refine ⟨1546726053844964010443275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062301405126618680591033 1546726053844964010443275)
              ·
                refine ⟨2320089080767446015664913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546726053844964010443275 2320089080767446015664913)
                ·
                  refine ⟨1740066810575584511748685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2320089080767446015664913 1740066810575584511748685)
                  ·
                    refine ⟨652525053965844191905757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740066810575584511748685 652525053965844191905757)
                    ·
                      rfl

theorem cell22_1906182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1906182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906182 prefixEnd_1906182 := by exact prefixLift 1906182
  have htrace : WordTrace (prefixWord ++ tailWord_1906182) baseStart_1906182 baseEnd_1906182 := by
    simpa [prefixWord, tailWord_1906182, baseEnd_1906182] using wordTrace_append hprefix tailTrace_1906182
  have hstable : (prefixWord ++ tailWord_1906182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906182).length < 2 ^ (prefixWord ++ tailWord_1906182).sum := by decide
  have hdescent : baseEnd_1906182 < baseStart_1906182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906185 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_1906185 : Nat := 118140960795 + 1906185 * 2 ^ 59
def prefixEnd_1906185 : Nat := 4983230072969 + 3 ^ 40 * 1906185 * 2
def baseEnd_1906185 : Nat := 652526080927153184080747

theorem tailTrace_1906185 : CollatzResearch.WordTrace tailWord_1906185 prefixEnd_1906185 652526080927153184080747 := by
  unfold tailWord_1906185
  simp only [CollatzResearch.WordTrace]
  refine ⟨69524278599224770324712009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46349519066149846883141339 69524278599224770324712009)
  ·
    refine ⟨52143208949418577743534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69524278599224770324712009 52143208949418577743534007)
    ·
      refine ⟨78214813424127866615301011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52143208949418577743534007 78214813424127866615301011)
      ·
        refine ⟨117322220136191799922951517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78214813424127866615301011 117322220136191799922951517)
        ·
          refine ⟨43995832551071924971106819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117322220136191799922951517 43995832551071924971106819)
          ·
            refine ⟨65993748826607887456660229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43995832551071924971106819 65993748826607887456660229)
            ·
              refine ⟨12373827904988978898123793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65993748826607887456660229 12373827904988978898123793)
              ·
                refine ⟨9280370928741734173592845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12373827904988978898123793 9280370928741734173592845)
                ·
                  refine ⟨3480139098278150315097317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9280370928741734173592845 3480139098278150315097317)
                  ·
                    refine ⟨652526080927153184080747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480139098278150315097317 652526080927153184080747)
                    ·
                      rfl

theorem cell22_1906185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_1906185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906185 prefixEnd_1906185 := by exact prefixLift 1906185
  have htrace : WordTrace (prefixWord ++ tailWord_1906185) baseStart_1906185 baseEnd_1906185 := by
    simpa [prefixWord, tailWord_1906185, baseEnd_1906185] using wordTrace_append hprefix tailTrace_1906185
  have hstable : (prefixWord ++ tailWord_1906185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906185).length < 2 ^ (prefixWord ++ tailWord_1906185).sum := by decide
  have hdescent : baseEnd_1906185 < baseStart_1906185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906320 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_1906320 : Nat := 118140960795 + 1906320 * 2 ^ 59
def prefixEnd_1906320 : Nat := 4983230072969 + 3 ^ 40 * 1906320 * 2
def baseEnd_1906320 : Nat := 652572294186057831955333

theorem tailTrace_1906320 : CollatzResearch.WordTrace tailWord_1906320 prefixEnd_1906320 652572294186057831955333 := by
  unfold tailWord_1906320
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764601226867844190438207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46352801635823792253917609 34764601226867844190438207)
  ·
    refine ⟨52146901840301766285657311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764601226867844190438207 52146901840301766285657311)
    ·
      refine ⟨78220352760452649428485967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52146901840301766285657311 78220352760452649428485967)
      ·
        refine ⟨117330529140678974142728951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78220352760452649428485967 117330529140678974142728951)
        ·
          refine ⟨175995793711018461214093427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117330529140678974142728951 175995793711018461214093427)
          ·
            refine ⟨263993690566527691821140141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175995793711018461214093427 263993690566527691821140141)
            ·
              refine ⟨98997633962447884432927553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263993690566527691821140141 98997633962447884432927553)
              ·
                refine ⟨74248225471835913324695665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98997633962447884432927553 74248225471835913324695665)
                ·
                  refine ⟨55686169103876934993521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74248225471835913324695665 55686169103876934993521749)
                  ·
                    refine ⟨652572294186057831955333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55686169103876934993521749 652572294186057831955333)
                    ·
                      rfl

theorem cell22_1906320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_1906320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906320 prefixEnd_1906320 := by exact prefixLift 1906320
  have htrace : WordTrace (prefixWord ++ tailWord_1906320) baseStart_1906320 baseEnd_1906320 := by
    simpa [prefixWord, tailWord_1906320, baseEnd_1906320] using wordTrace_append hprefix tailTrace_1906320
  have hstable : (prefixWord ++ tailWord_1906320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906320).length < 2 ^ (prefixWord ++ tailWord_1906320).sum := by decide
  have hdescent : baseEnd_1906320 < baseStart_1906320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906328 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_1906328 : Nat := 118140960795 + 1906328 * 2 ^ 59
def prefixEnd_1906328 : Nat := 4983230072969 + 3 ^ 40 * 1906328 * 2
def baseEnd_1906328 : Nat := 652575032749548477755309

theorem tailTrace_1906328 : CollatzResearch.WordTrace tailWord_1906328 prefixEnd_1906328 652575032749548477755309 := by
  unfold tailWord_1906328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764747118853352873583819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46352996158471137164778425 34764747118853352873583819)
  ·
    refine ⟨52147120678280029310375729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764747118853352873583819 52147120678280029310375729)
    ·
      refine ⟨39110340508710021982781797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52147120678280029310375729 39110340508710021982781797)
      ·
        refine ⟨7333188845383129121771587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39110340508710021982781797 7333188845383129121771587)
        ·
          refine ⟨10999783268074693682657381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333188845383129121771587 10999783268074693682657381)
          ·
            refine ⟨2062459362764005065498259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10999783268074693682657381 2062459362764005065498259)
            ·
              refine ⟨3093689044146007598247389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062459362764005065498259 3093689044146007598247389)
              ·
                refine ⟨1160133391554752849342771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093689044146007598247389 1160133391554752849342771)
                ·
                  refine ⟨1740200087332129274014157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160133391554752849342771 1740200087332129274014157)
                  ·
                    refine ⟨652575032749548477755309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740200087332129274014157 652575032749548477755309)
                    ·
                      rfl

theorem cell22_1906328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_1906328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906328 prefixEnd_1906328 := by exact prefixLift 1906328
  have htrace : WordTrace (prefixWord ++ tailWord_1906328) baseStart_1906328 baseEnd_1906328 := by
    simpa [prefixWord, tailWord_1906328, baseEnd_1906328] using wordTrace_append hprefix tailTrace_1906328
  have hstable : (prefixWord ++ tailWord_1906328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906328).length < 2 ^ (prefixWord ++ tailWord_1906328).sum := by decide
  have hdescent : baseEnd_1906328 < baseStart_1906328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906352 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_1906352 : Nat := 118140960795 + 1906352 * 2 ^ 59
def prefixEnd_1906352 : Nat := 4983230072969 + 3 ^ 40 * 1906352 * 2
def baseEnd_1906352 : Nat := 217527749480006805051745

theorem tailTrace_1906352 : CollatzResearch.WordTrace tailWord_1906352 prefixEnd_1906352 217527749480006805051745 := by
  unfold tailWord_1906352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765184794809878923020655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46353579726413171897360873 34765184794809878923020655)
  ·
    refine ⟨52147777192214818384530983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34765184794809878923020655 52147777192214818384530983)
    ·
      refine ⟨78221665788322227576796475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52147777192214818384530983 78221665788322227576796475)
      ·
        refine ⟨117332498682483341365194713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78221665788322227576796475 117332498682483341365194713)
        ·
          refine ⟨87999374011862506023896035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117332498682483341365194713 87999374011862506023896035)
          ·
            refine ⟨131999061017793759035844053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87999374011862506023896035 131999061017793759035844053)
            ·
              refine ⟨3093727992604541227402595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131999061017793759035844053 3093727992604541227402595)
              ·
                refine ⟨4640591988906811841103893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093727992604541227402595 4640591988906811841103893)
                ·
                  refine ⟨217527749480006805051745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4640591988906811841103893 217527749480006805051745)
                  ·
                    rfl

theorem cell22_1906352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_1906352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906352 prefixEnd_1906352 := by exact prefixLift 1906352
  have htrace : WordTrace (prefixWord ++ tailWord_1906352) baseStart_1906352 baseEnd_1906352 := by
    simpa [prefixWord, tailWord_1906352, baseEnd_1906352] using wordTrace_append hprefix tailTrace_1906352
  have hstable : (prefixWord ++ tailWord_1906352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906352).length < 2 ^ (prefixWord ++ tailWord_1906352).sum := by decide
  have hdescent : baseEnd_1906352 < baseStart_1906352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906358 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1906358 : Nat := 118140960795 + 1906358 * 2 ^ 59
def prefixEnd_1906358 : Nat := 4983230072969 + 3 ^ 40 * 1906358 * 2
def baseEnd_1906358 : Nat := 217528434120879466501739

theorem tailTrace_1906358 : CollatzResearch.WordTrace tailWord_1906358 prefixEnd_1906358 217528434120879466501739 := by
  unfold tailWord_1906358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345661776724876304422483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46353725618398680580506485 4345661776724876304422483)
  ·
    refine ⟨6518492665087314456633725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345661776724876304422483 6518492665087314456633725)
    ·
      refine ⟨2444434749407742921237647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6518492665087314456633725 2444434749407742921237647)
      ·
        refine ⟨3666652124111614381856471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444434749407742921237647 3666652124111614381856471)
        ·
          refine ⟨5499978186167421572784707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666652124111614381856471 5499978186167421572784707)
          ·
            refine ⟨8249967279251132359177061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499978186167421572784707 8249967279251132359177061)
            ·
              refine ⟨1546868864859587317345699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8249967279251132359177061 1546868864859587317345699)
              ·
                refine ⟨2320303297289380976018549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546868864859587317345699 2320303297289380976018549)
                ·
                  refine ⟨217528434120879466501739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320303297289380976018549 217528434120879466501739)
                  ·
                    rfl

theorem cell22_1906358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1906358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906358 prefixEnd_1906358 := by exact prefixLift 1906358
  have htrace : WordTrace (prefixWord ++ tailWord_1906358) baseStart_1906358 baseEnd_1906358 := by
    simpa [prefixWord, tailWord_1906358, baseEnd_1906358] using wordTrace_append hprefix tailTrace_1906358
  have hstable : (prefixWord ++ tailWord_1906358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906358).length < 2 ^ (prefixWord ++ tailWord_1906358).sum := by decide
  have hdescent : baseEnd_1906358 < baseStart_1906358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906367 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1906367 : Nat := 118140960795 + 1906367 * 2 ^ 59
def prefixEnd_1906367 : Nat := 4983230072969 + 3 ^ 40 * 1906367 * 2
def baseEnd_1906367 : Nat := 652588383246565376030189

theorem tailTrace_1906367 : CollatzResearch.WordTrace tailWord_1906367 prefixEnd_1906367 652588383246565376030189 := by
  unfold tailWord_1906367
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530916684565415407837355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46353944456376943605224903 69530916684565415407837355)
  ·
    refine ⟨104296375026848123111756033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69530916684565415407837355 104296375026848123111756033)
    ·
      refine ⟨78222281270136092333817025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104296375026848123111756033 78222281270136092333817025)
      ·
        refine ⟨58666710952602069250362769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78222281270136092333817025 58666710952602069250362769)
        ·
          refine ⟨44000033214451551937772077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58666710952602069250362769 44000033214451551937772077)
          ·
            refine ⟨16500012455419331976664529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44000033214451551937772077 16500012455419331976664529)
            ·
              refine ⟨12375009341564498982498397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16500012455419331976664529 12375009341564498982498397)
              ·
                refine ⟨4640628503086687118436899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12375009341564498982498397 4640628503086687118436899)
                ·
                  refine ⟨6960942754630030677655349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640628503086687118436899 6960942754630030677655349)
                  ·
                    refine ⟨652588383246565376030189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6960942754630030677655349 652588383246565376030189)
                    ·
                      rfl

theorem cell22_1906367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1906367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906367 prefixEnd_1906367 := by exact prefixLift 1906367
  have htrace : WordTrace (prefixWord ++ tailWord_1906367) baseStart_1906367 baseEnd_1906367 := by
    simpa [prefixWord, tailWord_1906367, baseEnd_1906367] using wordTrace_append hprefix tailTrace_1906367
  have hstable : (prefixWord ++ tailWord_1906367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906367).length < 2 ^ (prefixWord ++ tailWord_1906367).sum := by decide
  have hdescent : baseEnd_1906367 < baseStart_1906367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906388 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1906388 : Nat := 118140960795 + 1906388 * 2 ^ 59
def prefixEnd_1906388 : Nat := 4983230072969 + 3 ^ 40 * 1906388 * 2
def baseEnd_1906388 : Nat := 652595571975728321255125

theorem tailTrace_1906388 : CollatzResearch.WordTrace tailWord_1906388 prefixEnd_1906388 652595571975728321255125 := by
  unfold tailWord_1906388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765841308744667997175909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46354455078326223996234545 34765841308744667997175909)
  ·
    refine ⟨6518595245389625249470483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34765841308744667997175909 6518595245389625249470483)
    ·
      refine ⟨9777892868084437874205725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518595245389625249470483 9777892868084437874205725)
      ·
        refine ⟨3666709825531664202827147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9777892868084437874205725 3666709825531664202827147)
        ·
          refine ⟨5500064738297496304240721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666709825531664202827147 5500064738297496304240721)
          ·
            refine ⟨4125048553723122228180541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5500064738297496304240721 4125048553723122228180541)
            ·
              refine ⟨1546893207646170835567703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125048553723122228180541 1546893207646170835567703)
              ·
                refine ⟨2320339811469256253351555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546893207646170835567703 2320339811469256253351555)
                ·
                  refine ⟨3480509717203884380027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320339811469256253351555 3480509717203884380027333)
                  ·
                    refine ⟨652595571975728321255125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480509717203884380027333 652595571975728321255125)
                    ·
                      rfl

theorem cell22_1906388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1906388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906388 prefixEnd_1906388 := by exact prefixLift 1906388
  have htrace : WordTrace (prefixWord ++ tailWord_1906388) baseStart_1906388 baseEnd_1906388 := by
    simpa [prefixWord, tailWord_1906388, baseEnd_1906388] using wordTrace_append hprefix tailTrace_1906388
  have hstable : (prefixWord ++ tailWord_1906388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906388).length < 2 ^ (prefixWord ++ tailWord_1906388).sum := by decide
  have hdescent : baseEnd_1906388 < baseStart_1906388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906476 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_1906476 : Nat := 118140960795 + 1906476 * 2 ^ 59
def prefixEnd_1906476 : Nat := 4983230072969 + 3 ^ 40 * 1906476 * 2
def baseEnd_1906476 : Nat := 217541898724708475018285

theorem tailTrace_1906476 : CollatzResearch.WordTrace tailWord_1906476 prefixEnd_1906476 217541898724708475018285 := by
  unfold tailWord_1906476
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767446120585263511777641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46356594827447018015703521 34767446120585263511777641)
  ·
    refine ⟨26075584590438947633833231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34767446120585263511777641 26075584590438947633833231)
    ·
      refine ⟨39113376885658421450749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26075584590438947633833231 39113376885658421450749847)
      ·
        refine ⟨58670065328487632176124771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39113376885658421450749847 58670065328487632176124771)
        ·
          refine ⟨88005097992731448264187157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58670065328487632176124771 88005097992731448264187157)
          ·
            refine ⟨4125238968409286637383773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88005097992731448264187157 4125238968409286637383773)
            ·
              refine ⟨1546964613153482489018915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125238968409286637383773 1546964613153482489018915)
              ·
                refine ⟨2320446919730223733528373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546964613153482489018915 2320446919730223733528373)
                ·
                  refine ⟨217541898724708475018285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320446919730223733528373 217541898724708475018285)
                  ·
                    rfl

theorem cell22_1906476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_1906476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906476 prefixEnd_1906476 := by exact prefixLift 1906476
  have htrace : WordTrace (prefixWord ++ tailWord_1906476) baseStart_1906476 baseEnd_1906476 := by
    simpa [prefixWord, tailWord_1906476, baseEnd_1906476] using wordTrace_append hprefix tailTrace_1906476
  have hstable : (prefixWord ++ tailWord_1906476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906476).length < 2 ^ (prefixWord ++ tailWord_1906476).sum := by decide
  have hdescent : baseEnd_1906476 < baseStart_1906476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906487 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 8]
def baseStart_1906487 : Nat := 118140960795 + 1906487 * 2 ^ 59
def prefixEnd_1906487 : Nat := 4983230072969 + 3 ^ 40 * 1906487 * 2
def baseEnd_1906487 : Nat := 217543153899641687676607

theorem tailTrace_1906487 : CollatzResearch.WordTrace tailWord_1906487 prefixEnd_1906487 217543153899641687676607 := by
  unfold tailWord_1906487
  simp only [CollatzResearch.WordTrace]
  refine ⟨69535293444130675902205715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46356862296087117268137143 69535293444130675902205715)
  ·
    refine ⟨104302940166196013853308573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69535293444130675902205715 104302940166196013853308573)
    ·
      refine ⟨39113602562323505194990715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104302940166196013853308573 39113602562323505194990715)
      ·
        refine ⟨58670403843485257792486073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39113602562323505194990715 58670403843485257792486073)
        ·
          refine ⟨44002802882613943344364555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58670403843485257792486073 44002802882613943344364555)
          ·
            refine ⟨66004204323920915016546833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44002802882613943344364555 66004204323920915016546833)
            ·
              refine ⟨49503153242940686262410125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66004204323920915016546833 49503153242940686262410125)
              ·
                refine ⟨18563682466102757348403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49503153242940686262410125 18563682466102757348403797)
                ·
                  refine ⟨217543153899641687676607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18563682466102757348403797 217543153899641687676607)
                  ·
                    rfl

theorem cell22_1906487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_1906487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906487 prefixEnd_1906487 := by exact prefixLift 1906487
  have htrace : WordTrace (prefixWord ++ tailWord_1906487) baseStart_1906487 baseEnd_1906487 := by
    simpa [prefixWord, tailWord_1906487, baseEnd_1906487] using wordTrace_append hprefix tailTrace_1906487
  have hstable : (prefixWord ++ tailWord_1906487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906487).length < 2 ^ (prefixWord ++ tailWord_1906487).sum := by decide
  have hdescent : baseEnd_1906487 < baseStart_1906487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906549 : List Nat := [1, 3, 4, 1, 1, 1, 1, 10]
def baseStart_1906549 : Nat := 118140960795 + 1906549 * 2 ^ 59
def prefixEnd_1906549 : Nat := 4983230072969 + 3 ^ 40 * 1906549 * 2
def baseEnd_1906549 : Nat := 72516742840664174219959

theorem tailTrace_1906549 : CollatzResearch.WordTrace tailWord_1906549 prefixEnd_1906549 72516742840664174219959 := by
  unfold tailWord_1906549
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537554769906060490962701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46358369846604040327308467 69537554769906060490962701)
  ·
    refine ⟨26076583038714772684111013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69537554769906060490962701 26076583038714772684111013)
    ·
      refine ⟨4889359319759019878270815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26076583038714772684111013 4889359319759019878270815)
      ·
        refine ⟨7334038979638529817406223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889359319759019878270815 7334038979638529817406223)
        ·
          refine ⟨11001058469457794726109335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334038979638529817406223 11001058469457794726109335)
          ·
            refine ⟨16501587704186692089164003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001058469457794726109335 16501587704186692089164003)
            ·
              refine ⟨24752381556280038133746005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501587704186692089164003 24752381556280038133746005)
              ·
                refine ⟨72516742840664174219959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24752381556280038133746005 72516742840664174219959)
                ·
                  rfl

theorem cell22_1906549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 10].length) (baseStart_1906549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906549 prefixEnd_1906549 := by exact prefixLift 1906549
  have htrace : WordTrace (prefixWord ++ tailWord_1906549) baseStart_1906549 baseEnd_1906549 := by
    simpa [prefixWord, tailWord_1906549, baseEnd_1906549] using wordTrace_append hprefix tailTrace_1906549
  have hstable : (prefixWord ++ tailWord_1906549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906549).length < 2 ^ (prefixWord ++ tailWord_1906549).sum := by decide
  have hdescent : baseEnd_1906549 < baseStart_1906549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906570 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1906570 : Nat := 118140960795 + 1906570 * 2 ^ 59
def prefixEnd_1906570 : Nat := 4983230072969 + 3 ^ 40 * 1906570 * 2
def baseEnd_1906570 : Nat := 652657874295140513204567

theorem tailTrace_1906570 : CollatzResearch.WordTrace tailWord_1906570 prefixEnd_1906570 652657874295140513204567 := by
  unfold tailWord_1906570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17384580175707495269369291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46358880468553320718318109 17384580175707495269369291)
  ·
    refine ⟨26076870263561242904053937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17384580175707495269369291 26076870263561242904053937)
    ·
      refine ⟨19557652697670932178040453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26076870263561242904053937 19557652697670932178040453)
      ·
        refine ⟨3667059880813299783382585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19557652697670932178040453 3667059880813299783382585)
        ·
          refine ⟨2750294910609974837536939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3667059880813299783382585 2750294910609974837536939)
          ·
            refine ⟨4125442365914962256305409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750294910609974837536939 4125442365914962256305409)
            ·
              refine ⟨3094081774436221692229057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4125442365914962256305409 3094081774436221692229057)
              ·
                refine ⟨2320561330827166269171793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094081774436221692229057 2320561330827166269171793)
                ·
                  refine ⟨1740420998120374701878845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2320561330827166269171793 1740420998120374701878845)
                  ·
                    refine ⟨652657874295140513204567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740420998120374701878845 652657874295140513204567)
                    ·
                      rfl

theorem cell22_1906570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1906570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906570 prefixEnd_1906570 := by exact prefixLift 1906570
  have htrace : WordTrace (prefixWord ++ tailWord_1906570) baseStart_1906570 baseEnd_1906570 := by
    simpa [prefixWord, tailWord_1906570, baseEnd_1906570] using wordTrace_append hprefix tailTrace_1906570
  have hstable : (prefixWord ++ tailWord_1906570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906570).length < 2 ^ (prefixWord ++ tailWord_1906570).sum := by decide
  have hdescent : baseEnd_1906570 < baseStart_1906570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906581 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1906581 : Nat := 118140960795 + 1906581 * 2 ^ 59
def prefixEnd_1906581 : Nat := 4983230072969 + 3 ^ 40 * 1906581 * 2
def baseEnd_1906581 : Nat := 652661639819940151179533

theorem tailTrace_1906581 : CollatzResearch.WordTrace tailWord_1906581 prefixEnd_1906581 652661639819940151179533 := by
  unfold tailWord_1906581
  simp only [CollatzResearch.WordTrace]
  refine ⟨69538721905790129956127597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46359147937193419970751731 69538721905790129956127597)
  ·
    refine ⟨26077020714671298733547849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69538721905790129956127597 26077020714671298733547849)
    ·
      refine ⟨19557765536003474050160887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26077020714671298733547849 19557765536003474050160887)
      ·
        refine ⟨29336648304005211075241331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19557765536003474050160887 29336648304005211075241331)
        ·
          refine ⟨44004972456007816612861997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29336648304005211075241331 44004972456007816612861997)
          ·
            refine ⟨16501864671002931229823249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44004972456007816612861997 16501864671002931229823249)
            ·
              refine ⟨12376398503252198422367437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16501864671002931229823249 12376398503252198422367437)
              ·
                refine ⟨4641149438719574408387789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12376398503252198422367437 4641149438719574408387789)
                ·
                  refine ⟨1740431039519840403145421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4641149438719574408387789 1740431039519840403145421)
                  ·
                    refine ⟨652661639819940151179533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740431039519840403145421 652661639819940151179533)
                    ·
                      rfl

theorem cell22_1906581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1906581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906581 prefixEnd_1906581 := by exact prefixLift 1906581
  have htrace : WordTrace (prefixWord ++ tailWord_1906581) baseStart_1906581 baseEnd_1906581 := by
    simpa [prefixWord, tailWord_1906581, baseEnd_1906581] using wordTrace_append hprefix tailTrace_1906581
  have hstable : (prefixWord ++ tailWord_1906581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906581).length < 2 ^ (prefixWord ++ tailWord_1906581).sum := by decide
  have hdescent : baseEnd_1906581 < baseStart_1906581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906600 : List Nat := [2, 1, 6, 2, 1, 1, 3, 6]
def baseStart_1906600 : Nat := 118140960795 + 1906600 * 2 ^ 59
def prefixEnd_1906600 : Nat := 4983230072969 + 3 ^ 40 * 1906600 * 2
def baseEnd_1906600 : Nat := 72518682656470048328275

theorem tailTrace_1906600 : CollatzResearch.WordTrace tailWord_1906600 prefixEnd_1906600 72518682656470048328275 := by
  unfold tailWord_1906600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34769707446360648100534627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46359609928480864134046169 34769707446360648100534627)
  ·
    refine ⟨52154561169540972150801941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34769707446360648100534627 52154561169540972150801941)
    ·
      refine ⟨2444745054822233069568841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52154561169540972150801941 2444745054822233069568841)
      ·
        refine ⟨1833558791116674802176631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444745054822233069568841 1833558791116674802176631)
        ·
          refine ⟨2750338186675012203264947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833558791116674802176631 2750338186675012203264947)
          ·
            refine ⟨4125507280012518304897421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750338186675012203264947 4125507280012518304897421)
            ·
              refine ⟨1547065230004694364336533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125507280012518304897421 1547065230004694364336533)
              ·
                refine ⟨72518682656470048328275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1547065230004694364336533 72518682656470048328275)
                ·
                  rfl

theorem cell22_1906600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_1906600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906600 prefixEnd_1906600 := by exact prefixLift 1906600
  have htrace : WordTrace (prefixWord ++ tailWord_1906600) baseStart_1906600 baseEnd_1906600 := by
    simpa [prefixWord, tailWord_1906600, baseEnd_1906600] using wordTrace_append hprefix tailTrace_1906600
  have hstable : (prefixWord ++ tailWord_1906600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906600).length < 2 ^ (prefixWord ++ tailWord_1906600).sum := by decide
  have hdescent : baseEnd_1906600 < baseStart_1906600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906671 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 6, 3]
def baseStart_1906671 : Nat := 118140960795 + 1906671 * 2 ^ 59
def prefixEnd_1906671 : Nat := 4983230072969 + 3 ^ 40 * 1906671 * 2
def baseEnd_1906671 : Nat := 652692448659209916429257

theorem tailTrace_1906671 : CollatzResearch.WordTrace tailWord_1906671 prefixEnd_1906671 652692448659209916429257 := by
  unfold tailWord_1906671
  simp only [CollatzResearch.WordTrace]
  refine ⟨69542004475464075326903867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46361336316976050217935911 69542004475464075326903867)
  ·
    refine ⟨104313006713196112990355801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69542004475464075326903867 104313006713196112990355801)
    ·
      refine ⟨78234755034897084742766851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104313006713196112990355801 78234755034897084742766851)
      ·
        refine ⟨117352132552345627114150277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78234755034897084742766851 117352132552345627114150277)
        ·
          refine ⟨22003524853564805083903177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117352132552345627114150277 22003524853564805083903177)
          ·
            refine ⟨16502643640173603812927383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22003524853564805083903177 16502643640173603812927383)
            ·
              refine ⟨24753965460260405719391075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16502643640173603812927383 24753965460260405719391075)
              ·
                refine ⟨37130948190390608579086613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24753965460260405719391075 37130948190390608579086613)
                ·
                  refine ⟨1740513196424559777144685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37130948190390608579086613 1740513196424559777144685)
                  ·
                    refine ⟨652692448659209916429257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740513196424559777144685 652692448659209916429257)
                    ·
                      rfl

theorem cell22_1906671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_1906671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906671 prefixEnd_1906671 := by exact prefixLift 1906671
  have htrace : WordTrace (prefixWord ++ tailWord_1906671) baseStart_1906671 baseEnd_1906671 := by
    simpa [prefixWord, tailWord_1906671, baseEnd_1906671] using wordTrace_append hprefix tailTrace_1906671
  have hstable : (prefixWord ++ tailWord_1906671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906671).length < 2 ^ (prefixWord ++ tailWord_1906671).sum := by decide
  have hdescent : baseEnd_1906671 < baseStart_1906671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906761 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_1906761 : Nat := 118140960795 + 1906761 * 2 ^ 59
def prefixEnd_1906761 : Nat := 4983230072969 + 3 ^ 40 * 1906761 * 2
def baseEnd_1906761 : Nat := 652723257498479681678981

theorem tailTrace_1906761 : CollatzResearch.WordTrace tailWord_1906761 prefixEnd_1906761 652723257498479681678981 := by
  unfold tailWord_1906761
  simp only [CollatzResearch.WordTrace]
  refine ⟨69545287045138020697680137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46363524696758680465120091 69545287045138020697680137)
  ·
    refine ⟨52158965283853515523260103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69545287045138020697680137 52158965283853515523260103)
    ·
      refine ⟨78238447925780273284890155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52158965283853515523260103 78238447925780273284890155)
      ·
        refine ⟨117357671888670409927335233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78238447925780273284890155 117357671888670409927335233)
        ·
          refine ⟨88018253916502807445501425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117357671888670409927335233 88018253916502807445501425)
          ·
            refine ⟨66013690437377105584126069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88018253916502807445501425 66013690437377105584126069)
            ·
              refine ⟨6188783478504103648511819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66013690437377105584126069 6188783478504103648511819)
              ·
                refine ⟨9283175217756155472767729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188783478504103648511819 9283175217756155472767729)
                ·
                  refine ⟨6962381413317116604575797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283175217756155472767729 6962381413317116604575797)
                  ·
                    refine ⟨652723257498479681678981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962381413317116604575797 652723257498479681678981)
                    ·
                      rfl

theorem cell22_1906761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_1906761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906761 prefixEnd_1906761 := by exact prefixLift 1906761
  have htrace : WordTrace (prefixWord ++ tailWord_1906761) baseStart_1906761 baseEnd_1906761 := by
    simpa [prefixWord, tailWord_1906761, baseEnd_1906761] using wordTrace_append hprefix tailTrace_1906761
  have hstable : (prefixWord ++ tailWord_1906761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906761).length < 2 ^ (prefixWord ++ tailWord_1906761).sum := by decide
  have hdescent : baseEnd_1906761 < baseStart_1906761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906791 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 8]
def baseStart_1906791 : Nat := 118140960795 + 1906791 * 2 ^ 59
def prefixEnd_1906791 : Nat := 4983230072969 + 3 ^ 40 * 1906791 * 2
def baseEnd_1906791 : Nat := 217577842370523201142963

theorem tailTrace_1906791 : CollatzResearch.WordTrace tailWord_1906791 prefixEnd_1906791 217577842370523201142963 := by
  unfold tailWord_1906791
  simp only [CollatzResearch.WordTrace]
  refine ⟨69546381235029335821272227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46364254156686223880848151 69546381235029335821272227)
  ·
    refine ⟨104319571852544003731908341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69546381235029335821272227 104319571852544003731908341)
    ·
      refine ⟨9779959861176000349866407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104319571852544003731908341 9779959861176000349866407)
      ·
        refine ⟨14669939791764000524799611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779959861176000349866407 14669939791764000524799611)
        ·
          refine ⟨22004909687646000787199417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14669939791764000524799611 22004909687646000787199417)
          ·
            refine ⟨16503682265734500590399563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22004909687646000787199417 16503682265734500590399563)
            ·
              refine ⟨24755523398601750885599345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16503682265734500590399563 24755523398601750885599345)
              ·
                refine ⟨18566642548951313164199509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24755523398601750885599345 18566642548951313164199509)
                ·
                  refine ⟨217577842370523201142963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18566642548951313164199509 217577842370523201142963)
                  ·
                    rfl

theorem cell22_1906791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_1906791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906791 prefixEnd_1906791 := by exact prefixLift 1906791
  have htrace : WordTrace (prefixWord ++ tailWord_1906791) baseStart_1906791 baseEnd_1906791 := by
    simpa [prefixWord, tailWord_1906791, baseEnd_1906791] using wordTrace_append hprefix tailTrace_1906791
  have hstable : (prefixWord ++ tailWord_1906791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906791).length < 2 ^ (prefixWord ++ tailWord_1906791).sum := by decide
  have hdescent : baseEnd_1906791 < baseStart_1906791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906793 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_1906793 : Nat := 118140960795 + 1906793 * 2 ^ 59
def prefixEnd_1906793 : Nat := 4983230072969 + 3 ^ 40 * 1906793 * 2
def baseEnd_1906793 : Nat := 652734211752442264878883

theorem tailTrace_1906793 : CollatzResearch.WordTrace tailWord_1906793 prefixEnd_1906793 652734211752442264878883 := by
  unfold tailWord_1906793
  simp only [CollatzResearch.WordTrace]
  refine ⟨69546454181022090162845033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46364302787348060108563355 69546454181022090162845033)
  ·
    refine ⟨52159840635766567622133775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69546454181022090162845033 52159840635766567622133775)
    ·
      refine ⟨78239760953649851433200663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52159840635766567622133775 78239760953649851433200663)
      ·
        refine ⟨117359641430474777149800995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78239760953649851433200663 117359641430474777149800995)
        ·
          refine ⟨176039462145712165724701493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117359641430474777149800995 176039462145712165724701493)
          ·
            refine ⟨16503699576160515536690765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176039462145712165724701493 16503699576160515536690765)
            ·
              refine ⟨6188887341060193326259037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16503699576160515536690765 6188887341060193326259037)
              ·
                refine ⟨2320832752897572497347139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6188887341060193326259037 2320832752897572497347139)
                ·
                  refine ⟨3481249129346358746020709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320832752897572497347139 3481249129346358746020709)
                  ·
                    refine ⟨652734211752442264878883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481249129346358746020709 652734211752442264878883)
                    ·
                      rfl

theorem cell22_1906793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_1906793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906793 prefixEnd_1906793 := by exact prefixLift 1906793
  have htrace : WordTrace (prefixWord ++ tailWord_1906793) baseStart_1906793 baseEnd_1906793 := by
    simpa [prefixWord, tailWord_1906793, baseEnd_1906793] using wordTrace_append hprefix tailTrace_1906793
  have hstable : (prefixWord ++ tailWord_1906793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906793).length < 2 ^ (prefixWord ++ tailWord_1906793).sum := by decide
  have hdescent : baseEnd_1906793 < baseStart_1906793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906823 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1906823 : Nat := 118140960795 + 1906823 * 2 ^ 59
def prefixEnd_1906823 : Nat := 4983230072969 + 3 ^ 40 * 1906823 * 2
def baseEnd_1906823 : Nat := 652744481365532186628791

theorem tailTrace_1906823 : CollatzResearch.WordTrace tailWord_1906823 prefixEnd_1906823 652744481365532186628791 := by
  unfold tailWord_1906823
  simp only [CollatzResearch.WordTrace]
  refine ⟨69547548370913405286437123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46365032247275603524291415 69547548370913405286437123)
  ·
    refine ⟨104321322556370107929655685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69547548370913405286437123 104321322556370107929655685)
    ·
      refine ⟨19560247979319395236810441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104321322556370107929655685 19560247979319395236810441)
      ·
        refine ⟨14670185984489546427607831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19560247979319395236810441 14670185984489546427607831)
        ·
          refine ⟨22005278976734319641411747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14670185984489546427607831 22005278976734319641411747)
          ·
            refine ⟨33007918465101479462117621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22005278976734319641411747 33007918465101479462117621)
            ·
              refine ⟨3094492356103263699573527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33007918465101479462117621 3094492356103263699573527)
              ·
                refine ⟨4641738534154895549360291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094492356103263699573527 4641738534154895549360291)
                ·
                  refine ⟨6962607801232343324040437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641738534154895549360291 6962607801232343324040437)
                  ·
                    refine ⟨652744481365532186628791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962607801232343324040437 652744481365532186628791)
                    ·
                      rfl

theorem cell22_1906823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1906823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906823 prefixEnd_1906823 := by exact prefixLift 1906823
  have htrace : WordTrace (prefixWord ++ tailWord_1906823) baseStart_1906823 baseEnd_1906823 := by
    simpa [prefixWord, tailWord_1906823, baseEnd_1906823] using wordTrace_append hprefix tailTrace_1906823
  have hstable : (prefixWord ++ tailWord_1906823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906823).length < 2 ^ (prefixWord ++ tailWord_1906823).sum := by decide
  have hdescent : baseEnd_1906823 < baseStart_1906823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906913 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1906913 : Nat := 118140960795 + 1906913 * 2 ^ 59
def prefixEnd_1906913 : Nat := 4983230072969 + 3 ^ 40 * 1906913 * 2
def baseEnd_1906913 : Nat := 652775290204801951878515

theorem tailTrace_1906913 : CollatzResearch.WordTrace tailWord_1906913 prefixEnd_1906913 652775290204801951878515 := by
  unfold tailWord_1906913
  simp only [CollatzResearch.WordTrace]
  refine ⟨69550830940587350657213393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367220627058233771475595 69550830940587350657213393)
  ·
    refine ⟨52163123205440512992910045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69550830940587350657213393 52163123205440512992910045)
    ·
      refine ⟨19561171202040192372341267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52163123205440512992910045 19561171202040192372341267)
      ·
        refine ⟨29341756803060288558511901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19561171202040192372341267 29341756803060288558511901)
        ·
          refine ⟨11003158801147608209441963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29341756803060288558511901 11003158801147608209441963)
          ·
            refine ⟨16504738201721412314162945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11003158801147608209441963 16504738201721412314162945)
            ·
              refine ⟨12378553651291059235622209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16504738201721412314162945 12378553651291059235622209)
              ·
                refine ⟨9283915238468294426716657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12378553651291059235622209 9283915238468294426716657)
                ·
                  refine ⟨6962936428851220820037493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283915238468294426716657 6962936428851220820037493)
                  ·
                    refine ⟨652775290204801951878515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962936428851220820037493 652775290204801951878515)
                    ·
                      rfl

theorem cell22_1906913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1906913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906913 prefixEnd_1906913 := by exact prefixLift 1906913
  have htrace : WordTrace (prefixWord ++ tailWord_1906913) baseStart_1906913 baseEnd_1906913 := by
    simpa [prefixWord, tailWord_1906913, baseEnd_1906913] using wordTrace_append hprefix tailTrace_1906913
  have hstable : (prefixWord ++ tailWord_1906913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906913).length < 2 ^ (prefixWord ++ tailWord_1906913).sum := by decide
  have hdescent : baseEnd_1906913 < baseStart_1906913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906919 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1906919 : Nat := 118140960795 + 1906919 * 2 ^ 59
def prefixEnd_1906919 : Nat := 4983230072969 + 3 ^ 40 * 1906919 * 2
def baseEnd_1906919 : Nat := 652777344127419936228497

theorem tailTrace_1906919 : CollatzResearch.WordTrace tailWord_1906919 prefixEnd_1906919 652777344127419936228497 := by
  unfold tailWord_1906919
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551049778565613681931811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367366519043742454621207 69551049778565613681931811)
  ·
    refine ⟨104326574667848420522897717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69551049778565613681931811 104326574667848420522897717)
    ·
      refine ⟨9780616375110789424021661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104326574667848420522897717 9780616375110789424021661)
      ·
        refine ⟨3667731140666546034008123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9780616375110789424021661 3667731140666546034008123)
        ·
          refine ⟨5501596710999819051012185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667731140666546034008123 5501596710999819051012185)
          ·
            refine ⟨4126197533249864288259139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501596710999819051012185 4126197533249864288259139)
            ·
              refine ⟨6189296299874796432388709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126197533249864288259139 6189296299874796432388709)
              ·
                refine ⟨1160493056226524331072883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6189296299874796432388709 1160493056226524331072883)
                ·
                  refine ⟨1740739584339786496609325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160493056226524331072883 1740739584339786496609325)
                  ·
                    refine ⟨652777344127419936228497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740739584339786496609325 652777344127419936228497)
                    ·
                      rfl

theorem cell22_1906919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1906919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906919 prefixEnd_1906919 := by exact prefixLift 1906919
  have htrace : WordTrace (prefixWord ++ tailWord_1906919) baseStart_1906919 baseEnd_1906919 := by
    simpa [prefixWord, tailWord_1906919, baseEnd_1906919] using wordTrace_append hprefix tailTrace_1906919
  have hstable : (prefixWord ++ tailWord_1906919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906919).length < 2 ^ (prefixWord ++ tailWord_1906919).sum := by decide
  have hdescent : baseEnd_1906919 < baseStart_1906919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906930 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1906930 : Nat := 118140960795 + 1906930 * 2 ^ 59
def prefixEnd_1906930 : Nat := 4983230072969 + 3 ^ 40 * 1906930 * 2
def baseEnd_1906930 : Nat := 652781109652219574203463

theorem tailTrace_1906930 : CollatzResearch.WordTrace tailWord_1906930 prefixEnd_1906930 652781109652219574203463 := by
  unfold tailWord_1906930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387862745381440640145561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46367633987683841707054829 17387862745381440640145561)
  ·
    refine ⟨13040897059036080480109171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17387862745381440640145561 13040897059036080480109171)
    ·
      refine ⟨19561345588554120720163757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13040897059036080480109171 19561345588554120720163757)
      ·
        refine ⟨7335504595707795270061409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19561345588554120720163757 7335504595707795270061409)
        ·
          refine ⟨5501628446780846452546057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7335504595707795270061409 5501628446780846452546057)
          ·
            refine ⟨4126221335085634839409543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501628446780846452546057 4126221335085634839409543)
            ·
              refine ⟨6189332002628452259114315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126221335085634839409543 6189332002628452259114315)
              ·
                refine ⟨9283998003942678388671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6189332002628452259114315 9283998003942678388671473)
                ·
                  refine ⟨6962998502957008791503605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283998003942678388671473 6962998502957008791503605)
                  ·
                    refine ⟨652781109652219574203463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962998502957008791503605 652781109652219574203463)
                    ·
                      rfl

theorem cell22_1906930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1906930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906930 prefixEnd_1906930 := by exact prefixLift 1906930
  have htrace : WordTrace (prefixWord ++ tailWord_1906930) baseStart_1906930 baseEnd_1906930 := by
    simpa [prefixWord, tailWord_1906930, baseEnd_1906930] using wordTrace_append hprefix tailTrace_1906930
  have hstable : (prefixWord ++ tailWord_1906930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906930).length < 2 ^ (prefixWord ++ tailWord_1906930).sum := by decide
  have hdescent : baseEnd_1906930 < baseStart_1906930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906943 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 6]
def baseStart_1906943 : Nat := 118140960795 + 1906943 * 2 ^ 59
def prefixEnd_1906943 : Nat := 4983230072969 + 3 ^ 40 * 1906943 * 2
def baseEnd_1906943 : Nat := 217595186605963957876141

theorem tailTrace_1906943 : CollatzResearch.WordTrace tailWord_1906943 prefixEnd_1906943 217595186605963957876141 := by
  unfold tailWord_1906943
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551925130478665780805483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367950086985777187203655 69551925130478665780805483)
  ·
    refine ⟨104327887695717998671208225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69551925130478665780805483 104327887695717998671208225)
    ·
      refine ⟨78245915771788499003406169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104327887695717998671208225 78245915771788499003406169)
      ·
        refine ⟨58684436828841374252554627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78245915771788499003406169 58684436828841374252554627)
        ·
          refine ⟨88026655243262061378831941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58684436828841374252554627 88026655243262061378831941)
          ·
            refine ⟨16504997858111636508530989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88026655243262061378831941 16504997858111636508530989)
            ·
              refine ⟨6189374196791863690699121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16504997858111636508530989 6189374196791863690699121)
              ·
                refine ⟨4642030647593897768024341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189374196791863690699121 4642030647593897768024341)
                ·
                  refine ⟨217595186605963957876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4642030647593897768024341 217595186605963957876141)
                  ·
                    rfl

theorem cell22_1906943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_1906943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906943 prefixEnd_1906943 := by exact prefixLift 1906943
  have htrace : WordTrace (prefixWord ++ tailWord_1906943) baseStart_1906943 baseEnd_1906943 := by
    simpa [prefixWord, tailWord_1906943, baseEnd_1906943] using wordTrace_append hprefix tailTrace_1906943
  have hstable : (prefixWord ++ tailWord_1906943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906943).length < 2 ^ (prefixWord ++ tailWord_1906943).sum := by decide
  have hdescent : baseEnd_1906943 < baseStart_1906943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1906945 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1906945 : Nat := 118140960795 + 1906945 * 2 ^ 59
def prefixEnd_1906945 : Nat := 4983230072969 + 3 ^ 40 * 1906945 * 2
def baseEnd_1906945 : Nat := 652786244458764535078417

theorem tailTrace_1906945 : CollatzResearch.WordTrace tailWord_1906945 prefixEnd_1906945 652786244458764535078417 := by
  unfold tailWord_1906945
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551998076471420122378289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46367998717647613414918859 69551998076471420122378289)
  ·
    refine ⟨52163998557353565091783717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69551998076471420122378289 52163998557353565091783717)
    ·
      refine ⟨9780749729503793454709447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52163998557353565091783717 9780749729503793454709447)
      ·
        refine ⟨14671124594255690182064171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9780749729503793454709447 14671124594255690182064171)
        ·
          refine ⟨22006686891383535273096257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14671124594255690182064171 22006686891383535273096257)
          ·
            refine ⟨16505015168537651454822193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22006686891383535273096257 16505015168537651454822193)
            ·
              refine ⟨12378761376403238591116645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16505015168537651454822193 12378761376403238591116645)
              ·
                refine ⟨2321017758075607235834371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12378761376403238591116645 2321017758075607235834371)
                ·
                  refine ⟨3481526637113410853751557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321017758075607235834371 3481526637113410853751557)
                  ·
                    refine ⟨652786244458764535078417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481526637113410853751557 652786244458764535078417)
                    ·
                      rfl

theorem cell22_1906945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1906945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1906945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1906945 prefixEnd_1906945 := by exact prefixLift 1906945
  have htrace : WordTrace (prefixWord ++ tailWord_1906945) baseStart_1906945 baseEnd_1906945 := by
    simpa [prefixWord, tailWord_1906945, baseEnd_1906945] using wordTrace_append hprefix tailTrace_1906945
  have hstable : (prefixWord ++ tailWord_1906945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1906945).length < 2 ^ (prefixWord ++ tailWord_1906945).sum := by decide
  have hdescent : baseEnd_1906945 < baseStart_1906945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1906945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907018 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1907018 : Nat := 118140960795 + 1907018 * 2 ^ 59
def prefixEnd_1907018 : Nat := 4983230072969 + 3 ^ 40 * 1907018 * 2
def baseEnd_1907018 : Nat := 652811233850616678003193

theorem tailTrace_1907018 : CollatzResearch.WordTrace tailWord_1907018 prefixEnd_1907018 652811233850616678003193 := by
  unfold tailWord_1907018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388665151301738397446427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46369773736804635726523805 17388665151301738397446427)
  ·
    refine ⟨26082997726952607596169641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17388665151301738397446427 26082997726952607596169641)
    ·
      refine ⟨19562248295214455697127231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26082997726952607596169641 19562248295214455697127231)
      ·
        refine ⟨29343372442821683545690847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562248295214455697127231 29343372442821683545690847)
        ·
          refine ⟨44015058664232525318536271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29343372442821683545690847 44015058664232525318536271)
          ·
            refine ⟨66022587996348787977804407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44015058664232525318536271 66022587996348787977804407)
            ·
              refine ⟨99033881994523181966706611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66022587996348787977804407 99033881994523181966706611)
              ·
                refine ⟨148550822991784772950059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99033881994523181966706611 148550822991784772950059917)
                ·
                  refine ⟨55706558621919289856272469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148550822991784772950059917 55706558621919289856272469)
                  ·
                    refine ⟨652811233850616678003193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55706558621919289856272469 652811233850616678003193)
                    ·
                      rfl

theorem cell22_1907018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1907018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907018 prefixEnd_1907018 := by exact prefixLift 1907018
  have htrace : WordTrace (prefixWord ++ tailWord_1907018) baseStart_1907018 baseEnd_1907018 := by
    simpa [prefixWord, tailWord_1907018, baseEnd_1907018] using wordTrace_append hprefix tailTrace_1907018
  have hstable : (prefixWord ++ tailWord_1907018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907018).length < 2 ^ (prefixWord ++ tailWord_1907018).sum := by decide
  have hdescent : baseEnd_1907018 < baseStart_1907018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907112 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_1907112 : Nat := 118140960795 + 1907112 * 2 ^ 59
def prefixEnd_1907112 : Nat := 4983230072969 + 3 ^ 40 * 1907112 * 2
def baseEnd_1907112 : Nat := 217614470657210588717635

theorem tailTrace_1907112 : CollatzResearch.WordTrace tailWord_1907112 prefixEnd_1907112 217614470657210588717635 := by
  unfold tailWord_1907112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34779044533433203821853795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46372059377910938429138393 34779044533433203821853795)
  ·
    refine ⟨52168566800149805732780693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34779044533433203821853795 52168566800149805732780693)
    ·
      refine ⟨2445401568757022143724095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52168566800149805732780693 2445401568757022143724095)
      ·
        refine ⟨3668102353135533215586143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445401568757022143724095 3668102353135533215586143)
        ·
          refine ⟨5502153529703299823379215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668102353135533215586143 5502153529703299823379215)
          ·
            refine ⟨8253230294554949735068823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502153529703299823379215 8253230294554949735068823)
            ·
              refine ⟨12379845441832424602603235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253230294554949735068823 12379845441832424602603235)
              ·
                refine ⟨18569768162748636903904853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379845441832424602603235 18569768162748636903904853)
                ·
                  refine ⟨217614470657210588717635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18569768162748636903904853 217614470657210588717635)
                  ·
                    rfl

theorem cell22_1907112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_1907112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907112 prefixEnd_1907112 := by exact prefixLift 1907112
  have htrace : WordTrace (prefixWord ++ tailWord_1907112) baseStart_1907112 baseEnd_1907112 := by
    simpa [prefixWord, tailWord_1907112, baseEnd_1907112] using wordTrace_append hprefix tailTrace_1907112
  have hstable : (prefixWord ++ tailWord_1907112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907112).length < 2 ^ (prefixWord ++ tailWord_1907112).sum := by decide
  have hdescent : baseEnd_1907112 < baseStart_1907112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907129 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 4]
def baseStart_1907129 : Nat := 118140960795 + 1907129 * 2 ^ 59
def prefixEnd_1907129 : Nat := 4983230072969 + 3 ^ 40 * 1907129 * 2
def baseEnd_1907129 : Nat := 217616410473016462825951

theorem tailTrace_1907129 : CollatzResearch.WordTrace tailWord_1907129 prefixEnd_1907129 217616410473016462825951 := by
  unfold tailWord_1907129
  simp only [CollatzResearch.WordTrace]
  refine ⟨69558709107804819547076441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46372472738536546364717627 69558709107804819547076441)
  ·
    refine ⟨52169031830853614660307331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69558709107804819547076441 52169031830853614660307331)
    ·
      refine ⟨78253547746280421990460997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52169031830853614660307331 78253547746280421990460997)
      ·
        refine ⟨14672540202427579123211437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78253547746280421990460997 14672540202427579123211437)
        ·
          refine ⟨5502202575910342171204289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14672540202427579123211437 5502202575910342171204289)
          ·
            refine ⟨4126651931932756628403217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502202575910342171204289 4126651931932756628403217)
            ·
              refine ⟨3094988948949567471302413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126651931932756628403217 3094988948949567471302413)
              ·
                refine ⟨1160620855856087801738405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3094988948949567471302413 1160620855856087801738405)
                ·
                  refine ⟨217616410473016462825951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160620855856087801738405 217616410473016462825951)
                  ·
                    rfl

theorem cell22_1907129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_1907129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907129 prefixEnd_1907129 := by exact prefixLift 1907129
  have htrace : WordTrace (prefixWord ++ tailWord_1907129) baseStart_1907129 baseEnd_1907129 := by
    simpa [prefixWord, tailWord_1907129, baseEnd_1907129] using wordTrace_append hprefix tailTrace_1907129
  have hstable : (prefixWord ++ tailWord_1907129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907129).length < 2 ^ (prefixWord ++ tailWord_1907129).sum := by decide
  have hdescent : baseEnd_1907129 < baseStart_1907129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907144 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_1907144 : Nat := 118140960795 + 1907144 * 2 ^ 59
def prefixEnd_1907144 : Nat := 4983230072969 + 3 ^ 40 * 1907144 * 2
def baseEnd_1907144 : Nat := 652854366225594349352807

theorem tailTrace_1907144 : CollatzResearch.WordTrace tailWord_1907144 prefixEnd_1907144 652854366225594349352807 := by
  unfold tailWord_1907144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34779628101375238554436243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46372837468500318072581657 34779628101375238554436243)
  ·
    refine ⟨52169442152062857831654365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34779628101375238554436243 52169442152062857831654365)
    ·
      refine ⟨19563540807023571686870387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52169442152062857831654365 19563540807023571686870387)
      ·
        refine ⟨29345311210535357530305581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563540807023571686870387 29345311210535357530305581)
        ·
          refine ⟨11004491703950759073864593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29345311210535357530305581 11004491703950759073864593)
          ·
            refine ⟨8253368777963069305398445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11004491703950759073864593 8253368777963069305398445)
            ·
              refine ⟨3095013291736150989524417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8253368777963069305398445 3095013291736150989524417)
              ·
                refine ⟨2321259968802113242143313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095013291736150989524417 2321259968802113242143313)
                ·
                  refine ⟨1740944976601584931607485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321259968802113242143313 1740944976601584931607485)
                  ·
                    refine ⟨652854366225594349352807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740944976601584931607485 652854366225594349352807)
                    ·
                      rfl

theorem cell22_1907144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_1907144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907144 prefixEnd_1907144 := by exact prefixLift 1907144
  have htrace : WordTrace (prefixWord ++ tailWord_1907144) baseStart_1907144 baseEnd_1907144 := by
    simpa [prefixWord, tailWord_1907144, baseEnd_1907144] using wordTrace_append hprefix tailTrace_1907144
  have hstable : (prefixWord ++ tailWord_1907144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907144).length < 2 ^ (prefixWord ++ tailWord_1907144).sum := by decide
  have hdescent : baseEnd_1907144 < baseStart_1907144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907185 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 9]
def baseStart_1907185 : Nat := 118140960795 + 1907185 * 2 ^ 59
def prefixEnd_1907185 : Nat := 4983230072969 + 3 ^ 40 * 1907185 * 2
def baseEnd_1907185 : Nat := 217622800454494636359227

theorem tailTrace_1907185 : CollatzResearch.WordTrace tailWord_1907185 prefixEnd_1907185 217622800454494636359227 := by
  unfold tailWord_1907185
  simp only [CollatzResearch.WordTrace]
  refine ⟨69560751595601941111115009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46373834397067960740743339 69560751595601941111115009)
  ·
    refine ⟨52170563696701455833336257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69560751595601941111115009 52170563696701455833336257)
    ·
      refine ⟨39127922772526091875002193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52170563696701455833336257 39127922772526091875002193)
      ·
        refine ⟨29345942079394568906251645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39127922772526091875002193 29345942079394568906251645)
        ·
          refine ⟨11004728279772963339844367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29345942079394568906251645 11004728279772963339844367)
          ·
            refine ⟨16507092419659445009766551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004728279772963339844367 16507092419659445009766551)
            ·
              refine ⟨24760638629489167514649827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507092419659445009766551 24760638629489167514649827)
              ·
                refine ⟨37140957944233751271974741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24760638629489167514649827 37140957944233751271974741)
                ·
                  refine ⟨217622800454494636359227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37140957944233751271974741 217622800454494636359227)
                  ·
                    rfl

theorem cell22_1907185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_1907185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907185 prefixEnd_1907185 := by exact prefixLift 1907185
  have htrace : WordTrace (prefixWord ++ tailWord_1907185) baseStart_1907185 baseEnd_1907185 := by
    simpa [prefixWord, tailWord_1907185, baseEnd_1907185] using wordTrace_append hprefix tailTrace_1907185
  have hstable : (prefixWord ++ tailWord_1907185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907185).length < 2 ^ (prefixWord ++ tailWord_1907185).sum := by decide
  have hdescent : baseEnd_1907185 < baseStart_1907185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907268 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1907268 : Nat := 118140960795 + 1907268 * 2 ^ 59
def prefixEnd_1907268 : Nat := 4983230072969 + 3 ^ 40 * 1907268 * 2
def baseEnd_1907268 : Nat := 652896813959699359252427

theorem tailTrace_1907268 : CollatzResearch.WordTrace tailWord_1907268 prefixEnd_1907268 652896813959699359252427 := by
  unfold tailWord_1907268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781889427150623143193229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46375852569534164190924305 34781889427150623143193229)
  ·
    refine ⟨13043208535181483678697461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34781889427150623143193229 13043208535181483678697461)
    ·
      refine ⟨1222800800173264094877887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13043208535181483678697461 1222800800173264094877887)
      ·
        refine ⟨1834201200259896142316831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222800800173264094877887 1834201200259896142316831)
        ·
          refine ⟨2751301800389844213475247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834201200259896142316831 2751301800389844213475247)
          ·
            refine ⟨4126952700584766320212871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751301800389844213475247 4126952700584766320212871)
            ·
              refine ⟨6190429050877149480319307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126952700584766320212871 6190429050877149480319307)
              ·
                refine ⟨9285643576315724220478961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190429050877149480319307 9285643576315724220478961)
                ·
                  refine ⟨6964232682236793165359221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9285643576315724220478961 6964232682236793165359221)
                  ·
                    refine ⟨652896813959699359252427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6964232682236793165359221 652896813959699359252427)
                    ·
                      rfl

theorem cell22_1907268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1907268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907268 prefixEnd_1907268 := by exact prefixLift 1907268
  have htrace : WordTrace (prefixWord ++ tailWord_1907268) baseStart_1907268 baseEnd_1907268 := by
    simpa [prefixWord, tailWord_1907268, baseEnd_1907268] using wordTrace_append hprefix tailTrace_1907268
  have hstable : (prefixWord ++ tailWord_1907268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907268).length < 2 ^ (prefixWord ++ tailWord_1907268).sum := by decide
  have hdescent : baseEnd_1907268 < baseStart_1907268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907279 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 2, 3]
def baseStart_1907279 : Nat := 118140960795 + 1907279 * 2 ^ 59
def prefixEnd_1907279 : Nat := 4983230072969 + 3 ^ 40 * 1907279 * 2
def baseEnd_1907279 : Nat := 652900579484498997227393

theorem tailTrace_1907279 : CollatzResearch.WordTrace tailWord_1907279 prefixEnd_1907279 652900579484498997227393 := by
  unfold tailWord_1907279
  simp only [CollatzResearch.WordTrace]
  refine ⟨69564180057261395165036891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46376120038174263443357927 69564180057261395165036891)
  ·
    refine ⟨104346270085892092747555337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69564180057261395165036891 104346270085892092747555337)
    ·
      refine ⟨78259702564419069560666503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104346270085892092747555337 78259702564419069560666503)
      ·
        refine ⟨117389553846628604340999755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78259702564419069560666503 117389553846628604340999755)
        ·
          refine ⟨176084330769942906511499633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117389553846628604340999755 176084330769942906511499633)
          ·
            refine ⟨132063248077457179883624725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176084330769942906511499633 132063248077457179883624725)
            ·
              refine ⟨6190464753630805307044909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132063248077457179883624725 6190464753630805307044909)
              ·
                refine ⟨2321424282611551990141841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6190464753630805307044909 2321424282611551990141841)
                ·
                  refine ⟨1741068211958663992606381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321424282611551990141841 1741068211958663992606381)
                  ·
                    refine ⟨652900579484498997227393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741068211958663992606381 652900579484498997227393)
                    ·
                      rfl

theorem cell22_1907279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_1907279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907279 prefixEnd_1907279 := by exact prefixLift 1907279
  have htrace : WordTrace (prefixWord ++ tailWord_1907279) baseStart_1907279 baseEnd_1907279 := by
    simpa [prefixWord, tailWord_1907279, baseEnd_1907279] using wordTrace_append hprefix tailTrace_1907279
  have hstable : (prefixWord ++ tailWord_1907279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907279).length < 2 ^ (prefixWord ++ tailWord_1907279).sum := by decide
  have hdescent : baseEnd_1907279 < baseStart_1907279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907324 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_1907324 : Nat := 118140960795 + 1907324 * 2 ^ 59
def prefixEnd_1907324 : Nat := 4983230072969 + 3 ^ 40 * 1907324 * 2
def baseEnd_1907324 : Nat := 652915983904133879852255

theorem tailTrace_1907324 : CollatzResearch.WordTrace tailWord_1907324 prefixEnd_1907324 652915983904133879852255 := by
  unfold tailWord_1907324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782910671049183925212513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46377214228065578566950017 34782910671049183925212513)
  ·
    refine ⟨26087183003286887943909385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34782910671049183925212513 26087183003286887943909385)
    ·
      refine ⟨19565387252465165957932039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26087183003286887943909385 19565387252465165957932039)
      ·
        refine ⟨29348080878697748936898059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19565387252465165957932039 29348080878697748936898059)
        ·
          refine ⟨44022121318046623405347089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29348080878697748936898059 44022121318046623405347089)
          ·
            refine ⟨33016590988534967554010317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44022121318046623405347089 33016590988534967554010317)
            ·
              refine ⟨12381221620700612832753869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33016590988534967554010317 12381221620700612832753869)
              ·
                refine ⟨4642958107762729812282701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12381221620700612832753869 4642958107762729812282701)
                ·
                  refine ⟨1741109290411023679606013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4642958107762729812282701 1741109290411023679606013)
                  ·
                    refine ⟨652915983904133879852255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741109290411023679606013 652915983904133879852255)
                    ·
                      rfl

theorem cell22_1907324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_1907324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907324 prefixEnd_1907324 := by exact prefixLift 1907324
  have htrace : WordTrace (prefixWord ++ tailWord_1907324) baseStart_1907324 baseEnd_1907324 := by
    simpa [prefixWord, tailWord_1907324, baseEnd_1907324] using wordTrace_append hprefix tailTrace_1907324
  have hstable : (prefixWord ++ tailWord_1907324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907324).length < 2 ^ (prefixWord ++ tailWord_1907324).sum := by decide
  have hdescent : baseEnd_1907324 < baseStart_1907324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907463 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1907463 : Nat := 118140960795 + 1907463 * 2 ^ 59
def prefixEnd_1907463 : Nat := 4983230072969 + 3 ^ 40 * 1907463 * 2
def baseEnd_1907463 : Nat := 652963566444783850626829

theorem tailTrace_1907463 : CollatzResearch.WordTrace tailWord_1907463 prefixEnd_1907463 652963566444783850626829 := by
  unfold tailWord_1907463
  simp only [CollatzResearch.WordTrace]
  refine ⟨69570891088594794589735043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46380594059063196393156695 69570891088594794589735043)
  ·
    refine ⟨104356336632892191884602565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69570891088594794589735043 104356336632892191884602565)
    ·
      refine ⟨19566813118667285978362981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104356336632892191884602565 19566813118667285978362981)
      ·
        refine ⟨3668777459750116120943059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19566813118667285978362981 3668777459750116120943059)
        ·
          refine ⟨5503166189625174181414589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668777459750116120943059 5503166189625174181414589)
          ·
            refine ⟨2063687321109440318030471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5503166189625174181414589 2063687321109440318030471)
            ·
              refine ⟨3095530981664160477045707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063687321109440318030471 3095530981664160477045707)
              ·
                refine ⟨4643296472496240715568561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095530981664160477045707 4643296472496240715568561)
                ·
                  refine ⟨3482472354372180536676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643296472496240715568561 3482472354372180536676421)
                  ·
                    refine ⟨652963566444783850626829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482472354372180536676421 652963566444783850626829)
                    ·
                      rfl

theorem cell22_1907463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1907463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907463 prefixEnd_1907463 := by exact prefixLift 1907463
  have htrace : WordTrace (prefixWord ++ tailWord_1907463) baseStart_1907463 baseEnd_1907463 := by
    simpa [prefixWord, tailWord_1907463, baseEnd_1907463] using wordTrace_append hprefix tailTrace_1907463
  have hstable : (prefixWord ++ tailWord_1907463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907463).length < 2 ^ (prefixWord ++ tailWord_1907463).sum := by decide
  have hdescent : baseEnd_1907463 < baseStart_1907463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907489 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 7]
def baseStart_1907489 : Nat := 118140960795 + 1907489 * 2 ^ 59
def prefixEnd_1907489 : Nat := 4983230072969 + 3 ^ 40 * 1907489 * 2
def baseEnd_1907489 : Nat := 217657488925376149825583

theorem tailTrace_1907489 : CollatzResearch.WordTrace tailWord_1907489 prefixEnd_1907489 217657488925376149825583 := by
  unfold tailWord_1907489
  simp only [CollatzResearch.WordTrace]
  refine ⟨69571839386500601030181521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46381226257667067353454347 69571839386500601030181521)
  ·
    refine ⟨52178879539875450772636141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69571839386500601030181521 52178879539875450772636141)
    ·
      refine ⟨19567079827453294039738553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52178879539875450772636141 19567079827453294039738553)
      ·
        refine ⟨14675309870589970529803915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19567079827453294039738553 14675309870589970529803915)
        ·
          refine ⟨22012964805884955794705873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14675309870589970529803915 22012964805884955794705873)
          ·
            refine ⟨16509723604413716846029405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22012964805884955794705873 16509723604413716846029405)
            ·
              refine ⟨6191146351655143817261027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16509723604413716846029405 6191146351655143817261027)
              ·
                refine ⟨9286719527482715725891541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191146351655143817261027 9286719527482715725891541)
                ·
                  refine ⟨217657488925376149825583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9286719527482715725891541 217657488925376149825583)
                  ·
                    rfl

theorem cell22_1907489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_1907489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907489 prefixEnd_1907489 := by exact prefixLift 1907489
  have htrace : WordTrace (prefixWord ++ tailWord_1907489) baseStart_1907489 baseEnd_1907489 := by
    simpa [prefixWord, tailWord_1907489, baseEnd_1907489] using wordTrace_append hprefix tailTrace_1907489
  have hstable : (prefixWord ++ tailWord_1907489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907489).length < 2 ^ (prefixWord ++ tailWord_1907489).sum := by decide
  have hdescent : baseEnd_1907489 < baseStart_1907489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907493 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_1907493 : Nat := 118140960795 + 1907493 * 2 ^ 59
def prefixEnd_1907493 : Nat := 4983230072969 + 3 ^ 40 * 1907493 * 2
def baseEnd_1907493 : Nat := 652973836057873772376737

theorem tailTrace_1907493 : CollatzResearch.WordTrace tailWord_1907493 prefixEnd_1907493 652973836057873772376737 := by
  unfold tailWord_1907493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69571985278486109713327133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46381323518990739808884755 69571985278486109713327133)
  ·
    refine ⟨26089494479432291142497675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69571985278486109713327133 26089494479432291142497675)
    ·
      refine ⟨39134241719148436713746513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26089494479432291142497675 39134241719148436713746513)
      ·
        refine ⟨29350681289361327535309885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39134241719148436713746513 29350681289361327535309885)
        ·
          refine ⟨11006505483510497825741207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29350681289361327535309885 11006505483510497825741207)
          ·
            refine ⟨16509758225265746738611811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006505483510497825741207 16509758225265746738611811)
            ·
              refine ⟨24764637337898620107917717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16509758225265746738611811 24764637337898620107917717)
              ·
                refine ⟨1160842375213997817558643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24764637337898620107917717 1160842375213997817558643)
                ·
                  refine ⟨1741263562820996726337965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160842375213997817558643 1741263562820996726337965)
                  ·
                    refine ⟨652973836057873772376737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741263562820996726337965 652973836057873772376737)
                    ·
                      rfl

theorem cell22_1907493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_1907493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907493 prefixEnd_1907493 := by exact prefixLift 1907493
  have htrace : WordTrace (prefixWord ++ tailWord_1907493) baseStart_1907493 baseEnd_1907493 := by
    simpa [prefixWord, tailWord_1907493, baseEnd_1907493] using wordTrace_append hprefix tailTrace_1907493
  have hstable : (prefixWord ++ tailWord_1907493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907493).length < 2 ^ (prefixWord ++ tailWord_1907493).sum := by decide
  have hdescent : baseEnd_1907493 < baseStart_1907493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907534 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1907534 : Nat := 118140960795 + 1907534 * 2 ^ 59
def prefixEnd_1907534 : Nat := 4983230072969 + 3 ^ 40 * 1907534 * 2
def baseEnd_1907534 : Nat := 217662623731921110700537

theorem tailTrace_1907534 : CollatzResearch.WordTrace tailWord_1907534 prefixEnd_1907534 217662623731921110700537 := by
  unfold tailWord_1907534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696685083917196714446207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46382320447558382477046437 8696685083917196714446207)
  ·
    refine ⟨13045027625875795071669311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696685083917196714446207 13045027625875795071669311)
    ·
      refine ⟨19567541438813692607503967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13045027625875795071669311 19567541438813692607503967)
      ·
        refine ⟨29351312158220538911255951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19567541438813692607503967 29351312158220538911255951)
        ·
          refine ⟨44026968237330808366883927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29351312158220538911255951 44026968237330808366883927)
          ·
            refine ⟨66040452355996212550325891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44026968237330808366883927 66040452355996212550325891)
            ·
              refine ⟨99060678533994318825488837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66040452355996212550325891 99060678533994318825488837)
              ·
                refine ⟨18573877225123934779779157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99060678533994318825488837 18573877225123934779779157)
                ·
                  refine ⟨217662623731921110700537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18573877225123934779779157 217662623731921110700537)
                  ·
                    rfl

theorem cell22_1907534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1907534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907534 prefixEnd_1907534 := by exact prefixLift 1907534
  have htrace : WordTrace (prefixWord ++ tailWord_1907534) baseStart_1907534 baseEnd_1907534 := by
    simpa [prefixWord, tailWord_1907534, baseEnd_1907534] using wordTrace_append hprefix tailTrace_1907534
  have hstable : (prefixWord ++ tailWord_1907534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907534).length < 2 ^ (prefixWord ++ tailWord_1907534).sum := by decide
  have hdescent : baseEnd_1907534 < baseStart_1907534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907536 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_1907536 : Nat := 118140960795 + 1907536 * 2 ^ 59
def prefixEnd_1907536 : Nat := 4983230072969 + 3 ^ 40 * 1907536 * 2
def baseEnd_1907536 : Nat := 652988555836635993551605

theorem tailTrace_1907536 : CollatzResearch.WordTrace tailWord_1907536 prefixEnd_1907536 652988555836635993551605 := by
  unfold tailWord_1907536
  simp only [CollatzResearch.WordTrace]
  refine ⟨34786776808665164028571231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46382369078220218704761641 34786776808665164028571231)
  ·
    refine ⟨52180165212997746042856847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34786776808665164028571231 52180165212997746042856847)
    ·
      refine ⟨78270247819496619064285271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52180165212997746042856847 78270247819496619064285271)
      ·
        refine ⟨117405371729244928596427907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78270247819496619064285271 117405371729244928596427907)
        ·
          refine ⟨176108057593867392894641861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117405371729244928596427907 176108057593867392894641861)
          ·
            refine ⟨33020260798850136167745349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176108057593867392894641861 33020260798850136167745349)
            ·
              refine ⟨6191298899784400531452253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33020260798850136167745349 6191298899784400531452253)
              ·
                refine ⟨2321737087419150199294595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6191298899784400531452253 2321737087419150199294595)
                ·
                  refine ⟨3482605631128725298941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321737087419150199294595 3482605631128725298941893)
                  ·
                    refine ⟨652988555836635993551605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482605631128725298941893 652988555836635993551605)
                    ·
                      rfl

theorem cell22_1907536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_1907536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907536 prefixEnd_1907536 := by exact prefixLift 1907536
  have htrace : WordTrace (prefixWord ++ tailWord_1907536) baseStart_1907536 baseEnd_1907536 := by
    simpa [prefixWord, tailWord_1907536, baseEnd_1907536] using wordTrace_append hprefix tailTrace_1907536
  have hstable : (prefixWord ++ tailWord_1907536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907536).length < 2 ^ (prefixWord ++ tailWord_1907536).sum := by decide
  have hdescent : baseEnd_1907536 < baseStart_1907536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907579 : List Nat := [1, 1, 1, 1, 1, 5, 4, 8]
def baseStart_1907579 : Nat := 118140960795 + 1907579 * 2 ^ 59
def prefixEnd_1907579 : Nat := 4983230072969 + 3 ^ 40 * 1907579 * 2
def baseEnd_1907579 : Nat := 72555919512822023858497

theorem tailTrace_1907579 : CollatzResearch.WordTrace tailWord_1907579 prefixEnd_1907579 72555919512822023858497 := by
  unfold tailWord_1907579
  simp only [CollatzResearch.WordTrace]
  refine ⟨69575121956174546400957791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46383414637449697600638527 69575121956174546400957791)
  ·
    refine ⟨104362682934261819601436687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69575121956174546400957791 104362682934261819601436687)
    ·
      refine ⟨156544024401392729402155031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104362682934261819601436687 156544024401392729402155031)
      ·
        refine ⟨234816036602089094103232547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156544024401392729402155031 234816036602089094103232547)
        ·
          refine ⟨352224054903133641154848821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234816036602089094103232547 352224054903133641154848821)
          ·
            refine ⟨33021005147168778858267077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352224054903133641154848821 33021005147168778858267077)
            ·
              refine ⟨6191438465094146035925077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33021005147168778858267077 6191438465094146035925077)
              ·
                refine ⟨72555919512822023858497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6191438465094146035925077 72555919512822023858497)
                ·
                  rfl

theorem cell22_1907579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_1907579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907579 prefixEnd_1907579 := by exact prefixLift 1907579
  have htrace : WordTrace (prefixWord ++ tailWord_1907579) baseStart_1907579 baseEnd_1907579 := by
    simpa [prefixWord, tailWord_1907579, baseEnd_1907579] using wordTrace_append hprefix tailTrace_1907579
  have hstable : (prefixWord ++ tailWord_1907579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907579).length < 2 ^ (prefixWord ++ tailWord_1907579).sum := by decide
  have hdescent : baseEnd_1907579 < baseStart_1907579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907581 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1907581 : Nat := 118140960795 + 1907581 * 2 ^ 59
def prefixEnd_1907581 : Nat := 4983230072969 + 3 ^ 40 * 1907581 * 2
def baseEnd_1907581 : Nat := 653003960256270876176467

theorem tailTrace_1907581 : CollatzResearch.WordTrace tailWord_1907581 prefixEnd_1907581 653003960256270876176467 := by
  unfold tailWord_1907581
  simp only [CollatzResearch.WordTrace]
  refine ⟨69575194902167300742530597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46383463268111533828353731 69575194902167300742530597)
  ·
    refine ⟨13045349044156368889224487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69575194902167300742530597 13045349044156368889224487)
    ·
      refine ⟨19568023566234553333836731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13045349044156368889224487 19568023566234553333836731)
      ·
        refine ⟨29352035349351830000755097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19568023566234553333836731 29352035349351830000755097)
        ·
          refine ⟨22014026512013872500566323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29352035349351830000755097 22014026512013872500566323)
          ·
            refine ⟨33021039768020808750849485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22014026512013872500566323 33021039768020808750849485)
            ·
              refine ⟨12382889913007803281568557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33021039768020808750849485 12382889913007803281568557)
              ·
                refine ⟨4643583717377926230588209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12382889913007803281568557 4643583717377926230588209)
                ·
                  refine ⟨3482687788033444672941157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643583717377926230588209 3482687788033444672941157)
                  ·
                    refine ⟨653003960256270876176467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482687788033444672941157 653003960256270876176467)
                    ·
                      rfl

theorem cell22_1907581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1907581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907581 prefixEnd_1907581 := by exact prefixLift 1907581
  have htrace : WordTrace (prefixWord ++ tailWord_1907581) baseStart_1907581 baseEnd_1907581 := by
    simpa [prefixWord, tailWord_1907581, baseEnd_1907581] using wordTrace_append hprefix tailTrace_1907581
  have hstable : (prefixWord ++ tailWord_1907581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907581).length < 2 ^ (prefixWord ++ tailWord_1907581).sum := by decide
  have hdescent : baseEnd_1907581 < baseStart_1907581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907638 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1907638 : Nat := 118140960795 + 1907638 * 2 ^ 59
def prefixEnd_1907638 : Nat := 4983230072969 + 3 ^ 40 * 1907638 * 2
def baseEnd_1907638 : Nat := 653023472521141727501293

theorem tailTrace_1907638 : CollatzResearch.WordTrace tailWord_1907638 prefixEnd_1907638 653023472521141727501293 := by
  unfold tailWord_1907638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348579616435049967334723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46384849241973866318237045 4348579616435049967334723)
  ·
    refine ⟨6522869424652574951002085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4348579616435049967334723 6522869424652574951002085)
    ·
      refine ⟨1223038017122357803312891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6522869424652574951002085 1223038017122357803312891)
      ·
        refine ⟨1834557025683536704969337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223038017122357803312891 1834557025683536704969337)
        ·
          refine ⟨1375917769262652528727003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834557025683536704969337 1375917769262652528727003)
          ·
            refine ⟨2063876653893978793090505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375917769262652528727003 2063876653893978793090505)
            ·
              refine ⟨1547907490420484094817879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063876653893978793090505 1547907490420484094817879)
              ·
                refine ⟨2321861235630726142226819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547907490420484094817879 2321861235630726142226819)
                ·
                  refine ⟨3482791853446089213340229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321861235630726142226819 3482791853446089213340229)
                  ·
                    refine ⟨653023472521141727501293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482791853446089213340229 653023472521141727501293)
                    ·
                      rfl

theorem cell22_1907638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1907638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907638 prefixEnd_1907638 := by exact prefixLift 1907638
  have htrace : WordTrace (prefixWord ++ tailWord_1907638) baseStart_1907638 baseEnd_1907638 := by
    simpa [prefixWord, tailWord_1907638, baseEnd_1907638] using wordTrace_append hprefix tailTrace_1907638
  have hstable : (prefixWord ++ tailWord_1907638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907638).length < 2 ^ (prefixWord ++ tailWord_1907638).sum := by decide
  have hdescent : baseEnd_1907638 < baseStart_1907638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907671 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1907671 : Nat := 118140960795 + 1907671 * 2 ^ 59
def prefixEnd_1907671 : Nat := 4983230072969 + 3 ^ 40 * 1907671 * 2
def baseEnd_1907671 : Nat := 653034769095540641426191

theorem tailTrace_1907671 : CollatzResearch.WordTrace tailWord_1907671 prefixEnd_1907671 653034769095540641426191 := by
  unfold tailWord_1907671
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578477471841246113306867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46385651647894164075537911 69578477471841246113306867)
  ·
    refine ⟨104367716207761869169960301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69578477471841246113306867 104367716207761869169960301)
    ·
      refine ⟨39137893577910700938735113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104367716207761869169960301 39137893577910700938735113)
      ·
        refine ⟨29353420183433025704051335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39137893577910700938735113 29353420183433025704051335)
        ·
          refine ⟨44030130275149538556077003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29353420183433025704051335 44030130275149538556077003)
          ·
            refine ⟨66045195412724307834115505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44030130275149538556077003 66045195412724307834115505)
            ·
              refine ⟨49533896559543230875586629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66045195412724307834115505 49533896559543230875586629)
              ·
                refine ⟨9287605604914355789172493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49533896559543230875586629 9287605604914355789172493)
                ·
                  refine ⟨3482852101842883420939685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9287605604914355789172493 3482852101842883420939685)
                  ·
                    refine ⟨653034769095540641426191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482852101842883420939685 653034769095540641426191)
                    ·
                      rfl

theorem cell22_1907671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1907671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907671 prefixEnd_1907671 := by exact prefixLift 1907671
  have htrace : WordTrace (prefixWord ++ tailWord_1907671) baseStart_1907671 baseEnd_1907671 := by
    simpa [prefixWord, tailWord_1907671, baseEnd_1907671] using wordTrace_append hprefix tailTrace_1907671
  have hstable : (prefixWord ++ tailWord_1907671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907671).length < 2 ^ (prefixWord ++ tailWord_1907671).sum := by decide
  have hdescent : baseEnd_1907671 < baseStart_1907671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907688 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1907688 : Nat := 118140960795 + 1907688 * 2 ^ 59
def prefixEnd_1907688 : Nat := 4983230072969 + 3 ^ 40 * 1907688 * 2
def baseEnd_1907688 : Nat := 653040588542958263751139

theorem tailTrace_1907688 : CollatzResearch.WordTrace tailWord_1907688 prefixEnd_1907688 653040588542958263751139 := by
  unfold tailWord_1907688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34789548756389829008337859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46386065008519772011117145 34789548756389829008337859)
  ·
    refine ⟨52184323134584743512506789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34789548756389829008337859 52184323134584743512506789)
    ·
      refine ⟨9784560587734639408595023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52184323134584743512506789 9784560587734639408595023)
      ·
        refine ⟨14676840881601959112892535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9784560587734639408595023 14676840881601959112892535)
        ·
          refine ⟨22015261322402938669338803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14676840881601959112892535 22015261322402938669338803)
          ·
            refine ⟨33022891983604408004008205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22015261322402938669338803 33022891983604408004008205)
            ·
              refine ⟨12383584493851653001503077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33022891983604408004008205 12383584493851653001503077)
              ·
                refine ⟨2321922092597184937781827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12383584493851653001503077 2321922092597184937781827)
                ·
                  refine ⟨3482883138895777406672741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321922092597184937781827 3482883138895777406672741)
                  ·
                    refine ⟨653040588542958263751139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482883138895777406672741 653040588542958263751139)
                    ·
                      rfl

theorem cell22_1907688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1907688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907688 prefixEnd_1907688 := by exact prefixLift 1907688
  have htrace : WordTrace (prefixWord ++ tailWord_1907688) baseStart_1907688 baseEnd_1907688 := by
    simpa [prefixWord, tailWord_1907688, baseEnd_1907688] using wordTrace_append hprefix tailTrace_1907688
  have hstable : (prefixWord ++ tailWord_1907688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907688).length < 2 ^ (prefixWord ++ tailWord_1907688).sum := by decide
  have hdescent : baseEnd_1907688 < baseStart_1907688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907748 : List Nat := [2, 3, 1, 4, 1, 1, 2, 8]
def baseStart_1907748 : Nat := 118140960795 + 1907748 * 2 ^ 59
def prefixEnd_1907748 : Nat := 4983230072969 + 3 ^ 40 * 1907748 * 2
def baseEnd_1907748 : Nat := 72562347529904234138995

theorem tailTrace_1907748 : CollatzResearch.WordTrace tailWord_1907748 prefixEnd_1907748 72562347529904234138995 := by
  unfold tailWord_1907748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34790642946281144131929949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46387523928374858842573265 34790642946281144131929949)
  ·
    refine ⟨13046491104855429049473731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34790642946281144131929949 13046491104855429049473731)
    ·
      refine ⟨19569736657283143574210597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13046491104855429049473731 19569736657283143574210597)
      ·
        refine ⟨3669325623240589420164487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19569736657283143574210597 3669325623240589420164487)
        ·
          refine ⟨5503988434860884130246731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669325623240589420164487 5503988434860884130246731)
          ·
            refine ⟨8255982652291326195370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503988434860884130246731 8255982652291326195370097)
            ·
              refine ⟨6191986989218494646527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8255982652291326195370097 6191986989218494646527573)
              ·
                refine ⟨72562347529904234138995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6191986989218494646527573 72562347529904234138995)
                ·
                  rfl

theorem cell22_1907748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_1907748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907748 prefixEnd_1907748 := by exact prefixLift 1907748
  have htrace : WordTrace (prefixWord ++ tailWord_1907748) baseStart_1907748 baseEnd_1907748 := by
    simpa [prefixWord, tailWord_1907748, baseEnd_1907748] using wordTrace_append hprefix tailTrace_1907748
  have hstable : (prefixWord ++ tailWord_1907748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907748).length < 2 ^ (prefixWord ++ tailWord_1907748).sum := by decide
  have hdescent : baseEnd_1907748 < baseStart_1907748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907782 : List Nat := [6, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1907782 : Nat := 118140960795 + 1907782 * 2 ^ 59
def prefixEnd_1907782 : Nat := 4983230072969 + 3 ^ 40 * 1907782 * 2
def baseEnd_1907782 : Nat := 72563640740441483544539

theorem tailTrace_1907782 : CollatzResearch.WordTrace tailWord_1907782 prefixEnd_1907782 72563640740441483544539 := by
  unfold tailWord_1907782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174453936701222252206175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46388350649626074713731733 2174453936701222252206175)
  ·
    refine ⟨3261680905051833378309263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174453936701222252206175 3261680905051833378309263)
    ·
      refine ⟨4892521357577750067463895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261680905051833378309263 4892521357577750067463895)
      ·
        refine ⟨7338782036366625101195843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892521357577750067463895 7338782036366625101195843)
        ·
          refine ⟨11008173054549937651793765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338782036366625101195843 11008173054549937651793765)
          ·
            refine ⟨2064032447728113309711331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11008173054549937651793765 2064032447728113309711331)
            ·
              refine ⟨3096048671592169964566997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064032447728113309711331 3096048671592169964566997)
              ·
                refine ⟨72563640740441483544539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3096048671592169964566997 72563640740441483544539)
                ·
                  rfl

theorem cell22_1907782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1907782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907782 prefixEnd_1907782 := by exact prefixLift 1907782
  have htrace : WordTrace (prefixWord ++ tailWord_1907782) baseStart_1907782 baseEnd_1907782 := by
    simpa [prefixWord, tailWord_1907782, baseEnd_1907782] using wordTrace_append hprefix tailTrace_1907782
  have hstable : (prefixWord ++ tailWord_1907782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907782).length < 2 ^ (prefixWord ++ tailWord_1907782).sum := by decide
  have hdescent : baseEnd_1907782 < baseStart_1907782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907793 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 5]
def baseStart_1907793 : Nat := 118140960795 + 1907793 * 2 ^ 59
def prefixEnd_1907793 : Nat := 4983230072969 + 3 ^ 40 * 1907793 * 2
def baseEnd_1907793 : Nat := 217692177396257663291939

theorem tailTrace_1907793 : CollatzResearch.WordTrace tailWord_1907793 prefixEnd_1907793 217692177396257663291939 := by
  unfold tailWord_1907793
  simp only [CollatzResearch.WordTrace]
  refine ⟨69582927177399260949248033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46388618118266173966165355 69582927177399260949248033)
  ·
    refine ⟨52187195383049445711936025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69582927177399260949248033 52187195383049445711936025)
    ·
      refine ⟨39140396537287084283952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52187195383049445711936025 39140396537287084283952019)
      ·
        refine ⟨58710594805930626425928029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39140396537287084283952019 58710594805930626425928029)
        ·
          refine ⟨22016473052223984909723011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58710594805930626425928029 22016473052223984909723011)
          ·
            refine ⟨33024709578335977364584517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22016473052223984909723011 33024709578335977364584517)
            ·
              refine ⟨6192133045937995755859597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33024709578335977364584517 6192133045937995755859597)
              ·
                refine ⟨2322049892226748408447349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6192133045937995755859597 2322049892226748408447349)
                ·
                  refine ⟨217692177396257663291939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2322049892226748408447349 217692177396257663291939)
                  ·
                    rfl

theorem cell22_1907793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_1907793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907793 prefixEnd_1907793 := by exact prefixLift 1907793
  have htrace : WordTrace (prefixWord ++ tailWord_1907793) baseStart_1907793 baseEnd_1907793 := by
    simpa [prefixWord, tailWord_1907793, baseEnd_1907793] using wordTrace_append hprefix tailTrace_1907793
  have hstable : (prefixWord ++ tailWord_1907793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907793).length < 2 ^ (prefixWord ++ tailWord_1907793).sum := by decide
  have hdescent : baseEnd_1907793 < baseStart_1907793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907889 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 4]
def baseStart_1907889 : Nat := 118140960795 + 1907889 * 2 ^ 59
def prefixEnd_1907889 : Nat := 4983230072969 + 3 ^ 40 * 1907889 * 2
def baseEnd_1907889 : Nat := 217703131650220246491841

theorem tailTrace_1907889 : CollatzResearch.WordTrace tailWord_1907889 prefixEnd_1907889 217703131650220246491841 := by
  unfold tailWord_1907889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69586428585051469344742721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46390952390034312896495147 69586428585051469344742721)
  ·
    refine ⟨52189821438788602008557041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69586428585051469344742721 52189821438788602008557041)
    ·
      refine ⟨39142366079091451506417781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52189821438788602008557041 39142366079091451506417781)
      ·
        refine ⟨3669596819914823578726667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39142366079091451506417781 3669596819914823578726667)
        ·
          refine ⟨5504395229872235368090001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669596819914823578726667 5504395229872235368090001)
          ·
            refine ⟨4128296422404176526067501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5504395229872235368090001 4128296422404176526067501)
            ·
              refine ⟨1548111158401566197275313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128296422404176526067501 1548111158401566197275313)
              ·
                refine ⟨1161083368801174647956485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548111158401566197275313 1161083368801174647956485)
                ·
                  refine ⟨217703131650220246491841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161083368801174647956485 217703131650220246491841)
                  ·
                    rfl

theorem cell22_1907889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_1907889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907889 prefixEnd_1907889 := by exact prefixLift 1907889
  have htrace : WordTrace (prefixWord ++ tailWord_1907889) baseStart_1907889 baseEnd_1907889 := by
    simpa [prefixWord, tailWord_1907889, baseEnd_1907889] using wordTrace_append hprefix tailTrace_1907889
  have hstable : (prefixWord ++ tailWord_1907889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907889).length < 2 ^ (prefixWord ++ tailWord_1907889).sum := by decide
  have hdescent : baseEnd_1907889 < baseStart_1907889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907900 : List Nat := [2, 2, 2, 3, 2, 2, 2, 7]
def baseStart_1907900 : Nat := 118140960795 + 1907900 * 2 ^ 59
def prefixEnd_1907900 : Nat := 4983230072969 + 3 ^ 40 * 1907900 * 2
def baseEnd_1907900 : Nat := 72568128941717819716721

theorem tailTrace_1907900 : CollatzResearch.WordTrace tailWord_1907900 prefixEnd_1907900 72568128941717819716721 := by
  unfold tailWord_1907900
  simp only [CollatzResearch.WordTrace]
  refine ⟨34793414894005809111696577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46391219858674412148928769 34793414894005809111696577)
  ·
    refine ⟨26095061170504356833772433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34793414894005809111696577 26095061170504356833772433)
    ·
      refine ⟨19571295877878267625329325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26095061170504356833772433 19571295877878267625329325)
      ·
        refine ⟨7339235954204350359498497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19571295877878267625329325 7339235954204350359498497)
        ·
          refine ⟨5504426965653262769623873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7339235954204350359498497 5504426965653262769623873)
          ·
            refine ⟨4128320224239947077217905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5504426965653262769623873 4128320224239947077217905)
            ·
              refine ⟨3096240168179960307913429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128320224239947077217905 3096240168179960307913429)
              ·
                refine ⟨72568128941717819716721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3096240168179960307913429 72568128941717819716721)
                ·
                  rfl

theorem cell22_1907900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_1907900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907900 prefixEnd_1907900 := by exact prefixLift 1907900
  have htrace : WordTrace (prefixWord ++ tailWord_1907900) baseStart_1907900 baseEnd_1907900 := by
    simpa [prefixWord, tailWord_1907900, baseEnd_1907900] using wordTrace_append hprefix tailTrace_1907900
  have hstable : (prefixWord ++ tailWord_1907900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907900).length < 2 ^ (prefixWord ++ tailWord_1907900).sum := by decide
  have hdescent : baseEnd_1907900 < baseStart_1907900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1907992 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_1907992 : Nat := 118140960795 + 1907992 * 2 ^ 59
def prefixEnd_1907992 : Nat := 4983230072969 + 3 ^ 40 * 1907992 * 2
def baseEnd_1907992 : Nat := 653144653955602804150207

theorem tailTrace_1907992 : CollatzResearch.WordTrace tailWord_1907992 prefixEnd_1907992 653144653955602804150207 := by
  unfold tailWord_1907992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795092651839158967871115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46393456869118878623828153 34795092651839158967871115)
  ·
    refine ⟨52192638977758738451806673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795092651839158967871115 52192638977758738451806673)
    ·
      refine ⟨39144479233319053838855005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52192638977758738451806673 39144479233319053838855005)
      ·
        refine ⟨14679179712494645189570627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39144479233319053838855005 14679179712494645189570627)
        ·
          refine ⟨22018769568741967784355941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679179712494645189570627 22018769568741967784355941)
          ·
            refine ⟨4128519294139118959566739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22018769568741967784355941 4128519294139118959566739)
            ·
              refine ⟨6192778941208678439350109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128519294139118959566739 6192778941208678439350109)
              ·
                refine ⟨2322292102953254414756291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6192778941208678439350109 2322292102953254414756291)
                ·
                  refine ⟨3483438154429881622134437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322292102953254414756291 3483438154429881622134437)
                  ·
                    refine ⟨653144653955602804150207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483438154429881622134437 653144653955602804150207)
                    ·
                      rfl

theorem cell22_1907992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_1907992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1907992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1907992 prefixEnd_1907992 := by exact prefixLift 1907992
  have htrace : WordTrace (prefixWord ++ tailWord_1907992) baseStart_1907992 baseEnd_1907992 := by
    simpa [prefixWord, tailWord_1907992, baseEnd_1907992] using wordTrace_append hprefix tailTrace_1907992
  have hstable : (prefixWord ++ tailWord_1907992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1907992).length < 2 ^ (prefixWord ++ tailWord_1907992).sum := by decide
  have hdescent : baseEnd_1907992 < baseStart_1907992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1907992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908127 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_1908127 : Nat := 118140960795 + 1908127 * 2 ^ 59
def prefixEnd_1908127 : Nat := 4983230072969 + 3 ^ 40 * 1908127 * 2
def baseEnd_1908127 : Nat := 653190867214507452024793

theorem tailTrace_1908127 : CollatzResearch.WordTrace tailWord_1908127 prefixEnd_1908127 653190867214507452024793 := by
  unfold tailWord_1908127
  simp only [CollatzResearch.WordTrace]
  refine ⟨69595109158189235991906635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46396739438792823994604423 69595109158189235991906635)
  ·
    refine ⟨104392663737283853987859953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69595109158189235991906635 104392663737283853987859953)
    ·
      refine ⟨78294497802962890490894965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104392663737283853987859953 78294497802962890490894965)
      ·
        refine ⟨7340109169027770983521403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78294497802962890490894965 7340109169027770983521403)
        ·
          refine ⟨11010163753541656475282105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340109169027770983521403 11010163753541656475282105)
          ·
            refine ⟨8257622815156242356461579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11010163753541656475282105 8257622815156242356461579)
            ·
              refine ⟨12386434222734363534692369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257622815156242356461579 12386434222734363534692369)
              ·
                refine ⟨9289825667050772651019277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386434222734363534692369 9289825667050772651019277)
                ·
                  refine ⟨3483684625144039744132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9289825667050772651019277 3483684625144039744132229)
                  ·
                    refine ⟨653190867214507452024793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483684625144039744132229 653190867214507452024793)
                    ·
                      rfl

theorem cell22_1908127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_1908127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908127 prefixEnd_1908127 := by exact prefixLift 1908127
  have htrace : WordTrace (prefixWord ++ tailWord_1908127) baseStart_1908127 baseEnd_1908127 := by
    simpa [prefixWord, tailWord_1908127, baseEnd_1908127] using wordTrace_append hprefix tailTrace_1908127
  have hstable : (prefixWord ++ tailWord_1908127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908127).length < 2 ^ (prefixWord ++ tailWord_1908127).sum := by decide
  have hdescent : baseEnd_1908127 < baseStart_1908127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908157 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1908157 : Nat := 118140960795 + 1908157 * 2 ^ 59
def prefixEnd_1908157 : Nat := 4983230072969 + 3 ^ 40 * 1908157 * 2
def baseEnd_1908157 : Nat := 653201136827597373774701

theorem tailTrace_1908157 : CollatzResearch.WordTrace tailWord_1908157 prefixEnd_1908157 653201136827597373774701 := by
  unfold tailWord_1908157
  simp only [CollatzResearch.WordTrace]
  refine ⟨69596203348080551115498725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46397468898720367410332483 69596203348080551115498725)
  ·
    refine ⟨13049288127765103334156011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69596203348080551115498725 13049288127765103334156011)
    ·
      refine ⟨19573932191647655001234017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049288127765103334156011 19573932191647655001234017)
      ·
        refine ⟨14680449143735741250925513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19573932191647655001234017 14680449143735741250925513)
        ·
          refine ⟨11010336857801805938194135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14680449143735741250925513 11010336857801805938194135)
          ·
            refine ⟨16515505286702708907291203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010336857801805938194135 16515505286702708907291203)
            ·
              refine ⟨24773257930054063360936805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515505286702708907291203 24773257930054063360936805)
              ·
                refine ⟨4644985861885136880175651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24773257930054063360936805 4644985861885136880175651)
                ·
                  refine ⟨6967478792827705320263477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644985861885136880175651 6967478792827705320263477)
                  ·
                    refine ⟨653201136827597373774701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6967478792827705320263477 653201136827597373774701)
                    ·
                      rfl

theorem cell22_1908157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1908157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908157 prefixEnd_1908157 := by exact prefixLift 1908157
  have htrace : WordTrace (prefixWord ++ tailWord_1908157) baseStart_1908157 baseEnd_1908157 := by
    simpa [prefixWord, tailWord_1908157, baseEnd_1908157] using wordTrace_append hprefix tailTrace_1908157
  have hstable : (prefixWord ++ tailWord_1908157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908157).length < 2 ^ (prefixWord ++ tailWord_1908157).sum := by decide
  have hdescent : baseEnd_1908157 < baseStart_1908157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908191 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 2, 3]
def baseStart_1908191 : Nat := 118140960795 + 1908191 * 2 ^ 59
def prefixEnd_1908191 : Nat := 4983230072969 + 3 ^ 40 * 1908191 * 2
def baseEnd_1908191 : Nat := 653212775722432618424597

theorem tailTrace_1908191 : CollatzResearch.WordTrace tailWord_1908191 prefixEnd_1908191 653212775722432618424597 := by
  unfold tailWord_1908191
  simp only [CollatzResearch.WordTrace]
  refine ⟨69597443429957374922236427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46398295619971583281490951 69597443429957374922236427)
  ·
    refine ⟨104396165144936062383354641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69597443429957374922236427 104396165144936062383354641)
    ·
      refine ⟨78297123858702046787515981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104396165144936062383354641 78297123858702046787515981)
      ·
        refine ⟨29361421447013267545318493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78297123858702046787515981 29361421447013267545318493)
        ·
          refine ⟨11010533042629975329494435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29361421447013267545318493 11010533042629975329494435)
          ·
            refine ⟨16515799563944962994241653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010533042629975329494435 16515799563944962994241653)
            ·
              refine ⟨1548356209119840280710155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16515799563944962994241653 1548356209119840280710155)
              ·
                refine ⟨2322534313679760421065233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548356209119840280710155 2322534313679760421065233)
                ·
                  refine ⟨1741900735259820315798925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322534313679760421065233 1741900735259820315798925)
                  ·
                    refine ⟨653212775722432618424597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741900735259820315798925 653212775722432618424597)
                    ·
                      rfl

theorem cell22_1908191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_1908191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908191 prefixEnd_1908191 := by exact prefixLift 1908191
  have htrace : WordTrace (prefixWord ++ tailWord_1908191) baseStart_1908191 baseEnd_1908191 := by
    simpa [prefixWord, tailWord_1908191, baseEnd_1908191] using wordTrace_append hprefix tailTrace_1908191
  have hstable : (prefixWord ++ tailWord_1908191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908191).length < 2 ^ (prefixWord ++ tailWord_1908191).sum := by decide
  have hdescent : baseEnd_1908191 < baseStart_1908191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908232 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_1908232 : Nat := 118140960795 + 1908232 * 2 ^ 59
def prefixEnd_1908232 : Nat := 4983230072969 + 3 ^ 40 * 1908232 * 2
def baseEnd_1908232 : Nat := 217742270286774059383157

theorem tailTrace_1908232 : CollatzResearch.WordTrace tailWord_1908232 prefixEnd_1908232 217742270286774059383157 := by
  unfold tailWord_1908232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34799469411404419462239475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46399292548539225949652633 34799469411404419462239475)
  ·
    refine ⟨52199204117106629193359213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34799469411404419462239475 52199204117106629193359213)
    ·
      refine ⟨19574701543914985947509705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52199204117106629193359213 19574701543914985947509705)
      ·
        refine ⟨14681026157936239460632279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19574701543914985947509705 14681026157936239460632279)
        ·
          refine ⟨22021539236904359190948419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14681026157936239460632279 22021539236904359190948419)
          ·
            refine ⟨33032308855356538786422629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22021539236904359190948419 33032308855356538786422629)
            ·
              refine ⟨6193557910379351022454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33032308855356538786422629 6193557910379351022454243)
              ·
                refine ⟨9290336865569026533681365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193557910379351022454243 9290336865569026533681365)
                ·
                  refine ⟨217742270286774059383157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9290336865569026533681365 217742270286774059383157)
                  ·
                    rfl

theorem cell22_1908232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_1908232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908232 prefixEnd_1908232 := by exact prefixLift 1908232
  have htrace : WordTrace (prefixWord ++ tailWord_1908232) baseStart_1908232 baseEnd_1908232 := by
    simpa [prefixWord, tailWord_1908232, baseEnd_1908232] using wordTrace_append hprefix tailTrace_1908232
  have hstable : (prefixWord ++ tailWord_1908232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908232).length < 2 ^ (prefixWord ++ tailWord_1908232).sum := by decide
  have hdescent : baseEnd_1908232 < baseStart_1908232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908309 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1908309 : Nat := 118140960795 + 1908309 * 2 ^ 59
def prefixEnd_1908309 : Nat := 4983230072969 + 3 ^ 40 * 1908309 * 2
def baseEnd_1908309 : Nat := 653253169533919643974235

theorem tailTrace_1908309 : CollatzResearch.WordTrace tailWord_1908309 prefixEnd_1908309 653253169533919643974235 := by
  unfold tailWord_1908309
  simp only [CollatzResearch.WordTrace]
  refine ⟨69601747243529881075031981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46401164829019920716687987 69601747243529881075031981)
  ·
    refine ⟨26100655216323705403136993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69601747243529881075031981 26100655216323705403136993)
    ·
      refine ⟨19575491412242779052352745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26100655216323705403136993 19575491412242779052352745)
      ·
        refine ⟨14681618559182084289264559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19575491412242779052352745 14681618559182084289264559)
        ·
          refine ⟨22022427838773126433896839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14681618559182084289264559 22022427838773126433896839)
          ·
            refine ⟨33033641758159689650845259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22022427838773126433896839 33033641758159689650845259)
            ·
              refine ⟨49550462637239534476267889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33033641758159689650845259 49550462637239534476267889)
              ·
                refine ⟨37162846977929650857200917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49550462637239534476267889 37162846977929650857200917)
                ·
                  refine ⟨1742008452090452383931293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37162846977929650857200917 1742008452090452383931293)
                  ·
                    refine ⟨653253169533919643974235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742008452090452383931293 653253169533919643974235)
                    ·
                      rfl

theorem cell22_1908309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1908309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908309 prefixEnd_1908309 := by exact prefixLift 1908309
  have htrace : WordTrace (prefixWord ++ tailWord_1908309) baseStart_1908309 baseEnd_1908309 := by
    simpa [prefixWord, tailWord_1908309, baseEnd_1908309] using wordTrace_append hprefix tailTrace_1908309
  have hstable : (prefixWord ++ tailWord_1908309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908309).length < 2 ^ (prefixWord ++ tailWord_1908309).sum := by decide
  have hdescent : baseEnd_1908309 < baseStart_1908309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908324 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1908324 : Nat := 118140960795 + 1908324 * 2 ^ 59
def prefixEnd_1908324 : Nat := 4983230072969 + 3 ^ 40 * 1908324 * 2
def baseEnd_1908324 : Nat := 653258304340464604849189

theorem tailTrace_1908324 : CollatzResearch.WordTrace tailWord_1908324 prefixEnd_1908324 653258304340464604849189 := by
  unfold tailWord_1908324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801147169237769318414013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46401529558983692424552017 34801147169237769318414013)
  ·
    refine ⟨13050430188464163494405255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34801147169237769318414013 13050430188464163494405255)
    ·
      refine ⟨19575645282696245241607883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050430188464163494405255 19575645282696245241607883)
      ·
        refine ⟨29363467924044367862411825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19575645282696245241607883 29363467924044367862411825)
        ·
          refine ⟨22022600943033275896808869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29363467924044367862411825 22022600943033275896808869)
          ·
            refine ⟨4129237676818739230651663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22022600943033275896808869 4129237676818739230651663)
            ·
              refine ⟨6193856515228108845977495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129237676818739230651663 6193856515228108845977495)
              ·
                refine ⟨9290784772842163268966243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193856515228108845977495 9290784772842163268966243)
                ·
                  refine ⟨13936177159263244903449365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9290784772842163268966243 13936177159263244903449365)
                  ·
                    refine ⟨653258304340464604849189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13936177159263244903449365 653258304340464604849189)
                    ·
                      rfl

theorem cell22_1908324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1908324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908324 prefixEnd_1908324 := by exact prefixLift 1908324
  have htrace : WordTrace (prefixWord ++ tailWord_1908324) baseStart_1908324 baseEnd_1908324 := by
    simpa [prefixWord, tailWord_1908324, baseEnd_1908324] using wordTrace_append hprefix tailTrace_1908324
  have hstable : (prefixWord ++ tailWord_1908324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908324).length < 2 ^ (prefixWord ++ tailWord_1908324).sum := by decide
  have hdescent : baseEnd_1908324 < baseStart_1908324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908328 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_1908328 : Nat := 118140960795 + 1908328 * 2 ^ 59
def prefixEnd_1908328 : Nat := 4983230072969 + 3 ^ 40 * 1908328 * 2
def baseEnd_1908328 : Nat := 217753224540736642583059

theorem tailTrace_1908328 : CollatzResearch.WordTrace tailWord_1908328 prefixEnd_1908328 217753224540736642583059 := by
  unfold tailWord_1908328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801220115230523659986819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46401626820307364879982425 34801220115230523659986819)
  ·
    refine ⟨52201830172845785489980229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801220115230523659986819 52201830172845785489980229)
    ·
      refine ⟨9787843157408584779371293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52201830172845785489980229 9787843157408584779371293)
      ·
        refine ⟨3670441184028219292264235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9787843157408584779371293 3670441184028219292264235)
        ·
          refine ⟨5505661776042328938396353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670441184028219292264235 5505661776042328938396353)
          ·
            refine ⟨4129246332031746703797265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5505661776042328938396353 4129246332031746703797265)
            ·
              refine ⟨3096934749023810027847949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129246332031746703797265 3096934749023810027847949)
              ·
                refine ⟨1161350530883928760442981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3096934749023810027847949 1161350530883928760442981)
                ·
                  refine ⟨217753224540736642583059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161350530883928760442981 217753224540736642583059)
                  ·
                    rfl

theorem cell22_1908328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_1908328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908328 prefixEnd_1908328 := by exact prefixLift 1908328
  have htrace : WordTrace (prefixWord ++ tailWord_1908328) baseStart_1908328 baseEnd_1908328 := by
    simpa [prefixWord, tailWord_1908328, baseEnd_1908328] using wordTrace_append hprefix tailTrace_1908328
  have hstable : (prefixWord ++ tailWord_1908328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908328).length < 2 ^ (prefixWord ++ tailWord_1908328).sum := by decide
  have hdescent : baseEnd_1908328 < baseStart_1908328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908337 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1908337 : Nat := 118140960795 + 1908337 * 2 ^ 59
def prefixEnd_1908337 : Nat := 4983230072969 + 3 ^ 40 * 1908337 * 2
def baseEnd_1908337 : Nat := 653262754506136904274149

theorem tailTrace_1908337 : CollatzResearch.WordTrace tailWord_1908337 prefixEnd_1908337 653262754506136904274149 := by
  unfold tailWord_1908337
  simp only [CollatzResearch.WordTrace]
  refine ⟨69602768487428441857051265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46401845658285627904700843 69602768487428441857051265)
  ·
    refine ⟨52202076365571331392788449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69602768487428441857051265 52202076365571331392788449)
    ·
      refine ⟨39151557274178498544591337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52202076365571331392788449 39151557274178498544591337)
      ·
        refine ⟨29363667955633873908443503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39151557274178498544591337 29363667955633873908443503)
        ·
          refine ⟨44045501933450810862665255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29363667955633873908443503 44045501933450810862665255)
          ·
            refine ⟨66068252900176216293997883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44045501933450810862665255 66068252900176216293997883)
            ·
              refine ⟨99102379350264324440996825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66068252900176216293997883 99102379350264324440996825)
              ·
                refine ⟨74326784512698243330747619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99102379350264324440996825 74326784512698243330747619)
                ·
                  refine ⟨111490176769047364996121429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74326784512698243330747619 111490176769047364996121429)
                  ·
                    refine ⟨653262754506136904274149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111490176769047364996121429 653262754506136904274149)
                    ·
                      rfl

theorem cell22_1908337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1908337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908337 prefixEnd_1908337 := by exact prefixLift 1908337
  have htrace : WordTrace (prefixWord ++ tailWord_1908337) baseStart_1908337 baseEnd_1908337 := by
    simpa [prefixWord, tailWord_1908337, baseEnd_1908337] using wordTrace_append hprefix tailTrace_1908337
  have hstable : (prefixWord ++ tailWord_1908337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908337).length < 2 ^ (prefixWord ++ tailWord_1908337).sum := by decide
  have hdescent : baseEnd_1908337 < baseStart_1908337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908360 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_1908360 : Nat := 118140960795 + 1908360 * 2 ^ 59
def prefixEnd_1908360 : Nat := 4983230072969 + 3 ^ 40 * 1908360 * 2
def baseEnd_1908360 : Nat := 653270627876172510949079

theorem tailTrace_1908360 : CollatzResearch.WordTrace tailWord_1908360 prefixEnd_1908360 653270627876172510949079 := by
  unfold tailWord_1908360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801803683172558392569267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46402404910896744523425689 34801803683172558392569267)
  ·
    refine ⟨52202705524758837588853901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801803683172558392569267 52202705524758837588853901)
    ·
      refine ⟨19576014571784564095820213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52202705524758837588853901 19576014571784564095820213)
      ·
        refine ⟨1835251366104802883983145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19576014571784564095820213 1835251366104802883983145)
        ·
          refine ⟨1376438524578602162987359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835251366104802883983145 1376438524578602162987359)
          ·
            refine ⟨2064657786867903244481039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376438524578602162987359 2064657786867903244481039)
            ·
              refine ⟨3096986680301854866721559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064657786867903244481039 3096986680301854866721559)
              ·
                refine ⟨4645480020452782300082339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096986680301854866721559 4645480020452782300082339)
                ·
                  refine ⟨6968220030679173450123509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645480020452782300082339 6968220030679173450123509)
                  ·
                    refine ⟨653270627876172510949079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6968220030679173450123509 653270627876172510949079)
                    ·
                      rfl

theorem cell22_1908360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_1908360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908360 prefixEnd_1908360 := by exact prefixLift 1908360
  have htrace : WordTrace (prefixWord ++ tailWord_1908360) baseStart_1908360 baseEnd_1908360 := by
    simpa [prefixWord, tailWord_1908360, baseEnd_1908360] using wordTrace_append hprefix tailTrace_1908360
  have hstable : (prefixWord ++ tailWord_1908360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908360).length < 2 ^ (prefixWord ++ tailWord_1908360).sum := by decide
  have hdescent : baseEnd_1908360 < baseStart_1908360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908367 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 11]
def baseStart_1908367 : Nat := 118140960795 + 1908367 * 2 ^ 59
def prefixEnd_1908367 : Nat := 4983230072969 + 3 ^ 40 * 1908367 * 2
def baseEnd_1908367 : Nat := 217757674706408942008019

theorem tailTrace_1908367 : CollatzResearch.WordTrace tailWord_1908367 prefixEnd_1908367 217757674706408942008019 := by
  unfold tailWord_1908367
  simp only [CollatzResearch.WordTrace]
  refine ⟨69603862677319756980643355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46402575118213171320428903 69603862677319756980643355)
  ·
    refine ⟨104405794015979635470965033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69603862677319756980643355 104405794015979635470965033)
    ·
      refine ⟨78304345511984726603223775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104405794015979635470965033 78304345511984726603223775)
      ·
        refine ⟨117456518267977089904835663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78304345511984726603223775 117456518267977089904835663)
        ·
          refine ⟨176184777401965634857253495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117456518267977089904835663 176184777401965634857253495)
          ·
            refine ⟨264277166102948452285880243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176184777401965634857253495 264277166102948452285880243)
            ·
              refine ⟨396415749154422678428820365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264277166102948452285880243 396415749154422678428820365)
              ·
                refine ⟨148655905932908504410807637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396415749154422678428820365 148655905932908504410807637)
                ·
                  refine ⟨217757674706408942008019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 148655905932908504410807637 217757674706408942008019)
                  ·
                    rfl

theorem cell22_1908367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_1908367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908367 prefixEnd_1908367 := by exact prefixLift 1908367
  have htrace : WordTrace (prefixWord ++ tailWord_1908367) baseStart_1908367 baseEnd_1908367 := by
    simpa [prefixWord, tailWord_1908367, baseEnd_1908367] using wordTrace_append hprefix tailTrace_1908367
  have hstable : (prefixWord ++ tailWord_1908367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908367).length < 2 ^ (prefixWord ++ tailWord_1908367).sum := by decide
  have hdescent : baseEnd_1908367 < baseStart_1908367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908384 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_1908384 : Nat := 118140960795 + 1908384 * 2 ^ 59
def prefixEnd_1908384 : Nat := 4983230072969 + 3 ^ 40 * 1908384 * 2
def baseEnd_1908384 : Nat := 217759614522214816116335

theorem tailTrace_1908384 : CollatzResearch.WordTrace tailWord_1908384 prefixEnd_1908384 217759614522214816116335 := by
  unfold tailWord_1908384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34802241359129084442006103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46402988478838779256008137 34802241359129084442006103)
  ·
    refine ⟨52203362038693626663009155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34802241359129084442006103 52203362038693626663009155)
    ·
      refine ⟨78305043058040439994513733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52203362038693626663009155 78305043058040439994513733)
      ·
        refine ⟨14682195573382582498971325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78305043058040439994513733 14682195573382582498971325)
        ·
          refine ⟨5505823340018468437114247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14682195573382582498971325 5505823340018468437114247)
          ·
            refine ⟨8258735010027702655671371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505823340018468437114247 8258735010027702655671371)
            ·
              refine ⟨12388102515041553983507057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258735010027702655671371 12388102515041553983507057)
              ·
                refine ⟨9291076886281165487630293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12388102515041553983507057 9291076886281165487630293)
                ·
                  refine ⟨217759614522214816116335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9291076886281165487630293 217759614522214816116335)
                  ·
                    rfl

theorem cell22_1908384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_1908384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908384 prefixEnd_1908384 := by exact prefixLift 1908384
  have htrace : WordTrace (prefixWord ++ tailWord_1908384) baseStart_1908384 baseEnd_1908384 := by
    simpa [prefixWord, tailWord_1908384, baseEnd_1908384] using wordTrace_append hprefix tailTrace_1908384
  have hstable : (prefixWord ++ tailWord_1908384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908384).length < 2 ^ (prefixWord ++ tailWord_1908384).sum := by decide
  have hdescent : baseEnd_1908384 < baseStart_1908384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908405 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1908405 : Nat := 118140960795 + 1908405 * 2 ^ 59
def prefixEnd_1908405 : Nat := 4983230072969 + 3 ^ 40 * 1908405 * 2
def baseEnd_1908405 : Nat := 653286032295807393573941

theorem tailTrace_1908405 : CollatzResearch.WordTrace tailWord_1908405 prefixEnd_1908405 653286032295807393573941 := by
  unfold tailWord_1908405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69605248651182089470526669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46403499100788059647017779 69605248651182089470526669)
  ·
    refine ⟨26101968244193283551447501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69605248651182089470526669 26101968244193283551447501)
    ·
      refine ⟨9788238091572481331792813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26101968244193283551447501 9788238091572481331792813)
      ·
        refine ⟨3670589284339680499422305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9788238091572481331792813 3670589284339680499422305)
        ·
          refine ⟨2752941963254760374566729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670589284339680499422305 2752941963254760374566729)
          ·
            refine ⟨2064706472441070280925047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752941963254760374566729 2064706472441070280925047)
            ·
              refine ⟨3097059708661605421387571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064706472441070280925047 3097059708661605421387571)
              ·
                refine ⟨4645589562992408132081357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097059708661605421387571 4645589562992408132081357)
                ·
                  refine ⟨1742096086122153049530509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4645589562992408132081357 1742096086122153049530509)
                  ·
                    refine ⟨653286032295807393573941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742096086122153049530509 653286032295807393573941)
                    ·
                      rfl

theorem cell22_1908405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1908405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908405 prefixEnd_1908405 := by exact prefixLift 1908405
  have htrace : WordTrace (prefixWord ++ tailWord_1908405) baseStart_1908405 baseEnd_1908405 := by
    simpa [prefixWord, tailWord_1908405, baseEnd_1908405] using wordTrace_append hprefix tailTrace_1908405
  have hstable : (prefixWord ++ tailWord_1908405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908405).length < 2 ^ (prefixWord ++ tailWord_1908405).sum := by decide
  have hdescent : baseEnd_1908405 < baseStart_1908405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908632 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_1908632 : Nat := 118140960795 + 1908632 * 2 ^ 59
def prefixEnd_1908632 : Nat := 4983230072969 + 3 ^ 40 * 1908632 * 2
def baseEnd_1908632 : Nat := 217787913011618156049415

theorem tailTrace_1908632 : CollatzResearch.WordTrace tailWord_1908632 prefixEnd_1908632 217787913011618156049415 := by
  unfold tailWord_1908632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34806764010679853619520075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46409018680906471492693433 34806764010679853619520075)
  ·
    refine ⟨52210146016019780429280113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34806764010679853619520075 52210146016019780429280113)
    ·
      refine ⟨39157609512014835321960085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52210146016019780429280113 39157609512014835321960085)
      ·
        refine ⟨1835512945875695405716879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39157609512014835321960085 1835512945875695405716879)
        ·
          refine ⟨2753269418813543108575319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835512945875695405716879 2753269418813543108575319)
          ·
            refine ⟨4129904128220314662862979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753269418813543108575319 4129904128220314662862979)
            ·
              refine ⟨6194856192330471994294469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129904128220314662862979 6194856192330471994294469)
              ·
                refine ⟨1161535536061963498930213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6194856192330471994294469 1161535536061963498930213)
                ·
                  refine ⟨217787913011618156049415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161535536061963498930213 217787913011618156049415)
                  ·
                    rfl

theorem cell22_1908632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_1908632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908632 prefixEnd_1908632 := by exact prefixLift 1908632
  have htrace : WordTrace (prefixWord ++ tailWord_1908632) baseStart_1908632 baseEnd_1908632 := by
    simpa [prefixWord, tailWord_1908632, baseEnd_1908632] using wordTrace_append hprefix tailTrace_1908632
  have hstable : (prefixWord ++ tailWord_1908632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908632).length < 2 ^ (prefixWord ++ tailWord_1908632).sum := by decide
  have hdescent : baseEnd_1908632 < baseStart_1908632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908671 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 7]
def baseStart_1908671 : Nat := 118140960795 + 1908671 * 2 ^ 59
def prefixEnd_1908671 : Nat := 4983230072969 + 3 ^ 40 * 1908671 * 2
def baseEnd_1908671 : Nat := 217792363177290455474375

theorem tailTrace_1908671 : CollatzResearch.WordTrace tailWord_1908671 prefixEnd_1908671 217792363177290455474375 := by
  unfold tailWord_1908671
  simp only [CollatzResearch.WordTrace]
  refine ⟨69614950468218416899709867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46409966978812277933139911 69614950468218416899709867)
  ·
    refine ⟨104422425702327625349564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69614950468218416899709867 104422425702327625349564801)
    ·
      refine ⟨78316819276745719012173601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104422425702327625349564801 78316819276745719012173601)
      ·
        refine ⟨58737614457559289259130201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78316819276745719012173601 58737614457559289259130201)
        ·
          refine ⟨44053210843169466944347651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58737614457559289259130201 44053210843169466944347651)
          ·
            refine ⟨66079816264754200416521477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44053210843169466944347651 66079816264754200416521477)
            ·
              refine ⟨12389965549641412578097777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66079816264754200416521477 12389965549641412578097777)
              ·
                refine ⟨9292474162231059433573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12389965549641412578097777 9292474162231059433573333)
                ·
                  refine ⟨217792363177290455474375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9292474162231059433573333 217792363177290455474375)
                  ·
                    rfl

theorem cell22_1908671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_1908671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908671 prefixEnd_1908671 := by exact prefixLift 1908671
  have htrace : WordTrace (prefixWord ++ tailWord_1908671) baseStart_1908671 baseEnd_1908671 := by
    simpa [prefixWord, tailWord_1908671, baseEnd_1908671] using wordTrace_append hprefix tailTrace_1908671
  have hstable : (prefixWord ++ tailWord_1908671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908671).length < 2 ^ (prefixWord ++ tailWord_1908671).sum := by decide
  have hdescent : baseEnd_1908671 < baseStart_1908671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
