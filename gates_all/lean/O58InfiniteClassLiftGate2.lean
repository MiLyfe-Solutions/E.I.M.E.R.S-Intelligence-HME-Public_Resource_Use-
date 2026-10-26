import Lean.Elab.Tactic.Omega

namespace CPOQ

/-- Exact accelerated Collatz step with declared 2-adic valuation. -/
def ExactAccelStep (x y : Int) (a : Nat) : Prop :=
  3 * x + 1 = (2 : Int)^a * y ∧ ∃ z : Int, y = 2*z + 1

def seg33x00 (q : Nat) : Int :=
  (3487011090801549639707 : Int) + (9444732965739290427392 : Int) * (q : Int)

def seg33x01 (q : Nat) : Int :=
  (5230516636202324459561 : Int) + (14167099448608935641088 : Int) * (q : Int)

def seg33x02 (q : Nat) : Int :=
  (3922887477151743344671 : Int) + (10625324586456701730816 : Int) * (q : Int)

def seg33x03 (q : Nat) : Int :=
  (5884331215727615017007 : Int) + (15937986879685052596224 : Int) * (q : Int)

def seg33x04 (q : Nat) : Int :=
  (8826496823591422525511 : Int) + (23906980319527578894336 : Int) * (q : Int)

def seg33x05 (q : Nat) : Int :=
  (13239745235387133788267 : Int) + (35860470479291368341504 : Int) * (q : Int)

def seg33x06 (q : Nat) : Int :=
  (19859617853080700682401 : Int) + (53790705718937052512256 : Int) * (q : Int)

def seg33x07 (q : Nat) : Int :=
  (14894713389810525511801 : Int) + (40343029289202789384192 : Int) * (q : Int)

def seg33x08 (q : Nat) : Int :=
  (11171035042357894133851 : Int) + (30257271966902092038144 : Int) * (q : Int)

def seg33x09 (q : Nat) : Int :=
  (16756552563536841200777 : Int) + (45385907950353138057216 : Int) * (q : Int)

def seg33x10 (q : Nat) : Int :=
  (12567414422652630900583 : Int) + (34039430962764853542912 : Int) * (q : Int)

def seg33x11 (q : Nat) : Int :=
  (18851121633978946350875 : Int) + (51059146444147280314368 : Int) * (q : Int)

def seg33x12 (q : Nat) : Int :=
  (28276682450968419526313 : Int) + (76588719666220920471552 : Int) * (q : Int)

def seg33x13 (q : Nat) : Int :=
  (21207511838226314644735 : Int) + (57441539749665690353664 : Int) * (q : Int)

def seg33x14 (q : Nat) : Int :=
  (31811267757339471967103 : Int) + (86162309624498535530496 : Int) * (q : Int)

def seg33x15 (q : Nat) : Int :=
  (47716901636009207950655 : Int) + (129243464436747803295744 : Int) * (q : Int)

def seg33x16 (q : Nat) : Int :=
  (71575352454013811925983 : Int) + (193865196655121704943616 : Int) * (q : Int)

def seg33x17 (q : Nat) : Int :=
  (107363028681020717888975 : Int) + (290797794982682557415424 : Int) * (q : Int)

def seg33x18 (q : Nat) : Int :=
  (161044543021531076833463 : Int) + (436196692474023836123136 : Int) * (q : Int)

def seg33x19 (q : Nat) : Int :=
  (241566814532296615250195 : Int) + (654295038711035754184704 : Int) * (q : Int)

def seg33x20 (q : Nat) : Int :=
  (362350221798444922875293 : Int) + (981442558066553631277056 : Int) * (q : Int)

def seg33x21 (q : Nat) : Int :=
  (135881333174416846078235 : Int) + (368040959274957611728896 : Int) * (q : Int)

def seg33x22 (q : Nat) : Int :=
  (203821999761625269117353 : Int) + (552061438912436417593344 : Int) * (q : Int)

def seg33x23 (q : Nat) : Int :=
  (152866499821218951838015 : Int) + (414046079184327313195008 : Int) * (q : Int)

def seg33x24 (q : Nat) : Int :=
  (229299749731828427757023 : Int) + (621069118776490969792512 : Int) * (q : Int)

def seg33x25 (q : Nat) : Int :=
  (343949624597742641635535 : Int) + (931603678164736454688768 : Int) * (q : Int)

def seg33x26 (q : Nat) : Int :=
  (515924436896613962453303 : Int) + (1397405517247104682033152 : Int) * (q : Int)

def seg33x27 (q : Nat) : Int :=
  (773886655344920943679955 : Int) + (2096108275870657023049728 : Int) * (q : Int)

def seg33x28 (q : Nat) : Int :=
  (1160829983017381415519933 : Int) + (3144162413805985534574592 : Int) * (q : Int)

def seg33x29 (q : Nat) : Int :=
  (435311243631518030819975 : Int) + (1179060905177244575465472 : Int) * (q : Int)

def seg33x30 (q : Nat) : Int :=
  (652966865447277046229963 : Int) + (1768591357765866863198208 : Int) * (q : Int)

def seg33x31 (q : Nat) : Int :=
  (979450298170915569344945 : Int) + (2652887036648800294797312 : Int) * (q : Int)

def seg33x32 (q : Nat) : Int :=
  (734587723628186677008709 : Int) + (1989665277486600221097984 : Int) * (q : Int)

def seg33x33 (q : Nat) : Int :=
  (137735198180285001939133 : Int) + (373062239528737541455872 : Int) * (q : Int)

def seg33x34 (q : Nat) : Int :=
  (51650699317606875727175 : Int) + (139898339823276578045952 : Int) * (q : Int)

def seg33x35 (q : Nat) : Int :=
  (77476048976410313590763 : Int) + (209847509734914867068928 : Int) * (q : Int)

def seg33x36 (q : Nat) : Int :=
  (116214073464615470386145 : Int) + (314771264602372300603392 : Int) * (q : Int)

def seg33x37 (q : Nat) : Int :=
  (87160555098461602789609 : Int) + (236078448451779225452544 : Int) * (q : Int)

def seg33x38 (q : Nat) : Int :=
  (65370416323846202092207 : Int) + (177058836338834419089408 : Int) * (q : Int)

def seg33x39 (q : Nat) : Int :=
  (98055624485769303138311 : Int) + (265588254508251628634112 : Int) * (q : Int)

def seg33x40 (q : Nat) : Int :=
  (147083436728653954707467 : Int) + (398382381762377442951168 : Int) * (q : Int)

def seg33x41 (q : Nat) : Int :=
  (220625155092980932061201 : Int) + (597573572643566164426752 : Int) * (q : Int)

def seg33x42 (q : Nat) : Int :=
  (165468866319735699045901 : Int) + (448180179482674623320064 : Int) * (q : Int)

def seg33x43 (q : Nat) : Int :=
  (62050824869900887142213 : Int) + (168067567306002983745024 : Int) * (q : Int)

def seg33x44 (q : Nat) : Int :=
  (11634529663106416339165 : Int) + (31512668869875559452192 : Int) * (q : Int)

def seg33x45 (q : Nat) : Int :=
  (4362948623664906127187 : Int) + (11817250826203334794572 : Int) * (q : Int)

def seg33x46 (q : Nat) : Int :=
  (6544422935497359190781 : Int) + (17725876239305002191858 : Int) * (q : Int)

theorem seg33_step_01 (q : Nat) :
    ExactAccelStep (seg33x00 q) (seg33x01 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x00, seg33x01]
    omega
  · refine ⟨(2615258318101162229780 : Int) + (7083549724304467820544 : Int) * (q : Int), ?_⟩
    simp [seg33x01]
    omega

theorem seg33_step_02 (q : Nat) :
    ExactAccelStep (seg33x01 q) (seg33x02 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x01, seg33x02]
    omega
  · refine ⟨(1961443738575871672335 : Int) + (5312662293228350865408 : Int) * (q : Int), ?_⟩
    simp [seg33x02]
    omega

theorem seg33_step_03 (q : Nat) :
    ExactAccelStep (seg33x02 q) (seg33x03 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x02, seg33x03]
    omega
  · refine ⟨(2942165607863807508503 : Int) + (7968993439842526298112 : Int) * (q : Int), ?_⟩
    simp [seg33x03]
    omega

theorem seg33_step_04 (q : Nat) :
    ExactAccelStep (seg33x03 q) (seg33x04 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x03, seg33x04]
    omega
  · refine ⟨(4413248411795711262755 : Int) + (11953490159763789447168 : Int) * (q : Int), ?_⟩
    simp [seg33x04]
    omega

theorem seg33_step_05 (q : Nat) :
    ExactAccelStep (seg33x04 q) (seg33x05 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x04, seg33x05]
    omega
  · refine ⟨(6619872617693566894133 : Int) + (17930235239645684170752 : Int) * (q : Int), ?_⟩
    simp [seg33x05]
    omega

theorem seg33_step_06 (q : Nat) :
    ExactAccelStep (seg33x05 q) (seg33x06 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x05, seg33x06]
    omega
  · refine ⟨(9929808926540350341200 : Int) + (26895352859468526256128 : Int) * (q : Int), ?_⟩
    simp [seg33x06]
    omega

theorem seg33_step_07 (q : Nat) :
    ExactAccelStep (seg33x06 q) (seg33x07 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x06, seg33x07]
    omega
  · refine ⟨(7447356694905262755900 : Int) + (20171514644601394692096 : Int) * (q : Int), ?_⟩
    simp [seg33x07]
    omega

theorem seg33_step_08 (q : Nat) :
    ExactAccelStep (seg33x07 q) (seg33x08 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x07, seg33x08]
    omega
  · refine ⟨(5585517521178947066925 : Int) + (15128635983451046019072 : Int) * (q : Int), ?_⟩
    simp [seg33x08]
    omega

theorem seg33_step_09 (q : Nat) :
    ExactAccelStep (seg33x08 q) (seg33x09 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x08, seg33x09]
    omega
  · refine ⟨(8378276281768420600388 : Int) + (22692953975176569028608 : Int) * (q : Int), ?_⟩
    simp [seg33x09]
    omega

theorem seg33_step_10 (q : Nat) :
    ExactAccelStep (seg33x09 q) (seg33x10 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x09, seg33x10]
    omega
  · refine ⟨(6283707211326315450291 : Int) + (17019715481382426771456 : Int) * (q : Int), ?_⟩
    simp [seg33x10]
    omega

theorem seg33_step_11 (q : Nat) :
    ExactAccelStep (seg33x10 q) (seg33x11 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x10, seg33x11]
    omega
  · refine ⟨(9425560816989473175437 : Int) + (25529573222073640157184 : Int) * (q : Int), ?_⟩
    simp [seg33x11]
    omega

theorem seg33_step_12 (q : Nat) :
    ExactAccelStep (seg33x11 q) (seg33x12 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x11, seg33x12]
    omega
  · refine ⟨(14138341225484209763156 : Int) + (38294359833110460235776 : Int) * (q : Int), ?_⟩
    simp [seg33x12]
    omega

theorem seg33_step_13 (q : Nat) :
    ExactAccelStep (seg33x12 q) (seg33x13 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x12, seg33x13]
    omega
  · refine ⟨(10603755919113157322367 : Int) + (28720769874832845176832 : Int) * (q : Int), ?_⟩
    simp [seg33x13]
    omega

theorem seg33_step_14 (q : Nat) :
    ExactAccelStep (seg33x13 q) (seg33x14 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x13, seg33x14]
    omega
  · refine ⟨(15905633878669735983551 : Int) + (43081154812249267765248 : Int) * (q : Int), ?_⟩
    simp [seg33x14]
    omega

theorem seg33_step_15 (q : Nat) :
    ExactAccelStep (seg33x14 q) (seg33x15 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x14, seg33x15]
    omega
  · refine ⟨(23858450818004603975327 : Int) + (64621732218373901647872 : Int) * (q : Int), ?_⟩
    simp [seg33x15]
    omega

theorem seg33_step_16 (q : Nat) :
    ExactAccelStep (seg33x15 q) (seg33x16 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x15, seg33x16]
    omega
  · refine ⟨(35787676227006905962991 : Int) + (96932598327560852471808 : Int) * (q : Int), ?_⟩
    simp [seg33x16]
    omega

theorem seg33_step_17 (q : Nat) :
    ExactAccelStep (seg33x16 q) (seg33x17 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x16, seg33x17]
    omega
  · refine ⟨(53681514340510358944487 : Int) + (145398897491341278707712 : Int) * (q : Int), ?_⟩
    simp [seg33x17]
    omega

theorem seg33_step_18 (q : Nat) :
    ExactAccelStep (seg33x17 q) (seg33x18 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x17, seg33x18]
    omega
  · refine ⟨(80522271510765538416731 : Int) + (218098346237011918061568 : Int) * (q : Int), ?_⟩
    simp [seg33x18]
    omega

theorem seg33_step_19 (q : Nat) :
    ExactAccelStep (seg33x18 q) (seg33x19 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x18, seg33x19]
    omega
  · refine ⟨(120783407266148307625097 : Int) + (327147519355517877092352 : Int) * (q : Int), ?_⟩
    simp [seg33x19]
    omega

theorem seg33_step_20 (q : Nat) :
    ExactAccelStep (seg33x19 q) (seg33x20 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x19, seg33x20]
    omega
  · refine ⟨(181175110899222461437646 : Int) + (490721279033276815638528 : Int) * (q : Int), ?_⟩
    simp [seg33x20]
    omega

theorem seg33_step_21 (q : Nat) :
    ExactAccelStep (seg33x20 q) (seg33x21 q) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x20, seg33x21]
    omega
  · refine ⟨(67940666587208423039117 : Int) + (184020479637478805864448 : Int) * (q : Int), ?_⟩
    simp [seg33x21]
    omega

theorem seg33_step_22 (q : Nat) :
    ExactAccelStep (seg33x21 q) (seg33x22 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x21, seg33x22]
    omega
  · refine ⟨(101910999880812634558676 : Int) + (276030719456218208796672 : Int) * (q : Int), ?_⟩
    simp [seg33x22]
    omega

theorem seg33_step_23 (q : Nat) :
    ExactAccelStep (seg33x22 q) (seg33x23 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x22, seg33x23]
    omega
  · refine ⟨(76433249910609475919007 : Int) + (207023039592163656597504 : Int) * (q : Int), ?_⟩
    simp [seg33x23]
    omega

theorem seg33_step_24 (q : Nat) :
    ExactAccelStep (seg33x23 q) (seg33x24 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x23, seg33x24]
    omega
  · refine ⟨(114649874865914213878511 : Int) + (310534559388245484896256 : Int) * (q : Int), ?_⟩
    simp [seg33x24]
    omega

theorem seg33_step_25 (q : Nat) :
    ExactAccelStep (seg33x24 q) (seg33x25 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x24, seg33x25]
    omega
  · refine ⟨(171974812298871320817767 : Int) + (465801839082368227344384 : Int) * (q : Int), ?_⟩
    simp [seg33x25]
    omega

theorem seg33_step_26 (q : Nat) :
    ExactAccelStep (seg33x25 q) (seg33x26 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x25, seg33x26]
    omega
  · refine ⟨(257962218448306981226651 : Int) + (698702758623552341016576 : Int) * (q : Int), ?_⟩
    simp [seg33x26]
    omega

theorem seg33_step_27 (q : Nat) :
    ExactAccelStep (seg33x26 q) (seg33x27 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x26, seg33x27]
    omega
  · refine ⟨(386943327672460471839977 : Int) + (1048054137935328511524864 : Int) * (q : Int), ?_⟩
    simp [seg33x27]
    omega

theorem seg33_step_28 (q : Nat) :
    ExactAccelStep (seg33x27 q) (seg33x28 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x27, seg33x28]
    omega
  · refine ⟨(580414991508690707759966 : Int) + (1572081206902992767287296 : Int) * (q : Int), ?_⟩
    simp [seg33x28]
    omega

theorem seg33_step_29 (q : Nat) :
    ExactAccelStep (seg33x28 q) (seg33x29 q) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x28, seg33x29]
    omega
  · refine ⟨(217655621815759015409987 : Int) + (589530452588622287732736 : Int) * (q : Int), ?_⟩
    simp [seg33x29]
    omega

theorem seg33_step_30 (q : Nat) :
    ExactAccelStep (seg33x29 q) (seg33x30 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x29, seg33x30]
    omega
  · refine ⟨(326483432723638523114981 : Int) + (884295678882933431599104 : Int) * (q : Int), ?_⟩
    simp [seg33x30]
    omega

theorem seg33_step_31 (q : Nat) :
    ExactAccelStep (seg33x30 q) (seg33x31 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x30, seg33x31]
    omega
  · refine ⟨(489725149085457784672472 : Int) + (1326443518324400147398656 : Int) * (q : Int), ?_⟩
    simp [seg33x31]
    omega

theorem seg33_step_32 (q : Nat) :
    ExactAccelStep (seg33x31 q) (seg33x32 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x31, seg33x32]
    omega
  · refine ⟨(367293861814093338504354 : Int) + (994832638743300110548992 : Int) * (q : Int), ?_⟩
    simp [seg33x32]
    omega

theorem seg33_step_33 (q : Nat) :
    ExactAccelStep (seg33x32 q) (seg33x33 q) 4 := by
  constructor
  · simp [ExactAccelStep, seg33x32, seg33x33]
    omega
  · refine ⟨(68867599090142500969566 : Int) + (186531119764368770727936 : Int) * (q : Int), ?_⟩
    simp [seg33x33]
    omega

theorem seg33_step_34 (q : Nat) :
    ExactAccelStep (seg33x33 q) (seg33x34 q) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x33, seg33x34]
    omega
  · refine ⟨(25825349658803437863587 : Int) + (69949169911638289022976 : Int) * (q : Int), ?_⟩
    simp [seg33x34]
    omega

theorem seg33_step_35 (q : Nat) :
    ExactAccelStep (seg33x34 q) (seg33x35 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x34, seg33x35]
    omega
  · refine ⟨(38738024488205156795381 : Int) + (104923754867457433534464 : Int) * (q : Int), ?_⟩
    simp [seg33x35]
    omega

theorem seg33_step_36 (q : Nat) :
    ExactAccelStep (seg33x35 q) (seg33x36 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x35, seg33x36]
    omega
  · refine ⟨(58107036732307735193072 : Int) + (157385632301186150301696 : Int) * (q : Int), ?_⟩
    simp [seg33x36]
    omega

theorem seg33_step_37 (q : Nat) :
    ExactAccelStep (seg33x36 q) (seg33x37 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x36, seg33x37]
    omega
  · refine ⟨(43580277549230801394804 : Int) + (118039224225889612726272 : Int) * (q : Int), ?_⟩
    simp [seg33x37]
    omega

theorem seg33_step_38 (q : Nat) :
    ExactAccelStep (seg33x37 q) (seg33x38 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x37, seg33x38]
    omega
  · refine ⟨(32685208161923101046103 : Int) + (88529418169417209544704 : Int) * (q : Int), ?_⟩
    simp [seg33x38]
    omega

theorem seg33_step_39 (q : Nat) :
    ExactAccelStep (seg33x38 q) (seg33x39 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x38, seg33x39]
    omega
  · refine ⟨(49027812242884651569155 : Int) + (132794127254125814317056 : Int) * (q : Int), ?_⟩
    simp [seg33x39]
    omega

theorem seg33_step_40 (q : Nat) :
    ExactAccelStep (seg33x39 q) (seg33x40 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x39, seg33x40]
    omega
  · refine ⟨(73541718364326977353733 : Int) + (199191190881188721475584 : Int) * (q : Int), ?_⟩
    simp [seg33x40]
    omega

theorem seg33_step_41 (q : Nat) :
    ExactAccelStep (seg33x40 q) (seg33x41 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x40, seg33x41]
    omega
  · refine ⟨(110312577546490466030600 : Int) + (298786786321783082213376 : Int) * (q : Int), ?_⟩
    simp [seg33x41]
    omega

theorem seg33_step_42 (q : Nat) :
    ExactAccelStep (seg33x41 q) (seg33x42 q) 2 := by
  constructor
  · simp [ExactAccelStep, seg33x41, seg33x42]
    omega
  · refine ⟨(82734433159867849522950 : Int) + (224090089741337311660032 : Int) * (q : Int), ?_⟩
    simp [seg33x42]
    omega

theorem seg33_step_43 (q : Nat) :
    ExactAccelStep (seg33x42 q) (seg33x43 q) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x42, seg33x43]
    omega
  · refine ⟨(31025412434950443571106 : Int) + (84033783653001491872512 : Int) * (q : Int), ?_⟩
    simp [seg33x43]
    omega

theorem seg33_step_44 (q : Nat) :
    ExactAccelStep (seg33x43 q) (seg33x44 q) 4 := by
  constructor
  · simp [ExactAccelStep, seg33x43, seg33x44]
    omega
  · refine ⟨(5817264831553208169582 : Int) + (15756334434937779726096 : Int) * (q : Int), ?_⟩
    simp [seg33x44]
    omega

theorem seg33_step_45 (q : Nat) :
    ExactAccelStep (seg33x44 q) (seg33x45 q) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x44, seg33x45]
    omega
  · refine ⟨(2181474311832453063593 : Int) + (5908625413101667397286 : Int) * (q : Int), ?_⟩
    simp [seg33x45]
    omega

theorem seg33_step_46 (q : Nat) :
    ExactAccelStep (seg33x45 q) (seg33x46 q) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x45, seg33x46]
    omega
  · refine ⟨(3272211467748679595390 : Int) + (8862938119652501095929 : Int) * (q : Int), ?_⟩
    simp [seg33x46]
    omega

/-- Every member of the mod-2^73 Segment-33 source cylinder has the same first 46 exact accelerated valuations. -/
theorem o58_segment33_full_cylinder_prefix46 (q : Nat) :
    ExactAccelStep (seg33x00 q) (seg33x01 q) 1 ∧
      ExactAccelStep (seg33x01 q) (seg33x02 q) 2 ∧
      ExactAccelStep (seg33x02 q) (seg33x03 q) 1 ∧
      ExactAccelStep (seg33x03 q) (seg33x04 q) 1 ∧
      ExactAccelStep (seg33x04 q) (seg33x05 q) 1 ∧
      ExactAccelStep (seg33x05 q) (seg33x06 q) 1 ∧
      ExactAccelStep (seg33x06 q) (seg33x07 q) 2 ∧
      ExactAccelStep (seg33x07 q) (seg33x08 q) 2 ∧
      ExactAccelStep (seg33x08 q) (seg33x09 q) 1 ∧
      ExactAccelStep (seg33x09 q) (seg33x10 q) 2 ∧
      ExactAccelStep (seg33x10 q) (seg33x11 q) 1 ∧
      ExactAccelStep (seg33x11 q) (seg33x12 q) 1 ∧
      ExactAccelStep (seg33x12 q) (seg33x13 q) 2 ∧
      ExactAccelStep (seg33x13 q) (seg33x14 q) 1 ∧
      ExactAccelStep (seg33x14 q) (seg33x15 q) 1 ∧
      ExactAccelStep (seg33x15 q) (seg33x16 q) 1 ∧
      ExactAccelStep (seg33x16 q) (seg33x17 q) 1 ∧
      ExactAccelStep (seg33x17 q) (seg33x18 q) 1 ∧
      ExactAccelStep (seg33x18 q) (seg33x19 q) 1 ∧
      ExactAccelStep (seg33x19 q) (seg33x20 q) 1 ∧
      ExactAccelStep (seg33x20 q) (seg33x21 q) 3 ∧
      ExactAccelStep (seg33x21 q) (seg33x22 q) 1 ∧
      ExactAccelStep (seg33x22 q) (seg33x23 q) 2 ∧
      ExactAccelStep (seg33x23 q) (seg33x24 q) 1 ∧
      ExactAccelStep (seg33x24 q) (seg33x25 q) 1 ∧
      ExactAccelStep (seg33x25 q) (seg33x26 q) 1 ∧
      ExactAccelStep (seg33x26 q) (seg33x27 q) 1 ∧
      ExactAccelStep (seg33x27 q) (seg33x28 q) 1 ∧
      ExactAccelStep (seg33x28 q) (seg33x29 q) 3 ∧
      ExactAccelStep (seg33x29 q) (seg33x30 q) 1 ∧
      ExactAccelStep (seg33x30 q) (seg33x31 q) 1 ∧
      ExactAccelStep (seg33x31 q) (seg33x32 q) 2 ∧
      ExactAccelStep (seg33x32 q) (seg33x33 q) 4 ∧
      ExactAccelStep (seg33x33 q) (seg33x34 q) 3 ∧
      ExactAccelStep (seg33x34 q) (seg33x35 q) 1 ∧
      ExactAccelStep (seg33x35 q) (seg33x36 q) 1 ∧
      ExactAccelStep (seg33x36 q) (seg33x37 q) 2 ∧
      ExactAccelStep (seg33x37 q) (seg33x38 q) 2 ∧
      ExactAccelStep (seg33x38 q) (seg33x39 q) 1 ∧
      ExactAccelStep (seg33x39 q) (seg33x40 q) 1 ∧
      ExactAccelStep (seg33x40 q) (seg33x41 q) 1 ∧
      ExactAccelStep (seg33x41 q) (seg33x42 q) 2 ∧
      ExactAccelStep (seg33x42 q) (seg33x43 q) 3 ∧
      ExactAccelStep (seg33x43 q) (seg33x44 q) 4 ∧
      ExactAccelStep (seg33x44 q) (seg33x45 q) 3 ∧
      ExactAccelStep (seg33x45 q) (seg33x46 q) 1 := by
  constructor
  · exact seg33_step_01 q
  constructor
  · exact seg33_step_02 q
  constructor
  · exact seg33_step_03 q
  constructor
  · exact seg33_step_04 q
  constructor
  · exact seg33_step_05 q
  constructor
  · exact seg33_step_06 q
  constructor
  · exact seg33_step_07 q
  constructor
  · exact seg33_step_08 q
  constructor
  · exact seg33_step_09 q
  constructor
  · exact seg33_step_10 q
  constructor
  · exact seg33_step_11 q
  constructor
  · exact seg33_step_12 q
  constructor
  · exact seg33_step_13 q
  constructor
  · exact seg33_step_14 q
  constructor
  · exact seg33_step_15 q
  constructor
  · exact seg33_step_16 q
  constructor
  · exact seg33_step_17 q
  constructor
  · exact seg33_step_18 q
  constructor
  · exact seg33_step_19 q
  constructor
  · exact seg33_step_20 q
  constructor
  · exact seg33_step_21 q
  constructor
  · exact seg33_step_22 q
  constructor
  · exact seg33_step_23 q
  constructor
  · exact seg33_step_24 q
  constructor
  · exact seg33_step_25 q
  constructor
  · exact seg33_step_26 q
  constructor
  · exact seg33_step_27 q
  constructor
  · exact seg33_step_28 q
  constructor
  · exact seg33_step_29 q
  constructor
  · exact seg33_step_30 q
  constructor
  · exact seg33_step_31 q
  constructor
  · exact seg33_step_32 q
  constructor
  · exact seg33_step_33 q
  constructor
  · exact seg33_step_34 q
  constructor
  · exact seg33_step_35 q
  constructor
  · exact seg33_step_36 q
  constructor
  · exact seg33_step_37 q
  constructor
  · exact seg33_step_38 q
  constructor
  · exact seg33_step_39 q
  constructor
  · exact seg33_step_40 q
  constructor
  · exact seg33_step_41 q
  constructor
  · exact seg33_step_42 q
  constructor
  · exact seg33_step_43 q
  constructor
  · exact seg33_step_44 q
  constructor
  · exact seg33_step_45 q
  exact seg33_step_46 q

theorem o58_segment33_step47_q0 :
    ExactAccelStep (seg33x46 0) (2454158600811509696543 : Int) 3 := by
  constructor
  · simp [ExactAccelStep, seg33x46]
  · refine ⟨(1227079300405754848271 : Int), ?_⟩
    omega

theorem o58_segment33_step47_q1 :
    ExactAccelStep (seg33x46 1) (36405448762203542073959 : Int) 1 := by
  constructor
  · simp [ExactAccelStep, seg33x46]
  · refine ⟨(18202724381101771036979 : Int), ?_⟩
    omega

/-- The 73-bit cylinder cannot have one fixed step-47 valuation: q=0 has valuation 3 while q=1 has valuation 1. -/
theorem o58_segment33_precision73_not_step47_uniform :
    (∃ y : Int, ExactAccelStep (seg33x46 0) y 3) ∧
    (∃ y : Int, ExactAccelStep (seg33x46 1) y 1) := by
  exact ⟨⟨(2454158600811509696543 : Int), o58_segment33_step47_q0⟩,
         ⟨(36405448762203542073959 : Int), o58_segment33_step47_q1⟩⟩

end CPOQ
