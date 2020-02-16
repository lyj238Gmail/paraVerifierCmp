



ruleset  j : NODE do
invariant "1"
Cache[j].State = S -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "2"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd = Empty);

endruleset;




ruleset  i : NODE do
invariant "3"
Chan2[i].Cmd = Empty & InvSet[i] = true -> Cache[i].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "4"
i != j -> 
  (Chan3[j].Cmd = InvAck -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "5"
i != j -> 
  (InvSet[j] = true -> Cache[i].State != E);

endruleset;




ruleset  j : NODE do
invariant "6"
Cache[j].State = S -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE do
invariant "7"
Cache[i].State = E -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  j : NODE do
invariant "8"
Chan2[j].Cmd = GntE -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "9"
i != j -> 
  (Cache[i].State = E -> Cache[j].State != S);

endruleset;




ruleset  i : NODE do
invariant "10"
Chan2[i].Cmd = GntS -> Chan2[i].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "11"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan3[j].Cmd != InvAck);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "12"
i != j -> 
  (InvSet[i] = true & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "13"
i != j -> 
  (InvSet[j] = true & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);

endruleset;




ruleset  i : NODE do
invariant "14"
Cache[i].State = E -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "15"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "16"
Cache[j].State != E & Chan2[j].Cmd = Inv -> ExGntd = false;
endruleset;




ruleset  j : NODE do
invariant "17"
Cache[j].State = E -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE do
invariant "18"
Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != ReqS;
endruleset;




ruleset  i : NODE do
invariant "19"
Chan2[i].Cmd = GntE -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE do
invariant "20"
Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntE;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "21"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> Cache[i].State = I);

endruleset;




ruleset  j : NODE do
invariant "22"
Chan3[j].Cmd = InvAck -> InvSet[j] = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "23"
i != j -> 
  (Chan2[i].Cmd = GntS -> Cache[j].State != E);

endruleset;




ruleset  j : NODE do
invariant "24"
Chan2[j].Cmd = GntE -> ExGntd = true;
endruleset;




ruleset  i : NODE do
invariant "25"
InvSet[i] = true -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE do
invariant "26"
ExGntd = false -> Cache[i].State != E;
endruleset;




ruleset  i : NODE do
invariant "27"
Chan3[i].Cmd = InvAck -> Cache[i].State != E;
endruleset;




ruleset  j : NODE do
invariant "28"
InvSet[j] = true -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "29"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> Chan3[i].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "30"
i != j -> 
  (InvSet[j] = true -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  j : NODE do
invariant "31"
CurCmd = Empty -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "32"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "33"
i != j -> 
  (Cache[i].State = S -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  j : NODE do
invariant "34"
Cache[j].State = S -> MemData = AuxData;
endruleset;




ruleset  i : NODE do
invariant "35"
Chan2[i].Cmd = GntE -> MemData = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "36"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> ShrSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "37"
Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != Inv;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "38"
i != j -> 
  (InvSet[i] = true -> Cache[j].State != E);

endruleset;




ruleset  i : NODE do
invariant "39"
Chan2[i].Cmd = GntE -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "40"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan2[i].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "41"
i != j -> 
  (Chan2[j].Cmd = GntE -> Cache[i].State != S);

endruleset;




ruleset  i : NODE do
invariant "42"
Cache[i].State = E -> Cache[i].Data = AuxData;
endruleset;




ruleset  j : NODE do
invariant "43"
Cache[j].State = S -> Cache[j].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "44"
i != j -> 
  (Cache[j].State = E -> Cache[i].State != S);

endruleset;




ruleset  i : NODE do
invariant "45"
Chan3[i].Cmd = InvAck -> Chan2[i].Cmd = Empty;
endruleset;




ruleset  i : NODE do
invariant "46"
Chan2[i].Cmd = Inv -> CurCmd != Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "47"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> InvSet[j] = false);

endruleset;




ruleset  j : NODE do
invariant "48"
Chan2[j].Cmd = GntS -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "49"
i != j -> 
  (Chan2[i].Cmd = GntE -> InvSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "50"
Chan2[i].Cmd = GntS -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  j : NODE do
invariant "51"
InvSet[j] = true -> Chan2[j].Cmd != Inv;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "52"
i != j -> 
  (Cache[j].State = S -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "53"
i != j -> 
  (InvSet[j] = true & CurCmd = ReqS -> Chan2[i].Cmd != Inv);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "54"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd != Inv);

endruleset;




ruleset  j : NODE do
invariant "55"
Chan2[j].Cmd = GntS -> MemData = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "56"
i != j -> 
  (Cache[i].State = E -> Chan2[j].Cmd != GntS);

endruleset;




ruleset  j : NODE do
invariant "57"
Cache[j].State != E & Chan2[j].Cmd = Inv -> CurCmd = ReqE;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "58"
i != j -> 
  (Chan2[i].Cmd = Inv -> Cache[j].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "59"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> InvSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "60"
Chan2[i].Cmd = Inv -> Cache[i].State != I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "61"
i != j -> 
  (Cache[j].State = E -> Chan2[i].Cmd = Empty);

endruleset;




ruleset  i : NODE do
invariant "62"
Cache[i].State = E -> ExGntd = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "63"
i != j -> 
  (Chan2[j].Cmd = GntS -> Cache[i].State != E);

endruleset;




ruleset  i : NODE do
invariant "64"
Chan3[i].Cmd = InvAck -> Cache[i].State = I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "65"
i != j -> 
  (Cache[i].State = E -> Cache[j].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "66"
i != j -> 
  (Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  j : NODE do
invariant "67"
InvSet[j] = true -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "68"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "69"
Cache[j].State = E -> Chan2[j].Cmd != GntS;
endruleset;




ruleset  i : NODE do
invariant "70"
InvSet[i] = true -> Chan2[i].Cmd != Inv;
endruleset;




ruleset  j : NODE do
invariant "71"
Chan2[j].Cmd = Inv -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "72"
ExGntd = true -> Cache[i].State != S;
endruleset;




ruleset  j : NODE do
invariant "73"
InvSet[j] = true & ExGntd = true -> CurCmd != Empty;
endruleset;




ruleset  i : NODE do
invariant "74"
Cache[i].State = S -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "75"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan2[j].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "76"
CurCmd = Empty -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE do
invariant "77"
Chan2[i].Cmd = Inv -> Cache[i].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "78"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan2[i].Cmd != GntS);

endruleset;




ruleset  j : NODE do
invariant "79"
Chan2[j].Cmd = Inv -> Cache[j].Data = AuxData;
endruleset;




ruleset  i : NODE do
invariant "80"
Cache[i].State != E & Chan2[i].Cmd = Inv -> MemData = AuxData;
endruleset;




ruleset  j : NODE do
invariant "81"
Chan2[j].Cmd = GntE -> Cache[j].State != S;
endruleset;




ruleset  i : NODE do
invariant "82"
Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntS;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "83"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> ShrSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "84"
Chan2[i].Cmd = GntS -> ShrSet[i] = true;
endruleset;




ruleset  j : NODE do
invariant "85"
Chan2[j].Cmd = Inv -> Cache[j].State != I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "86"
i != j -> 
  (Cache[j].State = E -> Chan3[i].Cmd = Empty);

endruleset;




ruleset  i : NODE do
invariant "87"
Chan2[i].Cmd = Inv -> InvSet[i] = false;
endruleset;




ruleset  j : NODE do
invariant "88"
ExGntd = false & CurCmd = ReqS -> Chan2[j].Cmd != Inv;
endruleset;




ruleset  j : NODE do
invariant "89"
Cache[j].State = E -> ExGntd = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "90"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntE);

endruleset;




ruleset do
invariant "91"
ExGntd = false -> MemData = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "92"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "93"
InvSet[j] = true & Chan2[j].Cmd = Empty -> Cache[j].State != I;
endruleset;




ruleset  j : NODE do
invariant "94"
Chan3[j].Cmd = InvAck -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE do
invariant "95"
Cache[i].State = E -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "96"
Cache[i].State = S -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "97"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntS);

endruleset;




ruleset  j : NODE do
invariant "98"
InvSet[j] = true -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  j : NODE do
invariant "99"
Cache[j].State = E -> Cache[j].Data = AuxData;
endruleset;




ruleset  j : NODE do
invariant "100"
Chan3[j].Cmd = InvAck & ExGntd = true -> Chan3[j].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "101"
i != j -> 
  (Chan2[i].Cmd = GntE -> Cache[j].State = I);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "102"
i != j -> 
  (Chan3[j].Cmd = InvAck -> Cache[i].State != E);

endruleset;




ruleset  j : NODE do
invariant "103"
Chan2[j].Cmd = GntS -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "104"
Chan3[i].Cmd = InvAck -> CurCmd != Empty;
endruleset;




ruleset  i : NODE do
invariant "105"
Chan3[i].Cmd = InvAck -> Cache[i].State != S;
endruleset;




ruleset  j : NODE do
invariant "106"
ExGntd = true -> Cache[j].State != S;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "107"
i != j -> 
  (Cache[j].State = E -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  j : NODE do
invariant "108"
Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != GntE;
endruleset;




ruleset  j : NODE do
invariant "109"
Cache[j].State = S -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "110"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "111"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd != InvAck);

endruleset;




ruleset  j : NODE do
invariant "112"
Cache[j].State != E & Chan2[j].Cmd = Inv -> MemData = AuxData;
endruleset;




ruleset  j : NODE do
invariant "113"
Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != GntS;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "114"
i != j -> 
  (Chan2[j].Cmd = GntE -> Cache[i].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "115"
i != j -> 
  (Cache[i].State = E -> InvSet[j] = false);

endruleset;




ruleset  j : NODE do
invariant "116"
Chan2[j].Cmd = Inv -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE do
invariant "117"
Cache[i].State = S -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  j : NODE do
invariant "118"
Chan2[j].Cmd = GntE -> Cache[j].State = I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "119"
i != j -> 
  (Chan2[j].Cmd = GntS -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "120"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd != InvAck);

endruleset;




ruleset  j : NODE do
invariant "121"
ExGntd = false -> Chan2[j].Cmd != GntE;
endruleset;




ruleset  j : NODE do
invariant "122"
CurCmd = Empty -> Chan2[j].Cmd != Inv;
endruleset;




ruleset  j : NODE do
invariant "123"
Chan2[j].Cmd = GntE -> MemData = AuxData;
endruleset;




ruleset  i : NODE do
invariant "124"
Cache[i].State = I -> Chan2[i].Cmd != Inv;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "125"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != Inv);

endruleset;




ruleset  j : NODE do
invariant "126"
Chan2[j].Cmd = Inv -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "127"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> Chan2[i].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "128"
Cache[j].State != E & Chan2[j].Cmd = Inv -> CurCmd != ReqS;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "129"
i != j -> 
  (Cache[j].State = E -> ShrSet[i] = false);

endruleset;




ruleset  j : NODE do
invariant "130"
Chan2[j].Cmd = Inv -> InvSet[j] = false;
endruleset;




ruleset  i : NODE do
invariant "131"
Chan2[i].Cmd = GntE -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "132"
InvSet[i] = true -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "133"
i != j -> 
  (Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  i : NODE do
invariant "134"
CurCmd = Empty -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "135"
Chan2[i].Cmd = GntE -> Cache[i].State != E;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "136"
i != j -> 
  (Cache[i].State = E -> Chan3[j].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "137"
Chan2[j].Cmd = GntS -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "138"
i != j -> 
  (Cache[j].State = E -> Chan2[i].Cmd != GntS);

endruleset;




ruleset  j : NODE do
invariant "139"
Chan2[j].Cmd = GntS -> Cache[j].State != E;
endruleset;




ruleset  i : NODE do
invariant "140"
Cache[i].State = S -> Cache[i].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "141"
i != j -> 
  (InvSet[j] = true & CurCmd = ReqS -> Chan3[i].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "142"
Cache[j].State = S -> Chan2[j].Cmd != GntE;
endruleset;




ruleset  j : NODE do
invariant "143"
Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != Inv;
endruleset;




ruleset  i : NODE do
invariant "144"
Chan2[i].Cmd = Inv -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "145"
i != j -> 
  (InvSet[i] = true & CurCmd = ReqS -> Chan2[j].Cmd != Inv);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "146"
i != j -> 
  (Chan2[j].Cmd = Inv -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "147"
i != j -> 
  (InvSet[i] = true -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  j : NODE do
invariant "148"
Cache[j].State = E -> Chan2[j].Cmd != GntE;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "149"
i != j -> 
  (Cache[j].State = E -> Chan2[i].Cmd != Inv);

endruleset;




ruleset  j : NODE do
invariant "150"
Chan2[j].Cmd = GntE -> Cache[j].State != E;
endruleset;




ruleset  i : NODE do
invariant "151"
Chan2[i].Cmd = Inv -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "152"
i != j -> 
  (Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "153"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> ShrSet[j] = false);

endruleset;




ruleset  j : NODE do
invariant "154"
Cache[j].State = I -> Chan2[j].Cmd != Inv;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "155"
i != j -> 
  (Cache[i].State = E -> Cache[j].State = I);

endruleset;




ruleset  i : NODE do
invariant "156"
Cache[i].State = S -> Chan2[i].Cmd != GntE;
endruleset;




ruleset  j : NODE do
invariant "157"
Chan2[j].Cmd = Inv -> CurCmd != Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "158"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> InvSet[j] = false);

endruleset;




ruleset  j : NODE do
invariant "159"
Cache[j].State = E -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "160"
i != j -> 
  (Chan2[i].Cmd = GntE -> ShrSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "161"
ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[i].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "162"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan3[i].Cmd != InvAck);

endruleset;




ruleset  j : NODE do
invariant "163"
Chan2[j].Cmd = GntE -> ShrSet[j] = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "164"
i != j -> 
  (Cache[j].State = E -> Cache[i].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "165"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> ShrSet[i] = false);

endruleset;




ruleset  j : NODE do
invariant "166"
Chan3[j].Cmd = InvAck -> Cache[j].State != S;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "167"
i != j -> 
  (Chan2[i].Cmd = GntE -> Cache[j].State != E);

endruleset;




ruleset  i : NODE do
invariant "168"
ExGntd = false & CurCmd = ReqS -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "169"
i != j -> 
  (Chan2[j].Cmd = GntE -> Cache[i].State = I);

endruleset;




ruleset  j : NODE do
invariant "170"
Chan2[j].Cmd = GntE -> Chan2[j].Data = AuxData;
endruleset;




ruleset  j : NODE do
invariant "171"
Chan2[j].Cmd = GntS -> ExGntd = false;
endruleset;




ruleset  i : NODE do
invariant "172"
CurCmd = Empty -> Chan3[i].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "173"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan3[i].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "174"
Chan2[j].Cmd = GntS -> Chan2[j].Data = AuxData;
endruleset;




ruleset  i : NODE do
invariant "175"
Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd = ReqE;
endruleset;




ruleset  i : NODE do
invariant "176"
Chan3[i].Cmd = InvAck -> ShrSet[i] = true;
endruleset;




ruleset  i : NODE do
invariant "177"
Chan2[i].Cmd = GntS -> ExGntd = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "178"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> InvSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "179"
Chan2[i].Cmd = GntE -> Cache[i].State = I;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "180"
i != j -> 
  (Cache[i].State = E -> Chan2[j].Cmd != Inv);

endruleset;




ruleset  j : NODE do
invariant "181"
Chan3[j].Cmd = InvAck -> Cache[j].State != E;
endruleset;




ruleset  j : NODE do
invariant "182"
ExGntd = true -> Chan2[j].Cmd != GntS;
endruleset;




ruleset  i : NODE do
invariant "183"
Cache[i].State = S -> MemData = AuxData;
endruleset;




ruleset  i : NODE do
invariant "184"
ExGntd = true & InvSet[i] = true -> CurCmd != Empty;
endruleset;




ruleset  i : NODE do
invariant "185"
Chan2[i].Cmd = GntS -> Cache[i].State != E;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "186"
i != j -> 
  (Chan3[j].Cmd = InvAck & ExGntd = true -> Cache[i].State = I);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "187"
i != j -> 
  (Chan2[j].Cmd = Inv -> Cache[i].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "188"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> Cache[j].State = I);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "189"
i != j -> 
  (Chan3[i].Cmd = InvAck -> Cache[j].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "190"
i != j -> 
  (Cache[j].State = E -> Cache[i].State = I);

endruleset;




ruleset  i : NODE do
invariant "191"
Cache[i].State = E -> Chan2[i].Cmd != GntE;
endruleset;




ruleset  i : NODE do
invariant "192"
CurCmd = Empty -> Chan2[i].Cmd != Inv;
endruleset;




ruleset  i : NODE do
invariant "193"
InvSet[i] = true -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "194"
ExGntd = true -> Chan2[i].Cmd != GntS;
endruleset;




ruleset  i : NODE do
invariant "195"
Cache[i].State != E & Chan2[i].Cmd = Inv -> ExGntd = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "196"
i != j -> 
  (Cache[j].State = S -> Cache[i].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "197"
i != j -> 
  (Cache[i].State = S -> Cache[j].State != E);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "198"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> Chan2[i].Cmd != Inv);

endruleset;




ruleset  i : NODE do
invariant "199"
Chan2[i].Cmd = GntS -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  j : NODE do
invariant "200"
ExGntd = false & CurCmd = ReqS -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "201"
i != j -> 
  (Chan2[i].Cmd = GntE -> Cache[j].State != S);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "202"
i != j -> 
  (Cache[j].State = E -> Chan3[i].Cmd != InvAck);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "203"
i != j -> 
  (InvSet[j] = true & ExGntd = true -> Chan3[i].Cmd != InvAck);

endruleset;




ruleset  i : NODE do
invariant "204"
Chan2[i].Cmd = GntE -> Cache[i].State != S;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "205"
i != j -> 
  (ExGntd = true & InvSet[i] = true -> Cache[j].State = I);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "206"
i != j -> 
  (InvSet[i] = true & CurCmd = ReqS -> Chan3[j].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "207"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan3[j].Cmd = Empty);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "208"
i != j -> 
  (Chan2[j].Cmd = GntE -> ShrSet[i] = false);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "209"
i != j -> 
  (Cache[i].State = E -> Chan2[j].Cmd = Empty);

endruleset;




ruleset  j : NODE do
invariant "210"
ExGntd = false & CurCmd = ReqS -> Chan3[j].Cmd = Empty;
endruleset;




ruleset  i : NODE do
invariant "211"
ExGntd = false & CurCmd = ReqS -> Chan2[i].Cmd != Inv;
endruleset;




ruleset  i : NODE do
invariant "212"
ExGntd = false & CurCmd = ReqS -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "213"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd != InvAck);

endruleset;




ruleset  j : NODE do
invariant "214"
Chan3[j].Cmd = InvAck -> Cache[j].State = I;
endruleset;




ruleset  i : NODE do
invariant "215"
Cache[i].State = S -> ExGntd = false;
endruleset;




ruleset  j : NODE do
invariant "216"
InvSet[j] = true & Chan2[j].Cmd = Empty -> Cache[j].Data = AuxData;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "217"
i != j -> 
  (Cache[i].State = E -> Chan2[j].Cmd != GntE);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "218"
i != j -> 
  (ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != Inv);

endruleset;




ruleset  j : NODE do
invariant "219"
Chan3[j].Cmd = InvAck -> Chan2[j].Cmd = Empty;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "220"
i != j -> 
  (Chan2[i].Cmd = GntE -> Chan2[j].Cmd != Inv);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "221"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan2[i].Cmd != GntE);

endruleset;




ruleset  i : NODE do
invariant "222"
Chan2[i].Cmd = Inv -> Chan3[i].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "223"
Chan3[i].Cmd = InvAck -> InvSet[i] = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "224"
i != j -> 
  (Cache[i].State = E -> Chan3[j].Cmd != InvAck);

endruleset;




ruleset  j : NODE do
invariant "225"
Cache[j].State = S -> ExGntd = false;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "226"
i != j -> 
  (Cache[j].State = E -> InvSet[i] = false);

endruleset;




ruleset  i : NODE ;j : NODE do
invariant "227"
i != j -> 
  (Chan2[j].Cmd = GntE -> Chan2[i].Cmd != Inv);

endruleset;




ruleset  i : NODE do
invariant "228"
Chan2[i].Cmd = Empty & InvSet[i] = true -> Cache[i].State != I;
endruleset;




ruleset  i : NODE do
invariant "229"
Chan2[i].Cmd = GntE -> Chan2[i].Data = AuxData;
endruleset;




ruleset  i : NODE do
invariant "230"
Chan2[i].Cmd = GntE -> ExGntd = true;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "231"
i != j -> 
  (Cache[i].State = E -> ShrSet[j] = false);

endruleset;




ruleset  i : NODE do
invariant "232"
ExGntd = false -> Chan2[i].Cmd != GntE;
endruleset;




ruleset  j : NODE do
invariant "233"
Chan3[j].Cmd = InvAck -> CurCmd != Empty;
endruleset;




ruleset  j : NODE do
invariant "234"
Cache[j].State = E -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  j : NODE do
invariant "235"
Chan2[j].Cmd = GntE -> Chan3[j].Cmd != InvAck;
endruleset;




ruleset  i : NODE do
invariant "236"
Cache[i].State = E -> Chan2[i].Cmd != GntS;
endruleset;




ruleset  i : NODE ;j : NODE do
invariant "237"
i != j -> 
  (Chan2[j].Cmd = GntE -> InvSet[i] = false);

endruleset;




ruleset  i : NODE do
invariant "238"
Chan2[i].Cmd = GntS -> MemData = AuxData;
endruleset;




ruleset  j : NODE do
invariant "239"
ExGntd = false -> Cache[j].State != E;
endruleset;
