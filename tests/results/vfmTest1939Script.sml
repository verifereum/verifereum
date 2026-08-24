Theory vfmTest1939[no_sig_docs]
Ancestors vfmTestDefs1939
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1939_0.nsv", "result1939_1.nsv", "result1939_2.nsv", "result1939_3.nsv"];
val thyn = "vfmTestDefs1939";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
