Theory vfmTest2282[no_sig_docs]
Ancestors vfmTestDefs2282
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2282_0.nsv", "result2282_1.nsv"];
val thyn = "vfmTestDefs2282";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
