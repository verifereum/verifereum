Theory vfmTest1522[no_sig_docs]
Ancestors vfmTestDefs1522
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1522_0.nsv", "result1522_1.nsv", "result1522_2.nsv", "result1522_3.nsv", "result1522_4.nsv", "result1522_5.nsv", "result1522_6.nsv", "result1522_7.nsv"];
val thyn = "vfmTestDefs1522";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
