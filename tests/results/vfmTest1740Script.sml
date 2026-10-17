Theory vfmTest1740[no_sig_docs]
Ancestors vfmTestDefs1740
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1740_0.nsv", "result1740_1.nsv", "result1740_2.nsv", "result1740_3.nsv", "result1740_4.nsv", "result1740_5.nsv", "result1740_6.nsv", "result1740_7.nsv"];
val thyn = "vfmTestDefs1740";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
