Theory vfmTest1792[no_sig_docs]
Ancestors vfmTestDefs1792
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1792_0.nsv", "result1792_1.nsv", "result1792_2.nsv", "result1792_3.nsv", "result1792_4.nsv", "result1792_5.nsv", "result1792_6.nsv", "result1792_7.nsv", "result1792_8.nsv"];
val thyn = "vfmTestDefs1792";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
