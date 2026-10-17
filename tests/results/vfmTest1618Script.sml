Theory vfmTest1618[no_sig_docs]
Ancestors vfmTestDefs1618
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1618_0.nsv", "result1618_1.nsv", "result1618_2.nsv", "result1618_3.nsv", "result1618_4.nsv", "result1618_5.nsv", "result1618_6.nsv", "result1618_7.nsv"];
val thyn = "vfmTestDefs1618";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
