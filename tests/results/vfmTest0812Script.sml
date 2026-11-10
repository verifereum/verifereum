Theory vfmTest0812[no_sig_docs]
Ancestors vfmTestDefs0812
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0812_0.nsv", "result0812_1.nsv", "result0812_2.nsv", "result0812_3.nsv"];
val thyn = "vfmTestDefs0812";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
