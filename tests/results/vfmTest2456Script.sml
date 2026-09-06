Theory vfmTest2456[no_sig_docs]
Ancestors vfmTestDefs2456
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2456_0.nsv", "result2456_1.nsv", "result2456_2.nsv", "result2456_3.nsv", "result2456_4.nsv", "result2456_5.nsv"];
val thyn = "vfmTestDefs2456";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
