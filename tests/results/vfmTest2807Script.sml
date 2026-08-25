Theory vfmTest2807[no_sig_docs]
Ancestors vfmTestDefs2807
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2807_0.nsv", "result2807_1.nsv", "result2807_2.nsv", "result2807_3.nsv"];
val thyn = "vfmTestDefs2807";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
