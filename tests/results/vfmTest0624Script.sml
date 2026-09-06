Theory vfmTest0624[no_sig_docs]
Ancestors vfmTestDefs0624
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0624_0.nsv", "result0624_1.nsv", "result0624_2.nsv"];
val thyn = "vfmTestDefs0624";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
