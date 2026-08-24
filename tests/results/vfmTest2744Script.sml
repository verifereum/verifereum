Theory vfmTest2744[no_sig_docs]
Ancestors vfmTestDefs2744
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2744_0.nsv", "result2744_1.nsv", "result2744_2.nsv", "result2744_3.nsv"];
val thyn = "vfmTestDefs2744";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
