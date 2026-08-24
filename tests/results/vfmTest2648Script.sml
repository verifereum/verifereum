Theory vfmTest2648[no_sig_docs]
Ancestors vfmTestDefs2648
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2648_0.nsv", "result2648_1.nsv", "result2648_2.nsv", "result2648_3.nsv"];
val thyn = "vfmTestDefs2648";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
