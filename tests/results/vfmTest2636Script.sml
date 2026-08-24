Theory vfmTest2636[no_sig_docs]
Ancestors vfmTestDefs2636
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2636_0.nsv", "result2636_1.nsv", "result2636_2.nsv", "result2636_3.nsv"];
val thyn = "vfmTestDefs2636";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
