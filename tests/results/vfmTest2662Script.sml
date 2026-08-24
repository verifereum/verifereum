Theory vfmTest2662[no_sig_docs]
Ancestors vfmTestDefs2662
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2662_0.nsv", "result2662_1.nsv", "result2662_2.nsv", "result2662_3.nsv"];
val thyn = "vfmTestDefs2662";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
