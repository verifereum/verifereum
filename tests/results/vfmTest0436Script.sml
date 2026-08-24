Theory vfmTest0436[no_sig_docs]
Ancestors vfmTestDefs0436
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0436_0.nsv", "result0436_1.nsv", "result0436_2.nsv", "result0436_3.nsv", "result0436_4.nsv", "result0436_5.nsv", "result0436_6.nsv", "result0436_7.nsv", "result0436_8.nsv"];
val thyn = "vfmTestDefs0436";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
