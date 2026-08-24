Theory vfmTest0574[no_sig_docs]
Ancestors vfmTestDefs0574
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0574_0.nsv", "result0574_1.nsv", "result0574_2.nsv", "result0574_3.nsv"];
val thyn = "vfmTestDefs0574";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
