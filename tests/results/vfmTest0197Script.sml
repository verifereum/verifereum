Theory vfmTest0197[no_sig_docs]
Ancestors vfmTestDefs0197
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0197_0.nsv", "result0197_1.nsv", "result0197_2.nsv", "result0197_3.nsv", "result0197_4.nsv", "result0197_5.nsv", "result0197_6.nsv", "result0197_7.nsv"];
val thyn = "vfmTestDefs0197";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
