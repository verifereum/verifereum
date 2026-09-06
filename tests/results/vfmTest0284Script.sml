Theory vfmTest0284[no_sig_docs]
Ancestors vfmTestDefs0284
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0284_0.nsv", "result0284_1.nsv", "result0284_2.nsv", "result0284_3.nsv", "result0284_4.nsv", "result0284_5.nsv"];
val thyn = "vfmTestDefs0284";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
