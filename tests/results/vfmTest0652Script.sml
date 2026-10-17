Theory vfmTest0652[no_sig_docs]
Ancestors vfmTestDefs0652
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0652_0.nsv", "result0652_1.nsv", "result0652_2.nsv", "result0652_3.nsv", "result0652_4.nsv", "result0652_5.nsv", "result0652_6.nsv", "result0652_7.nsv", "result0652_8.nsv", "result0652_9.nsv", "result0652_10.nsv", "result0652_11.nsv"];
val thyn = "vfmTestDefs0652";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
