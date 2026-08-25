Theory vfmTest0953[no_sig_docs]
Ancestors vfmTestDefs0953
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0953_0.nsv", "result0953_1.nsv", "result0953_2.nsv", "result0953_3.nsv", "result0953_4.nsv", "result0953_5.nsv", "result0953_6.nsv", "result0953_7.nsv", "result0953_8.nsv"];
val thyn = "vfmTestDefs0953";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
