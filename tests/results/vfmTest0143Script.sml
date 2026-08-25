Theory vfmTest0143[no_sig_docs]
Ancestors vfmTestDefs0143
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0143_0.nsv", "result0143_1.nsv", "result0143_2.nsv", "result0143_3.nsv", "result0143_4.nsv", "result0143_5.nsv", "result0143_6.nsv", "result0143_7.nsv"];
val thyn = "vfmTestDefs0143";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
