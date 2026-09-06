Theory vfmTest0725[no_sig_docs]
Ancestors vfmTestDefs0725
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0725_0.nsv", "result0725_1.nsv", "result0725_2.nsv", "result0725_3.nsv", "result0725_4.nsv", "result0725_5.nsv"];
val thyn = "vfmTestDefs0725";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
