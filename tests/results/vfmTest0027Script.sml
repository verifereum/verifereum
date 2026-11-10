Theory vfmTest0027[no_sig_docs]
Ancestors vfmTestDefs0027
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0027_0.nsv", "result0027_1.nsv", "result0027_2.nsv", "result0027_3.nsv", "result0027_4.nsv", "result0027_5.nsv", "result0027_6.nsv", "result0027_7.nsv", "result0027_8.nsv", "result0027_9.nsv"];
val thyn = "vfmTestDefs0027";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
