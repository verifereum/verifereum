Theory vfmTest0017[no_sig_docs]
Ancestors vfmTestDefs0017
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0017_0.nsv", "result0017_1.nsv", "result0017_2.nsv", "result0017_3.nsv", "result0017_4.nsv", "result0017_5.nsv", "result0017_6.nsv", "result0017_7.nsv", "result0017_8.nsv", "result0017_9.nsv"];
val thyn = "vfmTestDefs0017";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
