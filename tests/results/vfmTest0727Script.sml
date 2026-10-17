Theory vfmTest0727[no_sig_docs]
Ancestors vfmTestDefs0727
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0727_0.nsv", "result0727_1.nsv", "result0727_2.nsv", "result0727_3.nsv", "result0727_4.nsv", "result0727_5.nsv", "result0727_6.nsv", "result0727_7.nsv", "result0727_8.nsv", "result0727_9.nsv"];
val thyn = "vfmTestDefs0727";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
