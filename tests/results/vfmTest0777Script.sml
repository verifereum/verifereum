Theory vfmTest0777[no_sig_docs]
Ancestors vfmTestDefs0777
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0777_0.nsv", "result0777_1.nsv", "result0777_2.nsv", "result0777_3.nsv", "result0777_4.nsv", "result0777_5.nsv", "result0777_6.nsv", "result0777_7.nsv"];
val thyn = "vfmTestDefs0777";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
