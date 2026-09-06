Theory vfmTest0164[no_sig_docs]
Ancestors vfmTestDefs0164
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0164_0.nsv", "result0164_1.nsv", "result0164_2.nsv", "result0164_3.nsv", "result0164_4.nsv", "result0164_5.nsv"];
val thyn = "vfmTestDefs0164";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
