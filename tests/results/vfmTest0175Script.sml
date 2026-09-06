Theory vfmTest0175[no_sig_docs]
Ancestors vfmTestDefs0175
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0175_0.nsv", "result0175_1.nsv", "result0175_2.nsv", "result0175_3.nsv", "result0175_4.nsv", "result0175_5.nsv", "result0175_6.nsv", "result0175_7.nsv", "result0175_8.nsv"];
val thyn = "vfmTestDefs0175";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
