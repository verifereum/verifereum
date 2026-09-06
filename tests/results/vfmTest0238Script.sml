Theory vfmTest0238[no_sig_docs]
Ancestors vfmTestDefs0238
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0238_0.nsv", "result0238_1.nsv", "result0238_2.nsv", "result0238_3.nsv", "result0238_4.nsv", "result0238_5.nsv"];
val thyn = "vfmTestDefs0238";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
