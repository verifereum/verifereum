Theory vfmTest0365[no_sig_docs]
Ancestors vfmTestDefs0365
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0365_0.nsv", "result0365_1.nsv", "result0365_2.nsv", "result0365_3.nsv"];
val thyn = "vfmTestDefs0365";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
