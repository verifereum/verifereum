Theory vfmTest0302[no_sig_docs]
Ancestors vfmTestDefs0302
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0302_0.nsv", "result0302_1.nsv", "result0302_2.nsv", "result0302_3.nsv"];
val thyn = "vfmTestDefs0302";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
