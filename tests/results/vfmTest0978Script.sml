Theory vfmTest0978[no_sig_docs]
Ancestors vfmTestDefs0978
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0978_0.nsv", "result0978_1.nsv", "result0978_2.nsv"];
val thyn = "vfmTestDefs0978";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
