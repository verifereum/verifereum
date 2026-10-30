Theory vfmTest0978[no_sig_docs]
Ancestors vfmTestDefs0978
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0978_0.nsv", "result0978_1.nsv", "result0978_2.nsv", "result0978_3.nsv", "result0978_4.nsv", "result0978_5.nsv", "result0978_6.nsv", "result0978_7.nsv"];
val thyn = "vfmTestDefs0978";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
