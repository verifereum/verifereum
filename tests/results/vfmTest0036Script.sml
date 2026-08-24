Theory vfmTest0036[no_sig_docs]
Ancestors vfmTestDefs0036
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0036_0.nsv", "result0036_1.nsv", "result0036_2.nsv", "result0036_3.nsv", "result0036_4.nsv"];
val thyn = "vfmTestDefs0036";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
