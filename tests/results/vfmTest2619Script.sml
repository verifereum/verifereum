Theory vfmTest2619[no_sig_docs]
Ancestors vfmTestDefs2619
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2619_0.nsv", "result2619_1.nsv", "result2619_2.nsv", "result2619_3.nsv"];
val thyn = "vfmTestDefs2619";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
